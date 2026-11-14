/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
import CslibFrontier.MachineLearning.PACLearning.DoubleSample
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Product.MapMeasure
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # The ε-net theorem on countable domains

Let `G` be a class of Boolean functions on a domain `Z` and `μ` a probability measure on `Z`. A
sample `S : Fin m → Z` is an *ε-net* for `G` under `μ` if every `g ∈ G` with
`μ {g = true} ≥ ε` takes the value `true` at some sample point
[HausslerWelzl1987; ShalevShwartzBenDavid2014, Section 28.3]. The ε-net theorem says that `m`
i.i.d. samples fail to be an ε-net with probability at most `2 Π_G(2m) 2^(-εm/2)` once
`εm ≥ 8`, where `Π_G` is the growth function [ShalevShwartzBenDavid2014, Section 28.3; see also
BlumerEhrenfeuchtHausslerWarmuth1989]. With Sauer's lemma this gives the sample size

`m ≥ (8 / ε) (d log (48 / ε) + log (4 / δ))`

for failure probability at most `δ` when every set shattered by `G` has at most `d` points. The
constants differ from those of the cited sources but have the same form.

The proof is the double-sample symmetrization argument. If some `g` with `μ {g = true} ≥ ε` misses
the first sample, then by the Chernoff lower tail a second independent sample has at least
`εm / 2` points with `g = true` with probability at least `1 / 2`. So the bad event has probability
at most twice that of the *double-sample event*: some `g ∈ G` is `false` on the first sample and
`true` on at least `k = ⌈εm / 2⌉` points of the second. Swapping any set of coordinates between
the two samples preserves the product measure. For a fixed double sample, at most
`Π_G(2m) 2^(m - k)` of the `2^m` swaps land in the double-sample event, because each realized
labeling of the `2m` points is compatible with at most `2^(m - k)` swaps. The measure-theoretic
steps of this argument (the ghost sample and swap averaging) are in `DoubleSample.lean`.

The domain is assumed countable with measurable singletons, so every set of samples is measurable.
Over general domains the theorem needs a measurability hypothesis on the class (the
"well-behaved" classes of [BlumerEhrenfeuchtHausslerWarmuth1989]); that case is not formalized
here.

## Main definitions

- `IsEpsNet μ G ε S`: the sample `S` is an ε-net for `G` under `μ`.
- `vcSampleSize d ε δ`: the sample size `(8 / ε) (d log (48 / ε) + log (4 / δ))`.

## Main results

- `measure_pi_not_isEpsNet_mul_two_pow_le`: **the ε-net theorem**, in growth-function form:
  `μ^m {S not an ε-net} * 2 ^ ⌈εm/2⌉ ≤ 2 Π_G(2m)` when `8 ≤ εm`.
- `measure_pi_not_isEpsNet_le_of_growthFunction_le`: the failure probability is at most `δ`
  when `2 Π_G(2m) ≤ δ 2 ^ ⌈εm/2⌉`.
- `growthFunction_le_of_vcSampleSize_le`: the explicit sample size achieves this when every set
  shattered by `G` has at most `d` points.
- `measure_pi_not_isEpsNet_le_of_vcSampleSize_le`: the ε-net theorem with the explicit sample
  size.

## References

* [D. Haussler, E. Welzl, *ε-nets and simplex range queries*][HausslerWelzl1987]
* [A. Blumer, A. Ehrenfeucht, D. Haussler, M. K. Warmuth, *Learnability and the
  Vapnik–Chervonenkis dimension*][BlumerEhrenfeuchtHausslerWarmuth1989]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Finset

namespace Cslib.MachineLearning.PACLearning

/-! ### Counting swaps -/

/-- For fixed label patterns `a` and `b` of two samples, the swaps `σ` after which the first
sample is labeled `false` everywhere and the second is labeled `true` at `k` or more points number
at most `2 ^ (m - k)`. -/
private theorem card_filter_swap_mul_two_pow_le {m k : ℕ} (a b : Fin m → Bool) :
    (Finset.univ.filter fun σ : Fin m → Bool =>
        (∀ i, (if σ i then b i else a i) = false) ∧
          k ≤ (Finset.univ.filter fun i => (if σ i then a i else b i) = true).card).card *
      2 ^ k ≤ 2 ^ m := by
  classical
  set Good := Finset.univ.filter fun σ : Fin m → Bool =>
    (∀ i, (if σ i then b i else a i) = false) ∧
      k ≤ (Finset.univ.filter fun i => (if σ i then a i else b i) = true).card
  rcases Good.eq_empty_or_nonempty with h | ⟨σ₀, hσ₀⟩
  · rw [h, Finset.card_empty, zero_mul]
    exact Nat.zero_le _
  obtain ⟨h0, hk⟩ := (Finset.mem_filter.1 hσ₀).2
  have hfilt : (Finset.univ.filter fun i => (if σ₀ i then a i else b i) = true) =
      Finset.univ.filter fun i => (a i || b i) = true := by
    refine Finset.filter_congr fun i _ => ?_
    have := h0 i
    cases hs : σ₀ i <;> cases ha : a i <;> cases hb : b i <;> simp_all
  rw [hfilt] at hk
  have hab : ∀ i, ¬ (a i = true ∧ b i = true) := by
    intro i ⟨ha, hb⟩
    have := h0 i
    cases hs : σ₀ i <;> simp_all
  -- A compatible swap is forced at every coordinate where `a` or `b` is `true`.
  set A : Fin m → Finset Bool := fun i =>
    if a i = true then {true} else if b i = true then {false} else Finset.univ
  have hsub : Good ⊆ Fintype.piFinset A := by
    intro σ hσ
    rw [Fintype.mem_piFinset]
    intro i
    have := (Finset.mem_filter.1 hσ).2.1 i
    simp only [A]
    cases hs : σ i <;> cases ha : a i <;> cases hb : b i <;> simp_all
  have hA : ∀ i, (A i).card * 2 ^ (if (a i || b i) = true then 1 else 0) ≤ 2 := by
    intro i
    have := hab i
    simp only [A]
    cases ha : a i <;> cases hb : b i <;> simp_all
  calc Good.card * 2 ^ k
      ≤ (Fintype.piFinset A).card *
          2 ^ (Finset.univ.filter fun i => (a i || b i) = true).card := by
        gcongr
    _ = ∏ i, ((A i).card * 2 ^ (if (a i || b i) = true then 1 else 0)) := by
        rw [Fintype.card_piFinset, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
          Finset.sum_boole, Nat.cast_id]
    _ ≤ ∏ _i : Fin m, 2 := Finset.prod_le_prod fun i _ => hA i
    _ = 2 ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable {Z : Type*}

/-- The double-sample event: some `g ∈ G` is `false` on the first sample and `true` on at least
`k` points of the second. -/
private def doubleSampleEvent (G : ConceptClass Z Bool) (m k : ℕ) :
    Set ((Fin m → Z) × (Fin m → Z)) :=
  {z | ∃ g ∈ G, (∀ i, g (z.1 i) = false) ∧
    k ≤ (Finset.univ.filter fun i => g (z.2 i) = true).card}

open Classical in
/-- For a fixed double sample, at most `Π_G(2m) 2 ^ (m - k)` swaps land in the double-sample
event. -/
private theorem card_filter_swapSamples_mem_mul_two_pow_le (G : ConceptClass Z Bool) {m : ℕ}
    (k : ℕ) (z : (Fin m → Z) × (Fin m → Z)) :
    (Finset.univ.filter fun σ : Fin m → Bool =>
        swapSamples σ z ∈ doubleSampleEvent G m k).card * 2 ^ k ≤
      growthFunction G (m + m) * 2 ^ m := by
  classical
  set Good := Finset.univ.filter fun σ : Fin m → Bool =>
    swapSamples σ z ∈ doubleSampleEvent G m k
  set x : Fin (m + m) → Z := Fin.append z.1 z.2
  have hw : ∀ σ ∈ Good, ∃ g ∈ G, (∀ i, g ((swapSamples σ z).1 i) = false) ∧
      k ≤ (Finset.univ.filter fun i => g ((swapSamples σ z).2 i) = true).card :=
    fun σ hσ => (Finset.mem_filter.1 hσ).2
  -- Each good swap determines a labeling of the `2m` points realized by `G`.
  let v : (Fin m → Bool) → (Fin (m + m) → Bool) := fun σ =>
    if hσ : σ ∈ Good then fun j => (hw σ hσ).choose (x j) else fun _ => false
  have hvR : ∀ σ ∈ Good, v σ ∈ restriction G x := by
    intro σ hσ
    rw [mem_restriction]
    exact ⟨(hw σ hσ).choose, (hw σ hσ).choose_spec.1,
      fun j => by simp only [v, hσ, ↓reduceDIte]⟩
  -- Each labeling is compatible with at most `2 ^ (m - k)` swaps.
  have hfib : ∀ w ∈ Good.image v, (Good.filter fun σ => v σ = w).card * 2 ^ k ≤ 2 ^ m := by
    intro w _
    refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card ?_))
      (card_filter_swap_mul_two_pow_le (k := k) (fun i => w (Fin.castAdd m i))
        (fun i => w (Fin.natAdd m i)))
    intro σ hσ
    obtain ⟨hσG, rfl⟩ := Finset.mem_filter.1 hσ
    obtain ⟨-, h1, h2⟩ := (hw σ hσG).choose_spec
    have hva : ∀ i, v σ (Fin.castAdd m i) = (hw σ hσG).choose (z.1 i) := fun i => by
      simp only [v, hσG, ↓reduceDIte, x, Fin.append_left]
    have hvb : ∀ i, v σ (Fin.natAdd m i) = (hw σ hσG).choose (z.2 i) := fun i => by
      simp only [v, hσG, ↓reduceDIte, x, Fin.append_right]
    generalize (hw σ hσG).choose = g at h1 h2 hva hvb
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => ?_, ?_⟩
    · rw [hva, hvb]
      have := h1 i
      simp only [fst_swapSamples_apply] at this
      cases hσi : σ i
      · simpa [hσi] using this
      · simpa [hσi] using this
    · refine h2.trans_eq (congrArg Finset.card (Finset.filter_congr fun i _ => ?_))
      rw [hva, hvb, snd_swapSamples_apply]
      cases σ i <;> rfl
  have himg : (Good.image v).card ≤ growthFunction G (m + m) := by
    calc (Good.image v).card = ((Good.image v : Finset _) : Set (Fin (m + m) → Bool)).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (restriction G x).ncard := Set.ncard_le_ncard (fun w hw' => by
            obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw')
            exact hvR σ hσ) (Set.toFinite _)
      _ ≤ growthFunction G (m + m) := ncard_restriction_le_growthFunction G x
  calc Good.card * 2 ^ k
      = ∑ w ∈ Good.image v, (Good.filter fun σ => v σ = w).card * 2 ^ k := by
        rw [Finset.card_eq_sum_card_image v Good, Finset.sum_mul]
    _ ≤ ∑ _w ∈ Good.image v, 2 ^ m := Finset.sum_le_sum hfib
    _ = (Good.image v).card * 2 ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ growthFunction G (m + m) * 2 ^ m := Nat.mul_le_mul_right _ himg

/-! ### The explicit sample size -/

/-- The VC sample size `(8 / ε) (d log (48 / ε) + log (4 / δ))`. -/
@[expose] noncomputable def vcSampleSize (d : ℕ) (ε δ : ℝ) : ℝ :=
  8 / ε * (d * Real.log (48 / ε) + Real.log (4 / δ))

/-- The explicit sample size makes `2 Π_G(2m) ≤ δ 2 ^ ⌈εm/2⌉` (and `8 ≤ εm`) whenever every
finite set shattered by `G` has at most `d` points. The proof applies Sauer's lemma in the form
`Π_G(2m) ≤ exp (2m / T) T ^ d` (`growthFunction_le_exp_mul_pow`) at `T = 48 / ε`. -/
theorem growthFunction_le_of_vcSampleSize_le {G : ConceptClass Z Bool} {d : ℕ}
    (hG : ∀ W : Finset Z, SetShatters G ↑W → W.card ≤ d) {m : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : vcSampleSize d ε δ ≤ m) :
    8 ≤ ε * m ∧ 2 * (growthFunction G (m + m) : ℝ) ≤ δ * 2 ^ ⌈ε * m / 2⌉₊ := by
  have hT : 1 ≤ 48 / ε := by rw [le_div_iff₀ hε]; linarith
  have hlogT : 0 ≤ Real.log (48 / ε) := Real.log_nonneg hT
  have hlog4 : 1 ≤ Real.log (4 / δ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    calc Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
      _ ≤ 4 / δ := by rw [le_div_iff₀ hδ]; nlinarith
  rw [vcSampleSize, div_mul_eq_mul_div, div_le_iff₀ hε] at hm
  have hdlog : 0 ≤ (d : ℝ) * Real.log (48 / ε) := mul_nonneg (Nat.cast_nonneg d) hlogT
  have h8 : 8 ≤ ε * m := by linarith
  refine ⟨h8, ?_⟩
  have hexp : ((m + m : ℕ) : ℝ) / (48 / ε) = ε * m / 24 := by
    push_cast
    field_simp
    ring
  have hlog2 : ε * m / 3 ≤ ε * m / 2 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  rw [Real.log_div (by norm_num) hδ.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hm
  calc 2 * (growthFunction G (m + m) : ℝ)
      ≤ 2 * (Real.exp (((m + m : ℕ) : ℝ) / (48 / ε)) * (48 / ε) ^ d) := by
        gcongr
        exact growthFunction_le_exp_mul_pow hG _ hT
    _ ≤ δ * (2 : ℝ) ^ (ε * m / 2) := by
        rw [hexp, ← Real.log_le_log_iff (by positivity) (by positivity),
          Real.log_mul two_ne_zero (by positivity),
          Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow,
          Real.log_mul hδ.ne' (by positivity), Real.log_rpow two_pos]
        push_cast at hm ⊢
        linarith [Real.log_two_gt_d9]
    _ ≤ δ * 2 ^ ⌈ε * m / 2⌉₊ := by
        gcongr
        calc (2 : ℝ) ^ (ε * m / 2) ≤ (2 : ℝ) ^ (⌈ε * m / 2⌉₊ : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
          _ = 2 ^ ⌈ε * m / 2⌉₊ := Real.rpow_natCast _ _

/-! ### ε-nets -/

section EpsNet

variable [MeasurableSpace Z]

/-- The sample `S` is an *ε-net* for the class `G` under the measure `μ`: every `g ∈ G` with
`μ {g = true} ≥ ε` takes the value `true` at some sample point [HausslerWelzl1987]. -/
@[expose] def IsEpsNet (μ : Measure Z) (G : ConceptClass Z Bool) (ε : ℝ) {m : ℕ}
    (S : Fin m → Z) : Prop :=
  ∀ g ∈ G, ENNReal.ofReal ε ≤ μ {z | g z = true} → ∃ i, g (S i) = true

theorem not_isEpsNet_iff {μ : Measure Z} {G : ConceptClass Z Bool} {ε : ℝ} {m : ℕ}
    {S : Fin m → Z} :
    ¬ IsEpsNet μ G ε S ↔
      ∃ g ∈ G, ENNReal.ofReal ε ≤ μ {z | g z = true} ∧ ∀ i, g (S i) = false := by
  simp only [IsEpsNet, not_forall, not_exists, Bool.not_eq_true, exists_prop]

end EpsNet

/-! ### The ε-net theorem -/

variable [MeasurableSpace Z] [MeasurableSingletonClass Z] [Countable Z]

/-- Lower tail for the number of points of `m` i.i.d. samples in an event of probability at
least `ε`: if `8 ≤ ε m`, fewer than `ε m / 2` of them fall in the event with probability at most
`1 / 2`. -/
private theorem measure_pi_card_lt_le_half (μ : Measure Z) [IsProbabilityMeasure μ]
    (g : Z → Bool) {ε : ℝ} (hε : ENNReal.ofReal ε ≤ μ {z | g z = true}) {m : ℕ}
    (hm : 8 ≤ ε * m) :
    Measure.pi (fun _ : Fin m => μ)
        {T | ((Finset.univ.filter fun i => g (T i) = true).card : ℝ) < ε * m / 2} ≤ 1 / 2 := by
  classical
  -- Push the samples forward to their labels, an i.i.d. sample of a Bernoulli distribution.
  set q : PMF Bool := (μ.map g).toPMF
  have hmap : (Measure.pi fun _ : Fin m => μ).map (fun T i => g (T i)) =
      (Cslib.Probability.PMF.pi fun _ : Fin m => q).toMeasure :=
    Cslib.Probability.PMF.map_measurePi_eq_toMeasure_pi _ fun _ =>
      (measurable_of_countable g).aemeasurable
  have hgm : Measurable fun (T : Fin m → Z) i => g (T i) := measurable_of_countable _
  have hpre : {T : Fin m → Z | ((Finset.univ.filter fun i => g (T i) = true).card : ℝ) <
      ε * m / 2} = (fun T i => g (T i)) ⁻¹'
        {b : Fin m → Bool | ((Finset.univ.filter fun i => b i = true).card : ℝ) < ε * m / 2} :=
    rfl
  rw [hpre, ← Measure.map_apply hgm (Set.toFinite _).measurableSet, hmap,
    PMF.toMeasure_apply_eq_toOuterMeasure]
  set score : Fin m → Bool → ℝ := fun _ b => if b = true then 1 else 0
  have hscore : ∀ i b, b ∈ q.support → score i b ∈ Set.Icc (0 : ℝ) 1 := by
    intro i b _
    cases b <;> simp [score]
  have hqt : q true = μ {z | g z = true} := by
    rw [Measure.toPMF_apply, Measure.map_apply (measurable_of_countable g)
      (measurableSet_singleton _)]
    rfl
  have hεq : ε ≤ (q true).toReal := by
    rw [hqt]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hε
  have hmean : ε * m ≤ ∑ i : Fin m, ∑ a, (q a).toReal * score i a := by
    simp only [score, Fintype.sum_bool, ite_true, mul_one, Bool.false_eq_true, ite_false,
      mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hεq (Nat.cast_nonneg _)
  -- The Chernoff lower tail at relative deviation `1 / 2`.
  have hch := Cslib.Probability.PMF.pi_sum_le_one_sub_mul (fun _ : Fin m => q) score hscore
    hmean (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsub : {b : Fin m → Bool | ((Finset.univ.filter fun i => b i = true).card : ℝ) <
      ε * m / 2} ⊆ {b | ∑ i, score i (b i) ≤ (1 - 1 / 2) * (ε * m)} := by
    intro b hb
    simp only [Set.mem_ofPred_eq] at hb ⊢
    have hcount : ((Finset.univ.filter fun i => b i = true).card : ℝ) =
        ∑ i, score i (b i) := by
      simp only [score, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
    linarith
  have hexp : Real.exp (-((1 / 2) ^ 2 * (ε * m) / 2)) < 1 / 2 := by
    calc Real.exp (-((1 / 2) ^ 2 * (ε * m) / 2)) ≤ Real.exp (-1) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ < 1 / 2 := by
          rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
          norm_num
          linarith [Real.exp_one_gt_d9]
  have hle := measure_mono (μ := (Cslib.Probability.PMF.pi fun _ : Fin m => q).toOuterMeasure)
    hsub
  have hne : (Cslib.Probability.PMF.pi fun _ : Fin m => q).toOuterMeasure
      {b | ∑ i, score i (b i) ≤ (1 - 1 / 2) * (ε * m)} ≠ ⊤ :=
    Cslib.Probability.PMF.toOuterMeasure_ne_top _ _
  refine hle.trans ?_
  rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat],
    ENNReal.le_ofReal_iff_toReal_le hne (by norm_num)]
  exact hch.trans hexp.le

/-- Symmetrization: the double-sample event has probability at most `Π_G(2m) / 2 ^ k`. -/
private theorem measure_doubleSampleEvent_mul_two_pow_le (μ : Measure Z)
    [IsProbabilityMeasure μ] (G : ConceptClass Z Bool) (m k : ℕ) :
    (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ)
        (doubleSampleEvent G m k) * 2 ^ k ≤ growthFunction G (m + m) := by
  classical
  set ρ := (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) with hρ
  set J := doubleSampleEvent G m k
  -- Average the indicator of `J` over all `2 ^ m` swaps.
  have hsum : (2 : ℝ≥0∞) ^ m * ρ J =
      ∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card : ℝ≥0∞)
        ∂ρ :=
    (lintegral_card_filter_swapSamples_mem μ .of_discrete).symm
  have hpt : ∀ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card :
      ℝ≥0∞) * 2 ^ k ≤ growthFunction G (m + m) * 2 ^ m := fun z => by
    exact_mod_cast card_filter_swapSamples_mem_mul_two_pow_le G k z
  have key : (2 : ℝ≥0∞) ^ m * (ρ J * 2 ^ k) ≤ 2 ^ m * growthFunction G (m + m) := by
    calc (2 : ℝ≥0∞) ^ m * (ρ J * 2 ^ k)
        = (∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card :
            ℝ≥0∞) ∂ρ) * 2 ^ k := by rw [← hsum, mul_assoc]
      _ = ∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card :
            ℝ≥0∞) * 2 ^ k ∂ρ := (lintegral_mul_const _ (measurable_of_countable _)).symm
      _ ≤ ∫⁻ _z, (growthFunction G (m + m) * 2 ^ m : ℝ≥0∞) ∂ρ := lintegral_mono hpt
      _ = growthFunction G (m + m) * 2 ^ m := by rw [lintegral_const, measure_univ, mul_one]
      _ = 2 ^ m * growthFunction G (m + m) := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).1 key

/-- **The ε-net theorem** on a countable domain [ShalevShwartzBenDavid2014, Section 28.3; see
also BlumerEhrenfeuchtHausslerWarmuth1989]: if `8 ≤ εm`, then `m` i.i.d. samples from `μ` fail to
be an ε-net for `G` with probability at most `2 Π_G(2m) / 2 ^ ⌈εm/2⌉`. -/
theorem measure_pi_not_isEpsNet_mul_two_pow_le (μ : Measure Z) [IsProbabilityMeasure μ]
    (G : ConceptClass Z Bool) {ε : ℝ} {m : ℕ} (hm : 8 ≤ ε * m) :
    Measure.pi (fun _ : Fin m => μ) {S | ¬ IsEpsNet μ G ε S} * 2 ^ ⌈ε * m / 2⌉₊ ≤
      2 * growthFunction G (m + m) := by
  classical
  set ν := Measure.pi (fun _ : Fin m => μ) with hν
  set k := ⌈ε * m / 2⌉₊ with hk
  set B := {S : Fin m → Z | ¬ IsEpsNet μ G ε S}
  set J := doubleSampleEvent G m k
  -- A sample missing a heavy `g` extends to the double-sample event with probability `≥ 1 / 2`.
  have hfib : ∀ S ∈ B, 1 / 2 ≤ ν (Prod.mk S ⁻¹' J) := by
    intro S hS
    obtain ⟨g, hg, hgε, hgS⟩ := not_isEpsNet_iff.1 hS
    have hsub : {T : Fin m → Z | k ≤ (Finset.univ.filter fun i => g (T i) = true).card} ⊆
        Prod.mk S ⁻¹' J := fun T hT => ⟨g, hg, hgS, hT⟩
    have hcompl : {T : Fin m → Z | k ≤ (Finset.univ.filter fun i => g (T i) = true).card}ᶜ =
        {T | ((Finset.univ.filter fun i => g (T i) = true).card : ℝ) < ε * m / 2} := by
      ext T
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, hk, Nat.lt_ceil]
    have hlow := measure_pi_card_lt_le_half μ g hgε hm
    rw [← hcompl, prob_compl_eq_one_sub .of_discrete] at hlow
    refine le_trans ?_ (measure_mono hsub)
    have h1 := tsub_le_iff_right.1 hlow
    refine ENNReal.le_of_add_le_add_left (a := 1 / 2) (by simp) ?_
    rw [ENNReal.add_halves]
    exact h1
  have hJB : ν B ≤
      2 * ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ) J) :=
    measure_le_two_mul_measure_prod ν ν B .of_discrete hfib
  have hρJ := measure_doubleSampleEvent_mul_two_pow_le μ G m k
  calc ν B * 2 ^ k
      ≤ 2 * ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ) J) *
          2 ^ k := by
        gcongr
    _ = 2 * ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ) J *
          2 ^ k) :=
        mul_assoc _ _ _
    _ ≤ 2 * growthFunction G (m + m) := by gcongr

/-- The ε-net theorem in `δ` form: if `8 ≤ εm` and `2 Π_G(2m) ≤ δ 2 ^ ⌈εm/2⌉`, then `m` i.i.d.
samples fail to be an ε-net with probability at most `δ`. -/
theorem measure_pi_not_isEpsNet_le_of_growthFunction_le (μ : Measure Z) [IsProbabilityMeasure μ]
    (G : ConceptClass Z Bool) {ε δ : ℝ} {m : ℕ} (hm : 8 ≤ ε * m)
    (hG : 2 * (growthFunction G (m + m) : ℝ) ≤ δ * 2 ^ ⌈ε * m / 2⌉₊) :
    Measure.pi (fun _ : Fin m => μ) {S | ¬ IsEpsNet μ G ε S} ≤ ENNReal.ofReal δ := by
  have h2 : (2 : ℝ≥0∞) * growthFunction G (m + m) ≤ ENNReal.ofReal δ * 2 ^ ⌈ε * m / 2⌉₊ := by
    have := ENNReal.ofReal_le_ofReal hG
    rwa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast, ENNReal.ofReal_mul' (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at this
  exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).1
    ((measure_pi_not_isEpsNet_mul_two_pow_le μ G hm).trans h2)

/-- **The ε-net theorem with an explicit sample size** on a countable domain
[BlumerEhrenfeuchtHausslerWarmuth1989; ShalevShwartzBenDavid2014, Section 28.3]: if every finite
set shattered by `G` has at most `d` points and `m ≥ (8 / ε) (d log (48 / ε) + log (4 / δ))`, then
`m` i.i.d. samples fail to be an ε-net for `G` with probability at most `δ`. The constants differ
from those of the cited sources but have the same form. -/
theorem measure_pi_not_isEpsNet_le_of_vcSampleSize_le (μ : Measure Z) [IsProbabilityMeasure μ]
    {G : ConceptClass Z Bool} {d : ℕ} (hG : ∀ W : Finset Z, SetShatters G ↑W → W.card ≤ d)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {m : ℕ}
    (hm : vcSampleSize d ε δ ≤ m) :
    Measure.pi (fun _ : Fin m => μ) {S | ¬ IsEpsNet μ G ε S} ≤ ENNReal.ofReal δ := by
  obtain ⟨h8, hgrowth⟩ := growthFunction_le_of_vcSampleSize_le hG hε hε1 hδ hδ1 hm
  exact measure_pi_not_isEpsNet_le_of_growthFunction_le μ G h8 hgrowth

end Cslib.MachineLearning.PACLearning
