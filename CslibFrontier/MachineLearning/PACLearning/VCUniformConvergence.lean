/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
public import CslibFrontier.MachineLearning.PACLearning.UniformConvergence
public import CslibFrontier.MachineLearning.PACLearning.DoubleSample
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.Combinatorics.Hoeffding
import CslibFrontier.MachineLearning.PACLearning.VCUpperBound

/-! # Uniform convergence from the growth function on countable domains

Let `G` be a class of Boolean functions on a countable domain `Z` with measurable singletons and
let `μ` be a probability measure on `Z`. The *uniform convergence theorem of Vapnik and
Chervonenkis* bounds the probability that the relative frequency of some event `{g = true}`,
`g ∈ G`, in `m` i.i.d. samples differs from its probability by at least `ε`:

`μ^m {S | ∃ g ∈ G, ε ≤ |#{i | g (S i)} / m - μ {g = true}|} ≤ 4 Π_G(2m) exp (-m ε² / 8)`,

where `Π_G` is the growth function [VapnikChervonenkis1971; AnthonyBartlett1999, Theorem 4.3].
Applied to the loss class of a binary concept class `C` and a distribution `D` on labeled
examples, this says that `m` i.i.d. examples fail to be `ε`-representative for `C` (in the sense of
[ShalevShwartzBenDavid2014, Definition 4.1]) with probability at most
`4 Π_C(2m) exp (-m ε² / 8)`. With Sauer's lemma, the explicit sample size

`uniformConvergenceSampleSize d ε δ = (16 / ε²) (2 d log (10 / ε) + log (4 / δ))`

brings the failure probability below `δ` when every set shattered by `C` has at most `d` points.

The proof is the double-sample symmetrization argument, with the measure-theoretic steps from
`DoubleSample.lean`.

* **Ghost sample.** If `g` witnesses a deviation of at least `ε` on `S`, then by Hoeffding's
  inequality (`measure_pi_le_abs_card_filter_div_sub_measure`) an independent sample `T` has
  relative frequency within `ε / 2` of `μ {g = true}` with probability at least `1 / 2`. The bad
  event therefore has at most twice the probability of the *double-sample event*: some `g ∈ G`
  has counts on `S` and `T` that differ by at least `m ε / 2`.
* **Swaps.** For a fixed double sample, the change of `g`'s count difference under the swap `σ` is
  the weighted bit sum `∑ i, w i (σ i - 1 / 2)` with weights `|w i| ≤ 2`. Hoeffding's inequality
  for random bit strings (`Cslib.BitString.card_filter_le_abs_sum_mul_sub_half_le`) bounds the
  number of swaps that make it at least `m ε / 2` by `2 · 2^m exp (-m ε² / 8)`. The weights depend
  only on the labeling of the `2m` sample points by `g`, and at most `Π_G(2m)` labelings occur.

The ghost-sample step is stated separately, for any bound on the fraction of bad swaps
(`measure_pi_exists_le_abs_card_filter_div_sub_measure_le_of_card_filter_swapSamples_le`);
`AgnosticVCSharp.lean` bounds that fraction by chaining instead of the union over labelings.

The theorem is stated with `≤ |…|` (a deviation of at least `ε`), which is slightly stronger than
the strict form `> ε` in the sources, and for all `ε ≥ 0` and `m`; when `4 Π_G(2m) exp (-m ε² / 8)`
is at least `1` it is trivial. The domain is assumed countable with measurable singletons, so that
every set of samples is measurable. Over general domains the theorem needs a measurability
hypothesis on the class, which is not formalized here.

## Main definitions

- `uniformConvergenceSampleSize d ε δ`: the sample size
  `(16 / ε²) (2 d log (10 / ε) + log (4 / δ))`.

## Main results

- `measure_pi_exists_le_abs_card_filter_div_sub_measure_le_of_card_filter_swapSamples_le`: the
  ghost-sample step, from any bound on the fraction of bad swaps of each double sample.
- `measure_pi_exists_le_abs_card_filter_div_sub_measure_le`: **uniform convergence of relative
  frequencies** for a Boolean class, with the bound `4 Π_G(2m) exp (-m ε² / 8)`.
- `measure_pi_exists_le_abs_empiricalMiscount_div_sub_error_le`: the same bound for the empirical
  errors of a binary concept class.
- `measure_pi_not_isRepresentative_le_growthFunction`: `m` i.i.d. examples fail to be
  `ε`-representative with probability at most `4 Π_C(2m) exp (-m ε² / 8)`.
- `four_mul_growthFunction_mul_exp_le_of_uniformConvergenceSampleSize_le`: the explicit sample size
  brings this below `δ`.
- `measure_pi_not_isRepresentative_le_of_uniformConvergenceSampleSize_le`: uniform convergence with
  the explicit sample size.

## References

* [V. N. Vapnik, A. Ya. Chervonenkis, *On the uniform convergence of relative frequencies of events
  to their probabilities*][VapnikChervonenkis1971]
* [M. Anthony, P. L. Bartlett, *Neural Network Learning: Theoretical
  Foundations*][AnthonyBartlett1999]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Finset

namespace Cslib.MachineLearning.PACLearning

/-! ### Counting swaps -/

/-- For weights `|w i| ≤ 2`, at most `2 · 2^m exp (-m ε² / 8)` of the bit strings `σ` make the
weighted sum `∑ i, w i (σ i - 1 / 2)` at least `m ε / 2` in absolute value. -/
private theorem card_filter_le_abs_sum_mul_sub_half_le_of_abs_le {m : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, |w i| ≤ 2) {ε : ℝ} (hε : 0 ≤ ε) :
    (#{σ : Fin m → Bool | m * ε / 2 ≤ |∑ i, w i * (((σ i).toNat : ℝ) - 1 / 2)|} : ℝ) ≤
      2 * 2 ^ m * Real.exp (-(m * ε ^ 2 / 8)) := by
  classical
  have hcard : (#{σ : Fin m → Bool | m * ε / 2 ≤ |∑ i, w i * (((σ i).toNat : ℝ) - 1 / 2)|} : ℝ) ≤
      2 ^ m := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin m → Bool))
      (fun σ => m * ε / 2 ≤ |∑ i, w i * (((σ i).toNat : ℝ) - 1 / 2)|)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine hcard.trans ?_
    simp
  set S := ∑ i, w i ^ 2 with hS
  have hS4 : S ≤ 4 * m := by
    calc S ≤ ∑ _i : Fin m, (4 : ℝ) := Finset.sum_le_sum fun i _ => by
          have := sq_le_sq' (abs_le.1 (hw i)).1 (abs_le.1 (hw i)).2
          linarith
      _ = 4 * m := by simp [mul_comm]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rcases (Finset.sum_nonneg fun i _ => sq_nonneg (w i) : 0 ≤ S).eq_or_lt with hS0 | hSpos
  · -- all weights vanish, so the sum is `0`
    have hw0 : ∀ i, w i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (w i)).1 hS0.symm i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    rcases hε.eq_or_lt with rfl | hεpos
    · refine hcard.trans ?_
      simp
    · have hempty : (Finset.univ.filter fun σ : Fin m → Bool =>
          m * ε / 2 ≤ |∑ i, w i * (((σ i).toNat : ℝ) - 1 / 2)|) = ∅ := by
        refine Finset.filter_false_of_mem fun σ _ => ?_
        simp only [hw0, zero_mul, Finset.sum_const_zero, abs_zero, not_le]
        positivity
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
  · refine (Cslib.BitString.card_filter_le_abs_sum_mul_sub_half_le w
      (t := m * ε / 2) (by positivity)).trans ?_
    rw [Fintype.card_fin]
    have hexp : m * ε ^ 2 / 8 ≤ 2 * (m * ε / 2) ^ 2 / S := by
      rw [le_div_iff₀ hSpos]
      have : 0 ≤ (m : ℝ) * ε ^ 2 := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg hexp)) (by positivity)

/-- The double-sample event: some `g ∈ G` has counts on the two samples that differ by at least
`m ε / 2`. -/
private def gapEvent {Z : Type*} (G : ConceptClass Z Bool) (m : ℕ) (ε : ℝ) :
    Set ((Fin m → Z) × (Fin m → Z)) :=
  {z | ∃ g ∈ G, m * ε / 2 ≤ |((Finset.univ.filter fun i => g (z.1 i) = true).card : ℝ) -
    (Finset.univ.filter fun i => g (z.2 i) = true).card|}

open Classical in
/-- For a fixed double sample, at most `Π_G(2m) · 2 · 2^m exp (-m ε² / 8)` swaps land in the
double-sample event. -/
private theorem card_filter_swapSamples_mem_gapEvent_le {Z : Type*} (G : ConceptClass Z Bool)
    {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (z : (Fin m → Z) × (Fin m → Z)) :
    ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ gapEvent G m ε).card : ℝ) ≤
      growthFunction G (m + m) * (2 * 2 ^ m * Real.exp (-(m * ε ^ 2 / 8))) := by
  set x : Fin (m + m) → Z := Fin.append z.1 z.2
  set R : Finset (Fin (m + m) → Bool) := (Set.toFinite (restriction G x)).toFinset
  -- The weight of coordinate `i` under the labeling `v` of the `2m` points.
  set w : (Fin (m + m) → Bool) → Fin m → ℝ := fun v i =>
    2 * (((v (Fin.natAdd m i)).toNat : ℝ) - (v (Fin.castAdd m i)).toNat)
  have hw : ∀ v i, |w v i| ≤ 2 := fun v i => by
    simp only [w]
    cases v (Fin.natAdd m i) <;> cases v (Fin.castAdd m i) <;> norm_num
  -- After the swap `σ`, the count difference of `g` is a weighted bit sum.
  have hkey : ∀ (g : Z → Bool) (σ : Fin m → Bool),
      ((Finset.univ.filter fun i => g ((swapSamples σ z).1 i) = true).card : ℝ) -
          (Finset.univ.filter fun i => g ((swapSamples σ z).2 i) = true).card =
        ∑ i, w (fun j => g (x j)) i * (((σ i).toNat : ℝ) - 1 / 2) := by
    intro g σ
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, x, Fin.append_left, Fin.append_right, fst_swapSamples_apply,
      snd_swapSamples_apply]
    cases hσ : σ i <;> cases h1 : g (z.1 i) <;> cases h2 : g (z.2 i) <;> norm_num [h1, h2]
  -- Each swap in the event is caught by the labeling of one realized pattern.
  have hcover : (Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ gapEvent G m ε) ⊆
      R.biUnion fun v => Finset.univ.filter fun σ : Fin m → Bool =>
        m * ε / 2 ≤ |∑ i, w v i * (((σ i).toNat : ℝ) - 1 / 2)| := by
    intro σ hσ
    obtain ⟨g, hg, hgap⟩ := (Finset.mem_filter.1 hσ).2
    refine Finset.mem_biUnion.2 ⟨fun j => g (x j), ?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    · rw [Set.Finite.mem_toFinset]
      exact mem_restriction.2 ⟨g, hg, fun _ => rfl⟩
    · rwa [← hkey]
  have hR : (R.card : ℝ) ≤ growthFunction G (m + m) := by
    rw [← Set.ncard_eq_toFinset_card]
    exact_mod_cast ncard_restriction_le_growthFunction G x
  calc ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ gapEvent G m ε).card : ℝ)
      ≤ ((R.biUnion fun v => Finset.univ.filter fun σ : Fin m → Bool =>
          m * ε / 2 ≤ |∑ i, w v i * (((σ i).toNat : ℝ) - 1 / 2)|).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ v ∈ R, ((Finset.univ.filter fun σ : Fin m → Bool =>
          m * ε / 2 ≤ |∑ i, w v i * (((σ i).toNat : ℝ) - 1 / 2)|).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ R, 2 * 2 ^ m * Real.exp (-(m * ε ^ 2 / 8)) :=
        Finset.sum_le_sum fun v _ =>
          card_filter_le_abs_sum_mul_sub_half_le_of_abs_le (w v) (hw v) hε
    _ = R.card * (2 * 2 ^ m * Real.exp (-(m * ε ^ 2 / 8))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ growthFunction G (m + m) * (2 * 2 ^ m * Real.exp (-(m * ε ^ 2 / 8))) := by
        gcongr

/-! ### Uniform convergence -/

section Countable

variable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z] [Countable Z]

open Classical in
/-- **The ghost-sample step** of double-sample symmetrization on a countable domain: suppose that
for every double sample `z`, at most a `β` fraction of the `2 ^ m` swaps `σ` give some `g ∈ G`
counts on the two swapped samples that differ by at least `m ε / 2`, and that
`4 exp (-m ε² / 2) ≤ 1`. Then the probability that the relative frequency of some `{g = true}`,
`g ∈ G`, in `m` i.i.d. samples deviates from `μ {g = true}` by at least `ε` is at most `2 β`.
Hoeffding's inequality puts the count of a fixed `g` on an independent ghost sample within
`m ε / 2` of `m μ {g = true}` with probability at least `1 / 2`, and swapping coordinates preserves
the law of the double sample. -/
theorem measure_pi_exists_le_abs_card_filter_div_sub_measure_le_of_card_filter_swapSamples_le
    (μ : Measure Z) [IsProbabilityMeasure μ] (G : ConceptClass Z Bool) (m : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (hexp : 4 * Real.exp (-(m * ε ^ 2 / 2)) ≤ 1) {β : ℝ}
    (hβ : ∀ z : (Fin m → Z) × (Fin m → Z),
      (#{σ : Fin m → Bool | ∃ g ∈ G, m * ε / 2 ≤
        |((Finset.univ.filter fun i => g ((swapSamples σ z).1 i) = true).card : ℝ) -
          (Finset.univ.filter fun i => g ((swapSamples σ z).2 i) = true).card|} : ℝ) ≤ 2 ^ m * β) :
    Measure.pi (fun _ : Fin m => μ)
        {S | ∃ g ∈ G, ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
          (μ {z | g z = true}).toReal|} ≤
      ENNReal.ofReal (2 * β) := by
  set ν := Measure.pi (fun _ : Fin m => μ) with hν
  set B := {S : Fin m → Z | ∃ g ∈ G, ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) /
    m - (μ {z | g z = true}).toReal|}
  set J := gapEvent G m ε
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num at hexp
    · exact hm
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hexp2 : 2 * Real.exp (-2 * m * (ε / 2) ^ 2) ≤ 1 / 2 := by
    rw [show -2 * (m : ℝ) * (ε / 2) ^ 2 = -(m * ε ^ 2 / 2) by ring]
    linarith
  have hJ : MeasurableSet J := .of_discrete
  -- Ghost sample: a deviation on `S` extends to the double-sample event with probability `≥ 1 / 2`.
  have hfib : ∀ S ∈ B, 1 / 2 ≤ ν (Prod.mk S ⁻¹' J) := by
    rintro S ⟨g, hg, hgS⟩
    set A := {T : Fin m → Z | ε / 2 ≤ |((Finset.univ.filter fun i => g (T i) = true).card : ℝ) /
      m - (μ {z | g z = true}).toReal|}
    have hA : ν A ≤ 1 / 2 := by
      refine (measure_pi_le_abs_card_filter_div_sub_measure μ (measurable_of_countable g) m
        (by positivity)).trans ?_
      rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]]
      exact ENNReal.ofReal_le_ofReal hexp2
    have hsub : Aᶜ ⊆ Prod.mk S ⁻¹' J := by
      intro T hT
      simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hT
      simp only [J, gapEvent, Set.mem_preimage, Set.mem_ofPred_eq]
      refine ⟨g, hg, ?_⟩
      set a := ((Finset.univ.filter fun i => g (S i) = true).card : ℝ)
      set b := ((Finset.univ.filter fun i => g (T i) = true).card : ℝ)
      have hab : ε / 2 ≤ |a / m - b / m| := by
        linarith [abs_sub_le (a / m) (b / m) (μ {z | g z = true}).toReal]
      have hdiff : a - b = m * (a / m - b / m) := by
        field_simp
      rw [hdiff, abs_mul, abs_of_pos hmR]
      calc (m : ℝ) * ε / 2 = m * (ε / 2) := by ring
        _ ≤ m * |a / m - b / m| := mul_le_mul_of_nonneg_left hab hmR.le
    calc (1 / 2 : ℝ≥0∞) = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - ν A := tsub_le_tsub_left hA 1
      _ = ν Aᶜ := (prob_compl_eq_one_sub .of_discrete).symm
      _ ≤ ν (Prod.mk S ⁻¹' J) := measure_mono hsub
  have hJB : ν B ≤ 2 * ν.prod ν J := measure_le_two_mul_measure_prod ν ν B hJ hfib
  -- Swaps: the double-sample event has probability at most `β`.
  have hK : ∀ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card :
      ℝ≥0∞) ≤ 2 ^ m * ENNReal.ofReal β := by
    intro z
    rw [← ENNReal.ofReal_natCast, show (2 : ℝ≥0∞) ^ m = ENNReal.ofReal (2 ^ m) by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hβ z)
  calc ν B ≤ 2 * ν.prod ν J := hJB
    _ ≤ 2 * ENNReal.ofReal β := by
        gcongr
        exact measure_prod_le_of_card_filter_swapSamples_mem_le μ hJ _ hK
    _ = ENNReal.ofReal (2 * β) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- **Uniform convergence of relative frequencies** on a countable domain [VapnikChervonenkis1971;
AnthonyBartlett1999, Theorem 4.3]: under `m` i.i.d. samples from `μ`, the probability that the
relative frequency of `{g = true}` deviates from `μ {g = true}` by at least `ε` for some `g ∈ G`
is at most `4 Π_G(2m) exp (-m ε² / 8)`. -/
theorem measure_pi_exists_le_abs_card_filter_div_sub_measure_le (μ : Measure Z)
    [IsProbabilityMeasure μ] (G : ConceptClass Z Bool) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => μ)
        {S | ∃ g ∈ G, ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
          (μ {z | g z = true}).toReal|} ≤
      ENNReal.ofReal (4 * growthFunction G (m + m) * Real.exp (-(m * ε ^ 2 / 8))) := by
  classical
  -- The bound is trivial when it is at least one.
  by_cases hbig : 1 ≤ 4 * (growthFunction G (m + m) : ℝ) * Real.exp (-(m * ε ^ 2 / 8))
  · exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hbig)
  push Not at hbig
  set B := {S : Fin m → Z | ∃ g ∈ G, ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) /
    m - (μ {z | g z = true}).toReal|} with hBdef
  rcases B.eq_empty_or_nonempty with hB | ⟨S₀, g₀, hg₀, -⟩
  · rw [hB, measure_empty]
    exact bot_le
  -- Otherwise `G` is nonempty, so `Π_G(2m) ≥ 1`, which forces `exp (-m ε² / 8) < 1 / 4`.
  have hN : (1 : ℝ) ≤ growthFunction G (m + m) := by
    have : 0 < growthFunction G (m + m) :=
      ((Set.ncard_pos (Set.toFinite _)).2 ⟨fun i => g₀ (Fin.append S₀ S₀ i),
        mem_restriction.2 ⟨g₀, hg₀, fun _ => rfl⟩⟩).trans_le
        (ncard_restriction_le_growthFunction G (Fin.append S₀ S₀))
    exact_mod_cast this
  have hexp4 : Real.exp (-(m * ε ^ 2 / 8)) < 1 / 4 := by
    have := le_mul_of_one_le_left (Real.exp_pos (-(m * ε ^ 2 / 8))).le hN
    linarith
  have hexp : 4 * Real.exp (-(m * ε ^ 2 / 2)) ≤ 1 := by
    have : Real.exp (-(m * ε ^ 2 / 2)) ≤ Real.exp (-(m * ε ^ 2 / 8)) :=
      Real.exp_le_exp.2 <| by
        have := mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (sq_nonneg ε)
        linarith
    linarith
  refine (measure_pi_exists_le_abs_card_filter_div_sub_measure_le_of_card_filter_swapSamples_le μ G
    m hε hexp (β := 2 * growthFunction G (m + m) * Real.exp (-(m * ε ^ 2 / 8))) fun z =>
      (card_filter_swapSamples_mem_gapEvent_le G hε z).trans_eq (by ring)).trans_eq
    (by congr 1; ring)

end Countable

section Classification

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- **Uniform convergence of empirical errors** on a countable domain [VapnikChervonenkis1971;
AnthonyBartlett1999, Theorem 4.3]: under `m` i.i.d. examples from `D`, the probability that the
empirical error of some `h ∈ C` deviates from its error by at least `ε` is at most
`4 Π_C(2m) exp (-m ε² / 8)`. -/
theorem measure_pi_exists_le_abs_empiricalMiscount_div_sub_error_le (D : Measure (α × Bool))
    [IsProbabilityMeasure D] (C : ConceptClass α Bool) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ h ∈ C, ε ≤ |(empiricalMiscount h S : ℝ) / m - (error D h).toReal|} ≤
      ENNReal.ofReal (4 * growthFunction C (m + m) * Real.exp (-(m * ε ^ 2 / 8))) := by
  have hsub : {S : LabeledSample α Bool m |
        ∃ h ∈ C, ε ≤ |(empiricalMiscount h S : ℝ) / m - (error D h).toReal|} ⊆
      {S | ∃ g ∈ lossClass C, ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
        (D {z | g z = true}).toReal|} := by
    rintro S ⟨h, hh, hS⟩
    refine ⟨fun p => decide (h p.1 ≠ p.2), mem_lossClass.2 ⟨h, hh, rfl⟩, ?_⟩
    simpa only [empiricalMiscount, error, decide_eq_true_eq] using hS
  refine (measure_mono hsub).trans
    ((measure_pi_exists_le_abs_card_filter_div_sub_measure_le D (lossClass C) m hε).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  have : (growthFunction (lossClass C) (m + m) : ℝ) ≤ growthFunction C (m + m) := by
    exact_mod_cast growthFunction_lossClass_le C _
  gcongr

/-- **Uniform convergence for a class with a bounded growth function** on a countable domain
[VapnikChervonenkis1971; AnthonyBartlett1999, Theorem 4.3]: `m` i.i.d. examples fail to be
`ε`-representative for `C` with probability at most `4 Π_C(2m) exp (-m ε² / 8)`. -/
theorem measure_pi_not_isRepresentative_le_growthFunction (D : Measure (α × Bool))
    [IsProbabilityMeasure D] (C : ConceptClass α Bool) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D C ε S} ≤
      ENNReal.ofReal (4 * growthFunction C (m + m) * Real.exp (-(m * ε ^ 2 / 8))) := by
  refine le_trans (measure_mono fun S hS => ?_)
    (measure_pi_exists_le_abs_empiricalMiscount_div_sub_error_le D C m hε)
  simp only [IsRepresentative, not_forall, not_le, Set.mem_ofPred_eq] at hS
  obtain ⟨h, hh, hlt⟩ := hS
  exact ⟨h, hh, hlt.le⟩

end Classification

/-! ### The explicit sample size -/

/-- The uniform convergence sample size `(16 / ε²) (2 d log (10 / ε) + log (4 / δ))`. -/
@[expose] noncomputable def uniformConvergenceSampleSize (d : ℕ) (ε δ : ℝ) : ℝ :=
  16 / ε ^ 2 * (2 * d * Real.log (10 / ε) + Real.log (4 / δ))

section SampleSize

variable {Z : Type*}

/-- The explicit sample size makes `4 Π_G(2m) exp (-m ε² / 8) ≤ δ` whenever every finite set
shattered by `G` has at most `d` points. The proof applies Sauer's lemma in the form
`Π_G(2m) ≤ exp (2m / T) T ^ d` (`growthFunction_le_exp_mul_pow`) at `T = (10 / ε)²`. -/
theorem four_mul_growthFunction_mul_exp_le_of_uniformConvergenceSampleSize_le
    {G : ConceptClass Z Bool} {d : ℕ} (hG : ∀ W : Finset Z, SetShatters G ↑W → W.card ≤ d)
    {m : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 10) (hδ : 0 < δ)
    (hm : uniformConvergenceSampleSize d ε δ ≤ m) :
    4 * (growthFunction G (m + m) : ℝ) * Real.exp (-(m * ε ^ 2 / 8)) ≤ δ := by
  have hT : 1 ≤ (10 / ε) ^ 2 := one_le_pow₀ (by rw [le_div_iff₀ hε]; linarith)
  have hexp : ((m + m : ℕ) : ℝ) / (10 / ε) ^ 2 = m * ε ^ 2 / 50 := by
    push_cast
    field_simp
    ring
  have hmε : 0 ≤ (m : ℝ) * ε ^ 2 := by positivity
  rw [uniformConvergenceSampleSize, div_mul_eq_mul_div, div_le_iff₀ (by positivity),
    Real.log_div (by norm_num) hδ.ne'] at hm
  calc 4 * (growthFunction G (m + m) : ℝ) * Real.exp (-(m * ε ^ 2 / 8))
      ≤ 4 * (Real.exp (((m + m : ℕ) : ℝ) / (10 / ε) ^ 2) * ((10 / ε) ^ 2) ^ d) *
          Real.exp (-(m * ε ^ 2 / 8)) := by
        gcongr
        exact growthFunction_le_exp_mul_pow hG _ hT
    _ ≤ δ := by
        rw [hexp, ← Real.log_le_log_iff (by positivity) hδ,
          Real.log_mul (by positivity) (Real.exp_pos _).ne',
          Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
          Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_exp,
          Real.log_pow, Real.log_pow]
        push_cast
        linarith

end SampleSize

section Classification

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- **Uniform convergence with an explicit sample size** on a countable domain: if every finite
set shattered by `C` has at most `d` points and `m ≥ (16 / ε²) (2 d log (10 / ε) + log (4 / δ))`,
then `m` i.i.d. examples fail to be `ε`-representative for `C` with probability at most `δ`. -/
theorem measure_pi_not_isRepresentative_le_of_uniformConvergenceSampleSize_le
    (D : Measure (α × Bool)) [IsProbabilityMeasure D] {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε10 : ε ≤ 10) (hδ : 0 < δ) (hm : uniformConvergenceSampleSize d ε δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D C ε S} ≤ ENNReal.ofReal δ :=
  (measure_pi_not_isRepresentative_le_growthFunction D C m hε.le).trans
    (ENNReal.ofReal_le_ofReal
      (four_mul_growthFunction_mul_exp_le_of_uniformConvergenceSampleSize_le hC hε hε10 hδ hm))

end Classification

end Cslib.MachineLearning.PACLearning
