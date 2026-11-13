/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.VCUniformConvergence
public import CslibFrontier.MachineLearning.PACLearning.VCUpperBound
import CslibFrontier.Foundations.Combinatorics.Hoeffding
import CslibFrontier.MachineLearning.PACLearning.VCDimension
import CslibFrontier.MachineLearning.Rademacher.Chaining

/-! # The sharp agnostic sample size for classes of finite VC dimension

If every finite set shattered by a Boolean class `G` on a countable domain has at most `d` points,
then for `m ≥ 16384 d / ε²` i.i.d. samples from `μ`, the relative frequency of some `{g = true}`,
`g ∈ G`, deviates from its probability by at least `ε` with probability at most
`4 exp (-m ε² / 32)`. Unlike `measure_pi_exists_le_abs_card_filter_div_sub_measure_le`, the bound
has no growth-function factor, so the sample size

`chainingSampleSize d ε δ = (16384 d + 32 log (4 / δ)) / ε²`

that brings it below `δ` has no factor `log (1 / ε)`. For the loss class of a binary concept class
`C` this gives uniform convergence, agnostic PAC learning by empirical risk minimization from
`chainingSampleSize d (ε / 2) δ` examples, and the agnostic sample-complexity bound
`O ((d + log (1 / δ)) / ε²)` of [ShalevShwartzBenDavid2014, Theorem 6.8]. Shalev-Shwartz and
Ben-David prove only the weaker `O ((d log (d / ε) + log (1 / δ)) / ε²)` (Section 28.1) and do not
apply their chaining lemma (Lemma 27.4) to the sharp form; the route here is that of
[Vershynin2018, Section 8.3], with explicit, unoptimized constants.

The proof is double-sample symmetrization with a different swap step.

* **Ghost sample.**
  `measure_pi_exists_le_abs_card_filter_div_sub_measure_le_of_card_filter_swapSamples_le`
  reduces the bound to the fraction of the `2 ^ m` swaps of a fixed double sample `z` under which
  some `g ∈ G` has counts on the two swapped samples that differ by at least `m ε / 2`.
* **Swaps.** Under the swap `σ`, the count difference of `g` is `∑ i, a_g i · signVal (σ i)`, where
  `a_g i = g (z.1 i) - g (z.2 i) ∈ {-1, 0, 1}`. The supremum over `g ∈ G` of this sum changes by at
  most `2` when one sign changes, so McDiarmid's inequality
  (`Cslib.BitString.card_filter_expect_add_le_le`) bounds the fraction of swaps on which it exceeds
  its mean by `m ε / 4` by `exp (-m ε² / 32)`. The vector `a_g` depends only on the labeling of the
  `2m` points of `z` by `g`, with `‖a_g - a_g'‖² ≤ 2 · hammingDist`, so the chaining bound
  `Cslib.MachineLearning.expect_ciSup_sum_mul_signVal_le_of_hammingDist` puts the mean at most
  `32 √(m d) ≤ m ε / 4`. The same holds for `-a_g`.

Through the loss class, whose shattered sets are no larger than those of `C`
(`card_le_of_setShatters_lossClass` in `VCUpperBound.lean`), this gives the classification results.
The domain is countable with measurable singletons, as in `VCUniformConvergence.lean`; uncountable
domains need a measurability hypothesis on the class. The constants are far from optimal: at
`ε = δ = 1 / 10` and `d = 1` the explicit size is about `6.6 · 10⁶`, against `97600` from
`uniformConvergenceSampleSize`. The improvement is in the rate, which wins only as `ε → 0`.

## Main definitions

- `chainingSampleSize d ε δ`: the sample size `(16384 d + 32 log (4 / δ)) / ε²`.

## Main results

- `card_filter_swapSamples_exists_le_abs_le`: the fraction of bad swaps of a double sample is at
  most `2 exp (-m ε² / 32)` once `16384 d ≤ m ε²`.
- `measure_pi_exists_le_abs_card_filter_div_sub_measure_le_exp`: **uniform convergence without a
  growth-function factor**, with bound `4 exp (-m ε² / 32)`.
- `measure_pi_not_isRepresentative_le_exp`,
  `measure_pi_not_isRepresentative_le_of_chainingSampleSize_le`: the same for `ε`-representative
  samples, and with the explicit sample size.
- `IsERM.measure_pi_lt_error_le_exp`, `IsERM.measure_pi_lt_error_le_of_chainingSampleSize_le`: the
  agnostic tail bound for empirical risk minimization.
- `isPACLearnerFor_univ_of_chainingSampleSize_le`, `sampleComplexity_univ_le_chainingSampleSize`:
  agnostic PAC learning from `chainingSampleSize d (ε / 2) δ` examples, and the sample-complexity
  bound `⌈chainingSampleSize (vcDim C) (ε / 2) δ⌉`.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Theorem 6.8, Lemma 27.4 and Section 28.1
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Section 8.3
* [C. McDiarmid, *On the method of bounded differences*][McDiarmid1989], Lemma 1.2
-/

public section

open MeasureTheory Cslib.BitString
open scoped ENNReal NNReal Finset BigOperators

namespace Cslib.MachineLearning.PACLearning

/-! ### Counting swaps by chaining -/

open Classical in
/-- If the vectors `b j` have entries in `[-1, 1]` and their maximal correlation with a uniformly
random sign vector has mean at most `m ε / 4`, then at most a `exp (-m ε² / 32)` fraction of the
sign vectors give some `b j` correlation at least `m ε / 2`. -/
private theorem card_filter_exists_le_sum_mul_signVal_le {ι : Type*} {m : ℕ} (b : ι → Fin m → ℝ)
    (hb : ∀ j i, |b j i| ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : 𝔼 σ : Fin m → Bool, ⨆ j, ∑ i, b j i * signVal (σ i) ≤ m * ε / 4) :
    (#{σ : Fin m → Bool | ∃ j, m * ε / 2 ≤ ∑ i, b j i * signVal (σ i)} : ℝ) ≤
      2 ^ m * Real.exp (-(m * ε ^ 2 / 32)) := by
  set F : (Fin m → Bool) → ℝ := fun σ => ⨆ j, ∑ i, b j i * signVal (σ i) with hFdef
  have hbdd (σ : Fin m → Bool) : BddAbove (Set.range fun j => ∑ i, b j i * signVal (σ i)) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨j, rfl⟩
    calc ∑ i, b j i * signVal (σ i) ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
          calc b j i * signVal (σ i) ≤ |b j i * signVal (σ i)| := le_abs_self _
            _ = |b j i| := by rw [abs_mul, abs_signVal, mul_one]
            _ ≤ 1 := hb j i
      _ = m := by simp
  -- Changing one sign changes the maximal correlation by at most `2`.
  have hF : Probability.HasBoundedDifferences (α := fun _ : Fin m => Bool) F fun _ => 2 :=
    Probability.HasBoundedDifferences.ciSup (fun _ => by norm_num)
      (fun j => Probability.hasBoundedDifferences_sum (α := fun _ : Fin m => Bool)
        (score := fun i c => b j i * signVal c) fun i c c' => by
          rw [← mul_sub, abs_mul]
          calc |b j i| * |signVal c - signVal c'| ≤ 1 * 2 := by
                gcongr
                · exact hb j i
                · cases c <;> cases c' <;> norm_num [signVal]
            _ = 2 := one_mul 2) hbdd
  have hmc := card_filter_expect_add_le_le hF (t := m * ε / 4) (by positivity)
  have hsum : ∑ _i : Fin m, (2 : ℝ) ^ 2 = m * 4 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hexp : 2 * ((m : ℝ) * ε / 4) ^ 2 / (m * 4) = m * ε ^ 2 / 32 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : (0 : ℝ) < m := Nat.cast_pos.2 hm
      field_simp
      ring
  rw [hsum, Fintype.card_fin, hexp] at hmc
  have hsub : (Finset.univ.filter fun σ : Fin m → Bool =>
      ∃ j, m * ε / 2 ≤ ∑ i, b j i * signVal (σ i)) ⊆
      Finset.univ.filter fun σ => (𝔼 y, F y) + m * ε / 4 ≤ F σ := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨j, hj⟩ := hσ
    have := le_ciSup (hbdd σ) j
    linarith
  exact (Nat.cast_le.2 (Finset.card_le_card hsub)).trans hmc

open Classical in
/-- **Counting bad swaps by chaining**: if every finite set shattered by `G` has at most `d` points
and `16384 d ≤ m ε²`, then for every double sample `z`, at most a `2 exp (-m ε² / 32)` fraction of
the swaps `σ` give some `g ∈ G` counts on the two swapped samples that differ by at least
`m ε / 2`. -/
theorem card_filter_swapSamples_exists_le_abs_le {Z : Type*} {G : ConceptClass Z Bool} {d : ℕ}
    (hG : ∀ W : Finset Z, SetShatters G ↑W → W.card ≤ d) {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hm : 16384 * d ≤ m * ε ^ 2) (z : (Fin m → Z) × (Fin m → Z)) :
    (#{σ : Fin m → Bool | ∃ g ∈ G, m * ε / 2 ≤
        |((Finset.univ.filter fun i => g ((swapSamples σ z).1 i) = true).card : ℝ) -
          (Finset.univ.filter fun i => g ((swapSamples σ z).2 i) = true).card|} : ℝ) ≤
      2 ^ m * (2 * Real.exp (-(m * ε ^ 2 / 32))) := by
  set x : Fin (m + m) → Z := Fin.append z.1 z.2 with hx
  set a : (Z → Bool) → Fin m → ℝ := fun g i => ((g (z.1 i)).toNat : ℝ) - (g (z.2 i)).toNat
    with ha
  -- After the swap `σ`, the count difference of `g` is the correlation of `a g` with the signs.
  have hkey (g : Z → Bool) (σ : Fin m → Bool) :
      ((Finset.univ.filter fun i => g ((swapSamples σ z).1 i) = true).card : ℝ) -
          (Finset.univ.filter fun i => g ((swapSamples σ z).2 i) = true).card =
        ∑ i, a g i * signVal (σ i) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [a, fst_swapSamples_apply, snd_swapSamples_apply]
    cases hσ : σ i <;> cases h1 : g (z.1 i) <;> cases h2 : g (z.2 i) <;>
      simp [signVal, h1, h2]
  -- The Hamming distance of two labelings of the double sample, split over its halves.
  have hham (g g' : Z → Bool) : (hammingDist (fun j => g (x j)) (fun j => g' (x j)) : ℝ) =
      ∑ i, ((if g (z.1 i) ≠ g' (z.1 i) then 1 else 0 : ℝ) +
        if g (z.2 i) ≠ g' (z.2 i) then 1 else 0) := by
    rw [hammingDist, Finset.card_filter]
    push_cast
    rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
    simp only [x, Fin.append_left, Fin.append_right]
  have hb (s : ℝ) (hs : s ^ 2 = 1) (g : G) (i : Fin m) : |s * a g i| ≤ 1 := by
    refine (sq_le_one_iff_abs_le_one _).1 ?_
    rw [mul_pow, hs, one_mul]
    simp only [a]
    cases g.1 (z.1 i) <;> cases g.1 (z.2 i) <;> norm_num
  have hnorm (s : ℝ) (hs : s ^ 2 = 1) (g : G) : ∑ i, (s * a g i) ^ 2 ≤ √m ^ 2 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg m)]
    calc ∑ i, (s * a g i) ^ 2 ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have := hb s hs g i
          rw [← sq_abs]
          nlinarith [abs_nonneg (s * a g i)]
      _ = m := by simp
  have hdist (s : ℝ) (hs : s ^ 2 = 1) (g g' : G) :
      ∑ i, (s * a g i - s * a g' i) ^ 2 ≤
        4 * √m ^ 2 / ((m + m : ℕ) : ℝ) *
          hammingDist (fun j => g.1 (x j)) (fun j => g'.1 (x j)) := by
    have hpt (i : Fin m) : (s * a g i - s * a g' i) ^ 2 ≤
        2 * ((if g.1 (z.1 i) ≠ g'.1 (z.1 i) then 1 else 0 : ℝ) +
          if g.1 (z.2 i) ≠ g'.1 (z.2 i) then 1 else 0) := by
      rw [← mul_sub, mul_pow, hs, one_mul]
      simp only [a]
      cases g.1 (z.1 i) <;> cases g'.1 (z.1 i) <;> cases g.1 (z.2 i) <;> cases g'.1 (z.2 i) <;>
        norm_num
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
    rw [Real.sq_sqrt hmR.le, show 4 * (m : ℝ) / ((m + m : ℕ) : ℝ) = 2 by
      push_cast; field_simp; ring, hham, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hpt i
  -- Chaining: the expected maximal correlation is at most `32 √(m d) ≤ m ε / 4`.
  have hE (s : ℝ) (hs : s ^ 2 = 1) :
      𝔼 σ : Fin m → Bool, ⨆ g : G, ∑ i, s * a g i * signVal (σ i) ≤ m * ε / 4 := by
    refine (expect_ciSup_sum_mul_signVal_le_of_hammingDist hG x (fun (g : G) j => g.1 (x j))
      (fun g => mem_restriction.2 ⟨g.1, g.2, fun _ => rfl⟩) (fun g i => s * a g i)
      (r := √m) (Real.sqrt_nonneg _) (hnorm s hs) (hdist s hs)).trans ?_
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : 128 * √d ≤ √m * ε := by
      rw [← Real.sqrt_sq hε, ← Real.sqrt_mul hm0, show (128 : ℝ) = √(128 ^ 2) by
        rw [Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (show (0 : ℝ) ≤ 128 ^ 2 by norm_num) d]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    calc 32 * √m * √d = √m * (128 * √d) / 4 := by ring
      _ ≤ √m * (√m * ε) / 4 := by gcongr
      _ = m * ε / 4 := by rw [← mul_assoc, Real.mul_self_sqrt hm0]
  -- McDiarmid for `a` and for `-a`.
  have h1 := card_filter_exists_le_sum_mul_signVal_le (fun (g : G) i => 1 * a g i)
    (hb 1 (by norm_num)) hε (hE 1 (by norm_num))
  have h2 := card_filter_exists_le_sum_mul_signVal_le (fun (g : G) i => -1 * a g i)
    (hb (-1) (by norm_num)) hε (hE (-1) (by norm_num))
  have hsub : (Finset.univ.filter fun σ : Fin m → Bool => ∃ g ∈ G, m * ε / 2 ≤
        |((Finset.univ.filter fun i => g ((swapSamples σ z).1 i) = true).card : ℝ) -
          (Finset.univ.filter fun i => g ((swapSamples σ z).2 i) = true).card|) ⊆
      (Finset.univ.filter fun σ : Fin m → Bool =>
        ∃ g : G, m * ε / 2 ≤ ∑ i, 1 * a g i * signVal (σ i)) ∪
      Finset.univ.filter fun σ : Fin m → Bool =>
        ∃ g : G, m * ε / 2 ≤ ∑ i, -1 * a g i * signVal (σ i) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hσ ⊢
    obtain ⟨g, hg, hgap⟩ := hσ
    rw [hkey] at hgap
    rcases le_abs.1 hgap with h | h
    · refine Or.inl ⟨⟨g, hg⟩, ?_⟩
      simp only [one_mul]
      exact h
    · refine Or.inr ⟨⟨g, hg⟩, ?_⟩
      simpa only [neg_mul, one_mul, Finset.sum_neg_distrib] using h
  have hcard := (Nat.cast_le (α := ℝ)).2 ((Finset.card_le_card hsub).trans
    (Finset.card_union_le _ _))
  push_cast at hcard
  linarith

/-! ### Uniform convergence -/

section Countable

variable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z] [Countable Z]

/-- **Uniform convergence without a growth-function factor** on a countable domain
[Vershynin2018, Section 8.3]: if every finite set shattered by `G` has at most `d` points and
`16384 d ≤ m ε²`, then under `m` i.i.d. samples from `μ`, the probability that the relative
frequency of `{g = true}` deviates from `μ {g = true}` by at least `ε` for some `g ∈ G` is at most
`4 exp (-m ε² / 32)`. -/
theorem measure_pi_exists_le_abs_card_filter_div_sub_measure_le_exp (μ : Measure Z)
    [IsProbabilityMeasure μ] {G : ConceptClass Z Bool} {d : ℕ}
    (hG : ∀ W : Finset Z, SetShatters G ↑W → W.card ≤ d) {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hm : 16384 * d ≤ m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => μ)
        {S | ∃ g ∈ G, ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
          (μ {z | g z = true}).toReal|} ≤
      ENNReal.ofReal (4 * Real.exp (-(m * ε ^ 2 / 32))) := by
  by_cases hbig : 1 ≤ 4 * Real.exp (-(m * ε ^ 2 / 32))
  · exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hbig)
  push Not at hbig
  have hexp : 4 * Real.exp (-(m * ε ^ 2 / 2)) ≤ 1 := by
    have : Real.exp (-(m * ε ^ 2 / 2)) ≤ Real.exp (-(m * ε ^ 2 / 32)) :=
      Real.exp_le_exp.2 <| by
        have := mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (sq_nonneg ε)
        linarith
    linarith
  refine (measure_pi_exists_le_abs_card_filter_div_sub_measure_le_of_card_filter_swapSamples_le μ G
    m hε hexp (β := 2 * Real.exp (-(m * ε ^ 2 / 32)))
    fun z => card_filter_swapSamples_exists_le_abs_le hG hε hm z).trans_eq (by congr 1; ring)

end Countable

/-- The sample size `(16384 d + 32 log (4 / δ)) / ε²` of the chaining bound. -/
@[expose] noncomputable def chainingSampleSize (d : ℕ) (ε δ : ℝ) : ℝ :=
  (16384 * d + 32 * Real.log (4 / δ)) / ε ^ 2

section Classification

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- **Uniform convergence without a growth-function factor** for a binary concept class on a
countable domain: if every finite set shattered by `C` has at most `d` points and
`16384 d ≤ m ε²`, then `m` i.i.d. examples fail to be `ε`-representative for `C` with probability
at most `4 exp (-m ε² / 32)`. -/
theorem measure_pi_not_isRepresentative_le_exp (D : Measure (α × Bool)) [IsProbabilityMeasure D]
    {C : ConceptClass α Bool} {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    {m : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hm : 16384 * d ≤ m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D C ε S} ≤
      ENNReal.ofReal (4 * Real.exp (-(m * ε ^ 2 / 32))) := by
  refine le_trans (measure_mono fun S hS => ?_)
    (measure_pi_exists_le_abs_card_filter_div_sub_measure_le_exp D
      (card_le_of_setShatters_lossClass hC) hε hm)
  simp only [IsRepresentative, not_forall, not_le, Set.mem_ofPred_eq] at hS
  obtain ⟨h, hh, hlt⟩ := hS
  refine ⟨fun p => decide (h p.1 ≠ p.2), mem_lossClass.2 ⟨h, hh, rfl⟩, ?_⟩
  simpa only [empiricalMiscount, error, decide_eq_true_eq] using hlt.le

/-- **Uniform convergence with the chaining sample size** on a countable domain: if every finite
set shattered by `C` has at most `d` points and `m ≥ (16384 d + 32 log (4 / δ)) / ε²`, then `m`
i.i.d. examples fail to be `ε`-representative for `C` with probability at most `δ`. -/
theorem measure_pi_not_isRepresentative_le_of_chainingSampleSize_le (D : Measure (α × Bool))
    [IsProbabilityMeasure D] {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hm : chainingSampleSize d ε δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D C ε S} ≤ ENNReal.ofReal δ := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hδ1)
  have hlog : 0 ≤ Real.log (4 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [chainingSampleSize, div_le_iff₀ (by positivity)] at hm
  refine (measure_pi_not_isRepresentative_le_exp D hC hε.le (by linarith)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc 4 * Real.exp (-(m * ε ^ 2 / 32)) ≤ 4 * Real.exp (-Real.log (4 / δ)) := by
        gcongr
        linarith
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]; ring

/-- **Agnostic tail bound for ERM without a growth-function factor** on a countable domain: if every
finite set shattered by `C` has at most `d` points and `65536 d ≤ m ε²`, then under every
distribution an empirical risk minimizer for `C` misses `optimalError D C + ε` with probability at
most `4 exp (-m ε² / 128)`. -/
theorem IsERM.measure_pi_lt_error_le_exp (D : Measure (α × Bool)) [IsProbabilityMeasure D]
    {C : ConceptClass α Bool} {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    {m : ℕ} {A : Learner α Bool m} (hA : IsERM A C) {ε : ℝ} (hε : 0 ≤ ε)
    (hm : 65536 * d ≤ m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal (4 * Real.exp (-(m * ε ^ 2 / 128))) := by
  refine (measure_mono fun S hS => ?_).trans
    ((measure_pi_not_isRepresentative_le_exp D hC (ε := ε / 2) (by positivity)
      (by rw [show (m : ℝ) * (ε / 2) ^ 2 = m * ε ^ 2 / 4 by ring]; linarith)).trans_eq
      (by rw [show (m : ℝ) * (ε / 2) ^ 2 / 32 = m * ε ^ 2 / 128 by ring]))
  exact fun hrep => (not_le.2 hS) (hrep.error_le_optimalError_add hA)

/-- **Agnostic learning by ERM with the chaining sample size** on a countable domain: if every
finite set shattered by `C` has at most `d` points and
`m ≥ chainingSampleSize d (ε / 2) δ = (65536 d + 128 log (4 / δ)) / ε²`, then under every
distribution an empirical risk minimizer for `C` misses `optimalError D C + ε` with probability at
most `δ`. -/
theorem IsERM.measure_pi_lt_error_le_of_chainingSampleSize_le (D : Measure (α × Bool))
    [IsProbabilityMeasure D] {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {A : Learner α Bool m}
    (hA : IsERM A C) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hm : chainingSampleSize d (ε / 2) δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans
    (measure_pi_not_isRepresentative_le_of_chainingSampleSize_le D hC (by positivity) hδ hm)
  exact fun hrep => (not_le.2 hS) (hrep.error_le_optimalError_add hA)

/-- **The sharp agnostic sample size** [ShalevShwartzBenDavid2014, Theorem 6.8] on a countable
domain: a class whose shattered finite sets have at most `d` points is `(ε, δ)`-PAC learnable over
all distributions from `m ≥ chainingSampleSize d (ε / 2) δ = O ((d + log (1 / δ)) / ε²)`
examples. If `C` is nonempty the learner is any empirical risk minimizer. If `C` is empty the
optimal error is `⊤` and any learner works. -/
theorem isPACLearnerFor_univ_of_chainingSampleSize_le {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : chainingSampleSize d ((ε.val : ℝ) / 2) δ.val ≤ m) :
    IsPACLearnerFor m ε δ C Set.univ := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => false, fun D _ _ => by simp [optimalError]⟩
  obtain ⟨A, hA⟩ := exists_isERM (m := m) hne
  refine ⟨A, fun D _ _ => ?_⟩
  have h := hA.measure_pi_lt_error_le_of_chainingSampleSize_le D hC
    (by exact_mod_cast ε.2.1) (by exact_mod_cast δ.2.1) hm
  rwa [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h

/-- The agnostic sample complexity of a class of finite VC dimension on a countable domain is at
most `⌈chainingSampleSize (vcDim C) (ε / 2) δ⌉ = O ((vcDim C + log (1 / δ)) / ε²)`
[ShalevShwartzBenDavid2014, Theorem 6.8]. -/
theorem sampleComplexity_univ_le_chainingSampleSize {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor C ε δ Set.univ ≤
      ⌈chainingSampleSize (vcDim C) ((ε.val : ℝ) / 2) δ.val⌉₊ :=
  Nat.sInf_le (isPACLearnerFor_univ_of_chainingSampleSize_le
    (fun _ hW => hW.card_le_vcDim hC) (Nat.le_ceil _))

end Classification

end Cslib.MachineLearning.PACLearning
