/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.RealizableSample
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.MachineLearning.PACLearning.ERM

/-! # Finite concept classes are PAC learnable in the realizable setting

Let `H` be a finite concept class and `D` a probability distribution on `α × β` realizable by `H`.
A hypothesis whose true error exceeds `ε` agrees with `m` i.i.d. examples with probability at most
`(1 - ε) ^ m`. A consistent learner outputs a concept of the version space on almost every sample,
so by the union bound its error exceeds `ε` with probability at most `|H| (1 - ε) ^ m`. Hence

`m ≥ (log |H| + log (1 / δ)) / ε`

samples make *every* consistent learner (in particular every empirical risk minimizer, see
`IsERM.isConsistent`) an `(ε, δ)`-PAC learner over all distributions realizable by `H`
[ShalevShwartzBenDavid2014, Corollary 2.3]. Learners here are semantic maps from samples to
hypotheses; no running-time bound is claimed.

The probability bounds need the misclassification set `{p | h p.1 ≠ p.2}` of every `h ∈ H` to be
measurable. This holds when every `h ∈ H` is measurable and equality on `β` is measurable, see
`measurableSet_misclassified`; for instance when `β` is `Bool`.

## Main results

- `measure_pi_forall_apply_eq_eq_pow`: a hypothesis survives `m` i.i.d. examples with probability
  `(1 - error D h) ^ m`; `measure_pi_forall_apply_eq_eq_pow_card` indexes the examples by any
  finite type.
- `measure_pi_exists_consistent_lt_error_le_card_mul_pow`: the union bound `|H| (1 - ε) ^ m` on
  some `h ∈ H` with error above `ε` agreeing with every example, for any distribution.
- `IsConsistent.measure_pi_lt_error_le_card_mul_pow`: the union bound `|H| (1 - ε) ^ m` for a
  consistent learner of a finite class.
- `natCast_mul_one_sub_ofReal_pow_le`: `n (1 - ε) ^ m ≤ δ` once `log n + log (1 / δ) ≤ ε m`.
- `IsConsistent.measure_pi_lt_error_le_of_log_card_add_log_inv_le`: the Occam sample-size form.
- `isPACLearnerFor_realizableDistributions_of_log_card_add_log_inv_le`: finite classes are
  `(ε, δ)`-PAC learnable from `m` examples whenever `log |H| + log (1 / δ) ≤ ε m`.
- `sampleComplexity_realizableDistributions_le_of_finite`: the realizable sample complexity of a
  finite class is at most `⌈(log |H| + log (1 / δ)) / ε⌉`.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A fixed hypothesis `h` agrees with i.i.d. examples from `D` indexed by a finite type `ι` with
probability `(1 - error D h) ^ |ι|`. -/
theorem measure_pi_forall_apply_eq_eq_pow_card {ι : Type*} [Fintype ι] (D : Measure (α × β))
    [IsProbabilityMeasure D] {h : α → β} (hh : MeasurableSet {p : α × β | h p.1 ≠ p.2}) :
    Measure.pi (fun _ : ι => D) {S : ι → α × β | ∀ i, h (S i).1 = (S i).2} =
      (1 - error D h) ^ Fintype.card ι := by
  have hset : {S : ι → α × β | ∀ i, h (S i).1 = (S i).2} =
      Set.univ.pi fun _ => {p : α × β | h p.1 ≠ p.2}ᶜ := by
    ext S
    simp only [mem_ofPred_eq, mem_pi, mem_univ, mem_compl_iff, not_not, true_implies]
  rw [hset, Measure.pi_pi, prob_compl_eq_one_sub hh, Finset.prod_const, Finset.card_univ, error]

/-- A fixed hypothesis `h` agrees with all `m` i.i.d. examples drawn from `D` with probability
`(1 - error D h) ^ m`. -/
theorem measure_pi_forall_apply_eq_eq_pow (D : Measure (α × β)) [IsProbabilityMeasure D]
    {h : α → β} (hh : MeasurableSet {p : α × β | h p.1 ≠ p.2}) (m : ℕ) :
    Measure.pi (fun _ : Fin m => D) {S : LabeledSample α β m | ∀ i, h (S i).1 = (S i).2} =
      (1 - error D h) ^ m := by
  rw [measure_pi_forall_apply_eq_eq_pow_card D hh, Fintype.card_fin]

/-- **Union bound over a finite class.** For any distribution `D`, the probability over `m` i.i.d.
examples that some `h ∈ H` with true error greater than `ε` agrees with all of them is at most
`|H| (1 - ε) ^ m`. No learner and no realizability are involved. -/
theorem measure_pi_exists_consistent_lt_error_le_card_mul_pow {H : Finset (α → β)}
    (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) (D : Measure (α × β))
    [IsProbabilityMeasure D] {m : ℕ} (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin m => D)
        {S : LabeledSample α β m | ∃ h ∈ H, ε < error D h ∧ ∀ i, h (S i).1 = (S i).2} ≤
      H.card * (1 - ε) ^ m := by
  classical
  set μ := Measure.pi (fun _ : Fin m => D)
  set Bad := H.filter fun h => ε < error D h
  have hsub : {S : LabeledSample α β m | ∃ h ∈ H, ε < error D h ∧ ∀ i, h (S i).1 = (S i).2} ⊆
      ⋃ h ∈ Bad, {S : LabeledSample α β m | ∀ i, h (S i).1 = (S i).2} := fun S ⟨h, hH, hε, hS⟩ =>
    mem_iUnion₂.2 ⟨h, Finset.mem_filter.2 ⟨hH, hε⟩, hS⟩
  calc μ {S | ∃ h ∈ H, ε < error D h ∧ ∀ i, h (S i).1 = (S i).2}
      ≤ μ (⋃ h ∈ Bad, {S : LabeledSample α β m | ∀ i, h (S i).1 = (S i).2}) := measure_mono hsub
    _ ≤ ∑ h ∈ Bad, μ {S : LabeledSample α β m | ∀ i, h (S i).1 = (S i).2} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ Bad, (1 - ε) ^ m := by
        refine Finset.sum_le_sum fun h hh => ?_
        obtain ⟨hhH, hhε⟩ := Finset.mem_filter.1 hh
        rw [measure_pi_forall_apply_eq_eq_pow D (hH h hhH)]
        gcongr
    _ ≤ H.card * (1 - ε) ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact Finset.filter_subset _ _

/-- **Union bound for consistent learners of a finite class.** If `D` is realizable by the finite
class `H` and `A` is consistent with `H`, then the probability over `m` i.i.d. examples that the
output of `A` has true error greater than `ε` is at most `|H| (1 - ε) ^ m`. -/
theorem IsConsistent.measure_pi_lt_error_le_card_mul_pow {H : Finset (α → β)}
    (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) {m : ℕ} {A : Learner α β m}
    (hA : IsConsistent A (H : Set (α → β))) {D : Measure (α × β)} [IsProbabilityMeasure D]
    (hD : IsRealizableBy D (H : Set (α → β))) (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin m => D) {S | ε < error D (A S)} ≤ H.card * (1 - ε) ^ m := by
  have hsub : {S | ε < error D (A S)} ≤ᵐ[Measure.pi (fun _ : Fin m => D)]
      {S : LabeledSample α β m | ∃ h ∈ H, ε < error D h ∧ ∀ i, h (S i).1 = (S i).2} := by
    filter_upwards [hA.ae_mem_versionSpace hD] with S hS hlt
    obtain ⟨hAH, hAS⟩ := hS
    exact ⟨A S, Finset.mem_coe.1 hAH, hlt, hAS⟩
  exact (measure_mono_ae hsub).trans
    (measure_pi_exists_consistent_lt_error_le_card_mul_pow hH D ε)

/-- `n exp (-(ε m)) ≤ δ` once `log n + log (1 / δ) ≤ ε m`. -/
private theorem natCast_mul_exp_neg_le {n m : ℕ} {ε δ : ℝ} (hδ : 0 < δ)
    (hm : Real.log n + Real.log δ⁻¹ ≤ ε * m) : n * Real.exp (-(ε * m)) ≤ δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hδ.le
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_inv] at hm
  calc (n : ℝ) * Real.exp (-(ε * m)) = Real.exp (Real.log n + -(ε * m)) := by
        rw [Real.exp_add, Real.exp_log hn']
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 (by linarith)
    _ = δ := Real.exp_log hδ

/-- `(1 - ε) ^ m ≤ exp (-(ε m))` in `ℝ≥0∞`. -/
private theorem one_sub_ofReal_pow_le (ε : ℝ) (hε : 0 ≤ ε) (m : ℕ) :
    (1 - ENNReal.ofReal ε) ^ m ≤ ENNReal.ofReal (Real.exp (-(ε * m))) := by
  have h1 : 1 - ENNReal.ofReal ε ≤ ENNReal.ofReal (Real.exp (-ε)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hε]
    exact ENNReal.ofReal_le_ofReal (Real.one_sub_le_exp_neg ε)
  calc (1 - ENNReal.ofReal ε) ^ m ≤ ENNReal.ofReal (Real.exp (-ε)) ^ m := by gcongr
    _ = ENNReal.ofReal (Real.exp (-(ε * m))) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
        congr 2
        ring

/-- **The Occam sample size.** `n (1 - ε) ^ m ≤ δ` once `log n + log (1 / δ) ≤ ε m`. -/
theorem natCast_mul_one_sub_ofReal_pow_le {n m : ℕ} {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hm : Real.log n + Real.log δ⁻¹ ≤ ε * m) :
    (n : ℝ≥0∞) * (1 - ENNReal.ofReal ε) ^ m ≤ ENNReal.ofReal δ :=
  calc (n : ℝ≥0∞) * (1 - ENNReal.ofReal ε) ^ m
      ≤ ENNReal.ofReal n * ENNReal.ofReal (Real.exp (-(ε * m))) := by
        rw [ENNReal.ofReal_natCast]
        gcongr
        exact one_sub_ofReal_pow_le ε hε m
    _ = ENNReal.ofReal (n * Real.exp (-(ε * m))) := (ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (natCast_mul_exp_neg_le hδ hm)

/-- **Occam bound for finite classes** [ShalevShwartzBenDavid2014, Corollary 2.3]. If `D` is
realizable by the finite class `H`, `A` is consistent with `H`, and
`log |H| + log (1 / δ) ≤ ε m`, then the output of `A` on `m` i.i.d. examples has true error
greater than `ε` with probability at most `δ`. -/
theorem IsConsistent.measure_pi_lt_error_le_of_log_card_add_log_inv_le {H : Finset (α → β)}
    (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) {m : ℕ} {A : Learner α β m}
    (hA : IsConsistent A (H : Set (α → β))) {D : Measure (α × β)} [IsProbabilityMeasure D]
    (hD : IsRealizableBy D (H : Set (α → β))) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hm : Real.log H.card + Real.log δ⁻¹ ≤ ε * m) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ :=
  (hA.measure_pi_lt_error_le_card_mul_pow hH hD _).trans
    (natCast_mul_one_sub_ofReal_pow_le hε hδ hm)

/-- **Finite classes are PAC learnable in the realizable setting**
[ShalevShwartzBenDavid2014, Corollary 2.3]: a finite class `H` is `(ε, δ)`-PAC learnable
from `m` examples over the distributions realizable by `H` whenever
`log |H| + log (1 / δ) ≤ ε m`. If `H` is nonempty the learner is any consistent learner, which
exists by `exists_isConsistent`. If `H` is empty no distribution is realizable, and the
hypothesis forces `m ≥ 1` because `log 0 = 0 < log (1 / δ)`; any learner that returns the label of
its first example works. -/
theorem isPACLearnerFor_realizableDistributions_of_log_card_add_log_inv_le
    {H : Finset (α → β)} (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2})
    {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : Real.log H.card + Real.log (δ.val : ℝ)⁻¹ ≤ ε.val * m) :
    IsPACLearnerFor m ε δ (H : Set (α → β)) (realizableDistributions (H : Set (α → β))) := by
  rcases H.eq_empty_or_nonempty with rfl | hne
  · have hδ : 0 < Real.log (δ.val : ℝ)⁻¹ :=
      Real.log_pos ((one_lt_inv₀ (by exact_mod_cast δ.2.1)).2 (by exact_mod_cast δ.2.2))
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
      subst h
      simp only [Finset.card_empty, Nat.cast_zero, Real.log_zero, zero_add, mul_zero] at hm
      linarith
    simpa only [Finset.coe_empty] using
      isPACLearnerFor_realizableDistributions_empty (fun S _ => (S ⟨0, hm0⟩).2) ε δ
  obtain ⟨A, hA⟩ := exists_isConsistent (m := m) (C := (H : Set (α → β))) (by exact_mod_cast hne)
  refine ⟨A, fun D _ hD => ?_⟩
  have h := hA.measure_pi_lt_error_le_of_log_card_add_log_inv_le hH hD ε.val.coe_nonneg
    (by exact_mod_cast δ.2.1) hm
  rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add]
  exact h

/-- The realizable sample complexity of a finite class `H` is at most
`⌈(log |H| + log (1 / δ)) / ε⌉` [ShalevShwartzBenDavid2014, Corollary 2.3]. -/
theorem sampleComplexity_realizableDistributions_le_of_finite
    {H : Finset (α → β)} (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2})
    (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor (H : Set (α → β)) ε δ
        (realizableDistributions (H : Set (α → β))) ≤
      ⌈(Real.log H.card + Real.log (δ.val : ℝ)⁻¹) / ε.val⌉₊ := by
  refine Nat.sInf_le
    (isPACLearnerFor_realizableDistributions_of_log_card_add_log_inv_le hH ?_)
  have hε : (0 : ℝ) < ε.val := by exact_mod_cast ε.2.1
  rw [mul_comm, ← div_le_iff₀ hε]
  exact Nat.le_ceil _

end Cslib.MachineLearning.PACLearning
