/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.UniformConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Agnostic PAC learning of finite classes

Every finite class `H` of hypotheses `α → β` is agnostically PAC learnable for the 0-1 loss by
empirical risk minimization [ShalevShwartzBenDavid2014, Corollary 4.6, stated there for any loss
with values in `[0, 1]`]. Under *every* distribution `D` on
`α × β`, realizable or not, an ERM learner on

`m ≥ 2 log (2 |H| / δ) / ε²`

i.i.d. examples outputs a hypothesis whose error is at most `optimalError D H + ε` with probability
at least `1 - δ`. This is the upstream `IsPACLearnerFor` over the family `Set.univ` of all
distributions: its success criterion is already measured against the optimal error of the class.
The proof combines uniform convergence for finite classes with Lemma 4.2 of the source
(`UniformConvergence.lean`).

Each hypothesis needs a measurable misclassification set; `measurableSet_misclassified` supplies
this for measurable hypotheses with `Bool` labels. The learners are semantic maps: no running time
is claimed, and finding an empirical risk minimizer can be computationally hard.

## Main results

- `IsERM.measure_pi_lt_error_le`: the agnostic tail bound `|H| · 2 exp (-m ε² / 2)` for ERM.
- `IsERM.measure_pi_lt_error_le_of_log_le`: failure probability at most `δ` once
  `2 log (2 |H| / δ) ≤ ε² m`.
- `isPACLearnerFor_univ_of_log_le`: the corresponding `IsPACLearnerFor` over all distributions.
- `sampleComplexity_univ_le_of_finite`: the agnostic sample complexity of `H` is at most
  `⌈2 log (2 |H| / δ) / ε²⌉`.
- `isPACLearnable_univ_of_finite`: every finite class is agnostically PAC learnable.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

section ERM

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β]

/-- **Agnostic tail bound for ERM on a finite class**: under every distribution `D`, an empirical
risk minimizer for `H` misses `optimalError D H + ε` with probability at most
`|H| · 2 exp (-m ε² / 2)`. -/
theorem IsERM.measure_pi_lt_error_le (D : Measure (α × β)) [IsProbabilityMeasure D]
    {H : Finset (α → β)} (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) {m : ℕ}
    {A : Learner α β m} (hA : IsERM A (H : Set (α → β))) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D)
        {S | optimalError D (H : Set (α → β)) + ENNReal.ofReal ε < error D (A S)} ≤
      H.card * ENNReal.ofReal (2 * Real.exp (-m * ε ^ 2 / 2)) := by
  refine (measure_mono fun S hS => ?_).trans
    ((measure_pi_not_isRepresentative_le D hH m (ε := ε / 2) (by positivity)).trans_eq ?_)
  · exact fun hrep => (not_le.2 hS) (hrep.error_le_optimalError_add hA)
  · rw [show -2 * (m : ℝ) * (ε / 2) ^ 2 = -m * ε ^ 2 / 2 by ring]

/-- **Finite classes are agnostically PAC learnable by ERM** for the 0-1 loss
[ShalevShwartzBenDavid2014, Corollary 4.6]: under every distribution `D`, if
`m ≥ 2 log (2 |H| / δ) / ε²` then an empirical risk minimizer for `H` misses
`optimalError D H + ε` with probability at most `δ`. -/
theorem IsERM.measure_pi_lt_error_le_of_log_le (D : Measure (α × β)) [IsProbabilityMeasure D]
    {H : Finset (α → β)} (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) {m : ℕ}
    {A : Learner α β m} (hA : IsERM A (H : Set (α → β))) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hm : 2 * Real.log (2 * H.card / δ) ≤ ε ^ 2 * m) :
    Measure.pi (fun _ : Fin m => D)
        {S | optimalError D (H : Set (α → β)) + ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ := by
  refine (hA.measure_pi_lt_error_le D hH hε).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases Nat.eq_zero_or_pos H.card with h0 | hn
  · rw [h0, Nat.cast_zero, zero_mul]
    exact hδ.le
  have hn' : (0 : ℝ) < 2 * H.card := by positivity
  rw [Real.log_div hn'.ne' hδ.ne'] at hm
  calc (H.card : ℝ) * (2 * Real.exp (-m * ε ^ 2 / 2)) =
        Real.exp (Real.log (2 * H.card) + -(ε ^ 2 * m / 2)) := by
        rw [Real.exp_add, Real.exp_log hn', show -(ε ^ 2 * m / 2) = -m * ε ^ 2 / 2 by ring]
        ring
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 (by linarith)
    _ = δ := Real.exp_log hδ

end ERM

section PAC

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Agnostic PAC learning of finite classes** for the 0-1 loss [ShalevShwartzBenDavid2014,
Corollary 4.6]: a finite class `H` is `(ε, δ)`-PAC learnable over all distributions from
`m ≥ 2 log (2 |H| / δ) / ε²` examples. If `H` is nonempty the learner is any empirical risk
minimizer. If `H` is empty the optimal error is `⊤` and any learner works. The instance
`Nonempty (α → β)` is needed in that case: the hypothesis on `m` then holds at `m = 0`, and there
is no learner from zero examples when `α → β` is empty. -/
theorem isPACLearnerFor_univ_of_log_le [Nonempty (α → β)] {H : Finset (α → β)}
    (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : 2 * Real.log (2 * H.card / (δ.val : ℝ)) ≤ (ε.val : ℝ) ^ 2 * m) :
    IsPACLearnerFor m ε δ (H : Set (α → β)) Set.univ := by
  classical
  rcases H.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => Classical.arbitrary _, fun D _ _ => ?_⟩
    simp [optimalError]
  obtain ⟨A, hA⟩ := exists_isERM (m := m) (C := (H : Set (α → β))) (by exact_mod_cast hne)
  refine ⟨A, fun D _ _ => ?_⟩
  have h := hA.measure_pi_lt_error_le_of_log_le D hH ε.val.coe_nonneg
    (by exact_mod_cast δ.2.1) hm
  rwa [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h

/-- `2 log (2 n / δ) ≤ ε² ⌈2 log (2 n / δ) / ε²⌉`. -/
private theorem log_le_ceil {n : ℕ} (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    2 * Real.log (2 * n / (δ.val : ℝ)) ≤
      (ε.val : ℝ) ^ 2 * ⌈2 * Real.log (2 * n / (δ.val : ℝ)) / (ε.val : ℝ) ^ 2⌉₊ := by
  have hε : (0 : ℝ) < (ε.val : ℝ) ^ 2 := by
    have : (0 : ℝ) < ε.val := by exact_mod_cast ε.2.1
    positivity
  have := Nat.le_ceil (2 * Real.log (2 * n / (δ.val : ℝ)) / (ε.val : ℝ) ^ 2)
  rw [div_le_iff₀ hε] at this
  linarith

/-- The agnostic sample complexity of a finite class `H` for the 0-1 loss is at most
`⌈2 log (2 |H| / δ) / ε²⌉` [ShalevShwartzBenDavid2014, Corollary 4.6]. -/
theorem sampleComplexity_univ_le_of_finite [Nonempty (α → β)] {H : Finset (α → β)}
    (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor (H : Set (α → β)) ε δ Set.univ ≤
      ⌈2 * Real.log (2 * H.card / (δ.val : ℝ)) / (ε.val : ℝ) ^ 2⌉₊ :=
  Nat.sInf_le (isPACLearnerFor_univ_of_log_le hH (log_le_ceil ε δ))

/-- **Every finite class is agnostically PAC learnable** for the 0-1 loss
[ShalevShwartzBenDavid2014, Corollary 4.6]. No instance `Nonempty (α → β)` is needed here: for
the empty class one example suffices, and the learner returns its label. -/
theorem isPACLearnable_univ_of_finite {H : Finset (α → β)}
    (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) :
    IsPACLearnable (H : Set (α → β)) Set.univ := fun ε δ => by
  rcases H.eq_empty_or_nonempty with rfl | ⟨h, -⟩
  · exact ⟨1, fun S _ => (S 0).2, fun D _ _ => by simp [optimalError]⟩
  · have : Nonempty (α → β) := ⟨h⟩
    exact ⟨_, isPACLearnerFor_univ_of_log_le hH (log_le_ceil ε δ)⟩

end PAC

end Cslib.MachineLearning.PACLearning
