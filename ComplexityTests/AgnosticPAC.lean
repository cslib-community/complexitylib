/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.MachineLearning.PACLearning.AgnosticFiniteClass
import ComplexityTests.RealizablePAC

/-! Checks for agnostic PAC learning of finite classes: a noisy distribution that no class
realizes but under which the two constant hypotheses have optimal error `1 / 2`; a sample that is
exactly representative and samples that are not; and the agnostic Occam bound for the constants
with explicit parameters, together with a matching check that zero examples do not suffice. -/

namespace ComplexityTests.AgnosticPAC

open Cslib.MachineLearning.PACLearning MeasureTheory
open ComplexityTests.RealizablePAC (constants card_constants const_mem_constants half
  measurableSet_misclassified_constants not_isPACLearnerFor_constants_zero)
open scoped NNReal ENNReal

/-! ### A noisy distribution -/

/-- The point `false` labeled `true` or `false` with probability `1 / 2` each. -/
noncomputable def noisy : Measure (Bool × Bool) :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (false, true) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (false, false)

instance : IsProbabilityMeasure noisy := by
  constructor
  simp only [noisy, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- Every hypothesis errs with probability `1 / 2` under `noisy`. -/
theorem error_noisy (h : Bool → Bool) : error noisy h = 2⁻¹ := by
  cases hf : h false <;> simp [noisy, error, hf]

/-- `noisy` is realizable by no class, so the realizable-case theorems say nothing about it. -/
example (C : ConceptClass Bool Bool) : noisy ∉ realizableDistributions C := by
  rintro ⟨h, -, hh⟩
  rw [error_noisy] at hh
  exact absurd hh (by norm_num)

/-- The best error of the constants under `noisy` is `1 / 2`, so the agnostic guarantee is
nonvacuous: it promises error at most `1 / 2 + ε`, not `ε`. -/
theorem optimalError_noisy_constants :
    optimalError noisy (constants : Set (Bool → Bool)) = 2⁻¹ := by
  refine le_antisymm (iInf₂_le _ (const_mem_constants true) |>.trans_eq (error_noisy _)) ?_
  exact le_iInf₂ fun h _ => (error_noisy h).ge

/-! ### Representative samples -/

/-- The sample that sees both labels of `false` estimates the error of each constant exactly. -/
example : IsRepresentative noisy (constants : Set (Bool → Bool)) 0
    (![(false, true), (false, false)] : LabeledSample Bool Bool 2) := by
  intro h hh
  simp only [constants, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hh
  have hS (b : Bool) : empiricalMiscount (fun _ => b)
      (![(false, true), (false, false)] : LabeledSample Bool Bool 2) = 1 := by
    cases b <;> decide
  rcases hh with rfl | rfl <;>
  · rw [hS, error_noisy]
    norm_num

/-- A single example never estimates the error of a constant to within `1 / 4`: its empirical
error is `0` or `1`, while the true error is `1 / 2`. -/
example (S : LabeledSample Bool Bool 1) :
    ¬ IsRepresentative noisy (constants : Set (Bool → Bool)) (1 / 4) S := by
  intro hS
  have h := hS _ (const_mem_constants true)
  rw [error_noisy] at h
  have hle : empiricalMiscount (fun _ => true) S ≤ 1 :=
    (Finset.card_filter_le _ _).trans_eq (by simp)
  interval_cases hk : empiricalMiscount (fun _ => true) S <;>
    · rw [abs_le] at h
      norm_num at h

/-! ### The agnostic Occam bound -/

/-- Seventeen examples suffice to learn the constants agnostically to accuracy and confidence
`1 / 2`, because `2 log (2 · 2 / (1 / 2)) = 6 log 2 ≤ (1 / 2)² · 17`. -/
theorem isPACLearnerFor_constants_seventeen :
    IsPACLearnerFor 17 half half (constants : Set (Bool → Bool)) Set.univ := by
  refine isPACLearnerFor_univ_of_log_le measurableSet_misclassified_constants ?_
  simp only [card_constants, half, Nat.cast_ofNat, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  rw [show (2 * 2 / (1 / 2) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9]

/-- Zero examples do not suffice, already for the realizable distributions. -/
theorem not_isPACLearnerFor_constants_univ_zero :
    ¬ IsPACLearnerFor 0 half half (constants : Set (Bool → Bool)) Set.univ :=
  fun h => not_isPACLearnerFor_constants_zero (h.antitone_family (Set.subset_univ _))

/-- The agnostic sample complexity of the constants at `(1/2, 1/2)` lies in `[1, 17]`; the upper
bound is `⌈2 log 8 / (1 / 2)²⌉ = ⌈24 log 2⌉ = 17`. -/
example : 1 ≤ sampleComplexity IsPACLearnerFor (constants : Set (Bool → Bool)) half half
      Set.univ ∧
    sampleComplexity IsPACLearnerFor (constants : Set (Bool → Bool)) half half Set.univ ≤ 17 := by
  refine ⟨Nat.one_le_iff_ne_zero.2 fun h0 => not_isPACLearnerFor_constants_univ_zero ?_, ?_⟩
  · have hmem := Nat.sInf_mem (⟨17, isPACLearnerFor_constants_seventeen⟩ :
      {m | IsPACLearnerFor m half half (constants : Set (Bool → Bool)) Set.univ}.Nonempty)
    unfold sampleComplexity at h0
    rwa [h0] at hmem
  · refine (sampleComplexity_univ_le_of_finite measurableSet_misclassified_constants
      half half).trans ?_
    refine Nat.ceil_le.2 ?_
    simp only [card_constants, half, Nat.cast_ofNat, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat]
    rw [show (2 * 2 / (1 / 2) : ℝ) = 2 ^ 3 by norm_num, Real.log_pow,
      div_le_iff₀ (by norm_num)]
    push_cast
    linarith [Real.log_two_lt_d9]

/-- Agnostic PAC learnability of a finite class needs no inhabited hypothesis space: with an empty
label type there are no hypotheses at all, and the empty class is still learnable. -/
example : IsPACLearnable ((∅ : Finset (Bool → Empty)) : Set (Bool → Empty)) Set.univ :=
  isPACLearnable_univ_of_finite (by simp)

end ComplexityTests.AgnosticPAC
