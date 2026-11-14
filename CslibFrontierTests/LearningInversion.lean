/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.Inversion

/-!
# Tests: learning by inverting the labelling map

The two constant functions on one bit, keyed by their value, with the inverter that reads the key
off the label of the first example. This inverter never fails, so the key it returns has uniform
error above `1 / 2` with probability at most `2 (1 / 2) ^ 4 = 1 / 8` from four examples, and, in
the cruder Occam form, at most `1 / 2`, since `log 2 + log 2 ≤ 4 / 2`. The first bound also holds
for a uniformly random key.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.LearningInversion

open Cslib.MachineLearning.UniformLearning Cslib.MachineLearning.PACLearning Cslib.Probability
open scoped ENNReal

/-- The two constant functions on one bit, keyed by their value. -/
private def constFamily : Bool → (Fin 1 → Bool) → Bool := fun b _ => b

/-- Read the key off the label of the first example. -/
private noncomputable def firstLabel {m : ℕ} (S : LabeledSample (Fin 1 → Bool) Bool (m + 1)) :
    PMF Bool :=
  PMF.pure (S 0).2

/-- The first label is always a consistent key. -/
private theorem firstLabel_never_fails (m : ℕ) (K : Bool) :
    (labelInversion constFamily firstLabel K).toOuterMeasure
      {p : LabeledSample (Fin 1 → Bool) Bool (m + 1) × Bool |
        ∃ i, constFamily p.2 (p.1 i).1 ≠ (p.1 i).2} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  rintro ⟨S, K'⟩ hp ⟨i, hi⟩
  simp only [labelInversion, firstLabel, uniformExamples, PMF.mem_support_bind_iff,
    PMF.support_map, PMF.support_pure, Set.mem_image, Set.mem_singleton_iff] at hp
  obtain ⟨_, ⟨x, -, rfl⟩, _, rfl, hS⟩ := hp
  cases hS
  exact hi rfl

/-- `|Bool| (1 - 1 / 2) ^ 4 = 1 / 8`. -/
private theorem card_bool_mul_pow_four :
    (Fintype.card Bool : ℝ≥0∞) * (1 - ENNReal.ofReal (1 / 2)) ^ 4 ≤ 1 / 8 := by
  rw [Fintype.card_bool, one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
    ENNReal.one_sub_inv_two, Nat.cast_ofNat, pow_succ, mul_left_comm,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one, ← ENNReal.inv_pow]
  norm_num

/-- From four examples, the key read off the first label has error above `1 / 2` with probability
at most `1 / 8`. -/
example (K : Bool) :
    (labelInversion constFamily (firstLabel (m := 3)) K).toOuterMeasure
      {p | (1 / 2 : ℝ) < uniformError (constFamily K) (constFamily p.2)} ≤ 1 / 8 := by
  refine (labelInversion_lt_uniformError_le constFamily firstLabel K (by norm_num)).trans ?_
  rw [firstLabel_never_fails, zero_add]
  exact card_bool_mul_pow_four

/-- The Occam form: from four examples, error above `1 / 2` has probability at most `1 / 2`, since
`log 2 + log 2 ≤ 4 / 2`. -/
example (K : Bool) :
    (labelInversion constFamily (firstLabel (m := 3)) K).toOuterMeasure
      {p | (1 / 2 : ℝ) < uniformError (constFamily K) (constFamily p.2)} ≤
        ENNReal.ofReal (1 / 2) := by
  refine (labelInversion_lt_uniformError_le_of_log_card_add_log_inv_le constFamily firstLabel K
    (δ := 1 / 2) (by norm_num) (by norm_num) ?_).trans ?_
  · rw [Fintype.card_bool, one_div, inv_inv, Nat.cast_ofNat]
    have := Real.log_le_sub_one_of_pos (two_pos (α := ℝ))
    norm_num
    linarith
  · rw [firstLabel_never_fails, zero_add]

/-- For a uniformly random key, error above `1 / 2` from four examples has probability at most
`1 / 8`. -/
example :
    ((PMF.uniformOfFintype Bool).bind fun K =>
        (labelInversion constFamily (firstLabel (m := 3)) K).map fun p => (K, p)).toOuterMeasure
      {(K, _, K') : Bool × LabeledSample (Fin 1 → Bool) Bool 4 × Bool |
        (1 / 2 : ℝ) < uniformError (constFamily K) (constFamily K')} ≤ 1 / 8 := by
  refine (bind_labelInversion_lt_uniformError_le constFamily firstLabel _ (by norm_num)).trans ?_
  have h0 (K : Bool) : (labelInversion constFamily (firstLabel (m := 3)) K).toOuterMeasure
      ((fun p => (K, p)) ⁻¹' {(_, S, K') : Bool × LabeledSample (Fin 1 → Bool) Bool 4 × Bool |
        ∃ i, constFamily K' (S i).1 ≠ (S i).2}) = 0 :=
    firstLabel_never_fails 3 K
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply, h0, mul_zero, tsum_zero,
    zero_add]
  exact card_bool_mul_pow_four

end CslibFrontierTests.LearningInversion
