/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.TrinomialParameters

open Cslib Cslib.TrinomialArithmetic Turing.MultiTapeTM

-- The minimal parameter changes exactly beyond degrees 2 and 6.
example : Probability.trinomialStepAux 0 = 0 := by
  rw [Probability.trinomialStepAux_eq_findGreatest]
  decide
example : Probability.trinomialStepAux 2 = 0 := by
  rw [Probability.trinomialStepAux_eq_findGreatest]
  decide
example : Probability.trinomialStepAux 3 = 1 := by
  rw [Probability.trinomialStepAux_eq_findGreatest]
  decide
example : Probability.trinomialStepAux 6 = 1 := by
  rw [Probability.trinomialStepAux_eq_findGreatest]
  decide
example : Probability.trinomialStepAux 7 = 2 := by
  rw [Probability.trinomialStepAux_eq_findGreatest]
  decide

-- A binary universe crossing a power of two changes the selected degree.
example : Probability.trinomialStep 64 1 = 1 := by
  unfold Probability.trinomialStep Probability.trinomialTargetBits
  rw [show Nat.clog 2 (max 64 2) = 6 by decide]
  norm_num [Probability.trinomialStepAux_eq_findGreatest]
example : Probability.trinomialStep 65 1 = 2 := by
  unfold Probability.trinomialStep Probability.trinomialTargetBits
  rw [show Nat.clog 2 (max 65 2) = 7 by decide]
  norm_num [Probability.trinomialStepAux_eq_findGreatest]

example : ComputableInPolyTime runSelected encSelectedInput encNat :=
  computableInPolyTime_runSelected

-- The same uniform evaluator handles the actual dependent seed type for every universe.
example (U bits : ℕ) (c : Fin 4 → Fin (2 ^ Probability.trinomialDeg U bits)) (u : Fin U) :
    runSelected ⟨U, bits, (c 0).val, (c 1).val, (c 2).val, (c 3).val, u.val⟩ =
      (Probability.trinomialPolyHash (Probability.trinomialStep U bits) 4 U bits c u).val :=
  runSelected_eq U bits c u

-- The binary universe may require one more bit than the field degree at U = 2^degree.
example : (encSelectedInput ⟨64, 0, 63, 63, 63, 63, 63⟩).length = 74 := by
  decide

example : (encSelectedInput ⟨64, 0, 63, 63, 63, 63, 63⟩).length ≤
    39 * Probability.trinomialTargetBits 64 0 + 8 := by
  have hdeg : Probability.trinomialDeg 64 0 = 6 := by
    unfold Probability.trinomialDeg Probability.trinomialStep Probability.trinomialTargetBits
    rw [show Nat.clog 2 (max 64 2) = 6 by decide]
    norm_num [Probability.trinomialStepAux_eq_findGreatest]
  exact length_encSelectedInput_le 64 0 (fun _ => ⟨63, by rw [hdeg]; decide⟩)
    ⟨63, by decide⟩
