/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.SqrtLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

/-!
# The shifted scale `(y + 1) / √⌊log₂ (y + 2)⌋`

The scale `n / √⌊log₂ n⌋` of `Complexity.Foundations.Data.Nat.SqrtLog`, shifted so that it is
defined at every size: `A (y + 1) / √⌊log₂ (y + 2)⌋`. It is monotone up to constants along a
linear bound `y ≤ C x + C` (`Nat.mul_succ_div_sqrt_log_two_le`), so a time bound stated in a
derived size, such as the number of variables of a compiled formula or the number of gates of a
linear-size circuit, transfers to the size `x` it is linear in. The lemma sits in its own module
so that clients do not rebuild with the scale API.

## Main results

* `Nat.mul_succ_div_sqrt_log_two_le`: if `y ≤ C x + C`, then
  `A (y + 1) / √⌊log₂ (y + 2)⌋ ≤ A (8 C + 14) (x + 1) / √⌊log₂ (x + 2)⌋`.
-/

public section

namespace Nat

/-- **The shifted scale is monotone up to constants.** If `y ≤ C x + C`, then
`A (y + 1) / √⌊log₂ (y + 2)⌋ ≤ A (8 C + 14) (x + 1) / √⌊log₂ (x + 2)⌋`. -/
theorem mul_succ_div_sqrt_log_two_le {A C x y : ℕ} (h : y ≤ C * x + C) :
    A * (y + 1) / sqrt (log 2 (y + 2)) ≤
      A * (8 * C + 14) * (x + 1) / sqrt (log 2 (x + 2)) := by
  set G := (x + 2) / sqrt (log 2 (x + 2))
  have hG : 1 ≤ G := one_le_div_sqrt_log_two (by omega)
  have h3 : y + 2 ≤ (C + 1) * (x + 2) := by nlinarith
  have h4 := div_sqrt_log_two_le_of_le h3
  have h5 : (C + 1) * (x + 2) / sqrt (log 2 ((C + 1) * (x + 2))) ≤ (C + 1) * G + (C + 1) :=
    mul_div_sqrt_log_two_le (C + 1) (x + 2)
  have h2 := mul_div_le_mul_div_add A (y + 2) (sqrt (log 2 (y + 2)))
  have h1 : A * (y + 1) / sqrt (log 2 (y + 2)) ≤ A * (y + 2) / sqrt (log 2 (y + 2)) :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
  have hscale : (y + 2) / sqrt (log 2 (y + 2)) ≤ 2 * ((C + 1) * G) + 2 * C + 4 := by
    omega
  calc A * (y + 1) / sqrt (log 2 (y + 2))
      ≤ A * (2 * ((C + 1) * G) + 2 * C + 4) + A := by
        nlinarith [Nat.mul_le_mul_left A hscale]
    _ ≤ A * (4 * C + 7) * G := by nlinarith [Nat.mul_le_mul_left (A * (2 * C + 5)) hG]
    _ ≤ A * (4 * C + 7) * (x + 2) / sqrt (log 2 (x + 2)) := mul_div_le_mul_div_assoc _ _ _
    _ ≤ A * (8 * C + 14) * (x + 1) / sqrt (log 2 (x + 2)) :=
        Nat.div_le_div_right (by
          calc A * (4 * C + 7) * (x + 2) ≤ A * (4 * C + 7) * (2 * (x + 1)) :=
                Nat.mul_le_mul_left _ (by omega)
            _ = A * (8 * C + 14) * (x + 1) := by ring)

end Nat
