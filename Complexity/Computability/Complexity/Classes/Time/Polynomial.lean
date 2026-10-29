/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time

/-!
# Polynomial deterministic time bounds

Polynomial time bounds are often written with `n + 1` to avoid exceptional arithmetic at the
empty input. The additive and multiplicative constants in `DTIME` make this convention equivalent
to the usual `n ^ k`, including degree zero.

## Main results

* `Cslib.Complexity.DTIME_succ_pow_eq`: `DTIME ((n + 1) ^ k) = DTIME (n ^ k)`.
-/

public section

namespace Cslib.Complexity

/-- Replacing the input length `n` by `n + 1` does not change a polynomial deterministic
time class, for any encoding and any natural degree. -/
theorem DTIME_succ_pow_eq {α : Type} (enc : α ↪ List Bool) (k : ℕ) :
    DTIME enc (fun n => (n + 1) ^ k) = DTIME enc (fun n => n ^ k) := by
  apply Set.Subset.antisymm
  · apply DTIME_mono_of_le_mul_add (C := 2 ^ k)
    intro n
    rcases n with _ | n
    · simp only [zero_add, one_pow]
      exact (Nat.one_le_pow k 2 (by omega)).trans (Nat.le_add_left _ _)
    · calc (n + 1 + 1) ^ k ≤ (2 * (n + 1)) ^ k := Nat.pow_le_pow_left (by omega) k
        _ = 2 ^ k * (n + 1) ^ k := mul_pow _ _ _
        _ ≤ 2 ^ k * (n + 1) ^ k + 2 ^ k := Nat.le_add_right _ _
  · exact DTIME_mono fun n => Nat.pow_le_pow_left (Nat.le_succ n) k

end Cslib.Complexity
