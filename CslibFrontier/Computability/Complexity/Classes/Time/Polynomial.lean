/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# Polynomial time bounds

Polynomial time bounds are often written with `n + 1` to avoid exceptional arithmetic at the
empty input. The additive and multiplicative constants in `DTIME` and `NTIME` make this convention
equivalent to the usual `n ^ k`, including degree zero.

## Main results

* `Cslib.Complexity.DTIME_succ_pow_eq`: `DTIME ((n + 1) ^ k) = DTIME (n ^ k)`.
* `Cslib.Complexity.NTIME_succ_pow_eq`: `NTIME ((n + 1) ^ k) = NTIME (n ^ k)`.
-/

public section

namespace Cslib.Complexity

/-- Replacing the input length `n` by `n + 1` does not change a polynomial deterministic
time class, for any encoding and any natural degree. -/
theorem DTIME_succ_pow_eq {α : Type} (enc : α ↪ List Bool) (k : ℕ) :
    DTIME enc (fun n => (n + 1) ^ k) = DTIME enc (fun n => n ^ k) :=
  Set.Subset.antisymm (DTIME_mono_of_le_mul_add (C := 2 ^ k) (Nat.add_one_pow_le_two_pow_mul_add k))
    (DTIME_mono fun n => Nat.pow_le_pow_left (Nat.le_succ n) k)

/-- Replacing the input length `n` by `n + 1` does not change a polynomial nondeterministic
time class, for any encoding and any natural degree. -/
theorem NTIME_succ_pow_eq {α : Type} (enc : α ↪ List Bool) (k : ℕ) :
    NTIME enc (fun n => (n + 1) ^ k) = NTIME enc (fun n => n ^ k) :=
  Set.Subset.antisymm (NTIME_mono_of_le_mul_add (C := 2 ^ k) (Nat.add_one_pow_le_two_pow_mul_add k))
    (NTIME_mono fun n => Nat.pow_le_pow_left (Nat.le_succ n) k)

end Cslib.Complexity
