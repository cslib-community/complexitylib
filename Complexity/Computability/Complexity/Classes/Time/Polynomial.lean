/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Time

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

/-- The shifted power `(n + 1) ^ k` is within a constant factor and summand of `n ^ k`. -/
private theorem succ_pow_le_two_pow_mul_add (k n : ℕ) :
    (n + 1) ^ k ≤ 2 ^ k * n ^ k + 2 ^ k := by
  rcases n with _ | n
  · simp only [zero_add, one_pow]
    exact (Nat.one_le_pow k 2 (by omega)).trans (Nat.le_add_left _ _)
  · calc (n + 1 + 1) ^ k ≤ (2 * (n + 1)) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * (n + 1) ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (n + 1) ^ k + 2 ^ k := Nat.le_add_right _ _

/-- Replacing the input length `n` by `n + 1` does not change a polynomial deterministic
time class, for any encoding and any natural degree. -/
theorem DTIME_succ_pow_eq {α : Type} (enc : α ↪ List Bool) (k : ℕ) :
    DTIME enc (fun n => (n + 1) ^ k) = DTIME enc (fun n => n ^ k) :=
  Set.Subset.antisymm (DTIME_mono_of_le_mul_add (C := 2 ^ k) (succ_pow_le_two_pow_mul_add k))
    (DTIME_mono fun n => Nat.pow_le_pow_left (Nat.le_succ n) k)

/-- Replacing the input length `n` by `n + 1` does not change a polynomial nondeterministic
time class, for any encoding and any natural degree. -/
theorem NTIME_succ_pow_eq {α : Type} (enc : α ↪ List Bool) (k : ℕ) :
    NTIME enc (fun n => (n + 1) ^ k) = NTIME enc (fun n => n ^ k) := by
  refine Set.Subset.antisymm ?_ (NTIME_mono fun n => Nat.pow_le_pow_left (Nat.le_succ n) k)
  rintro A ⟨c₁, c₂, k', State, hfinite, ntm, hA⟩
  refine ⟨c₁ * 2 ^ k, c₁ * 2 ^ k + c₂, k', State, hfinite, ntm, hA.mono fun a => ?_⟩
  have := Nat.mul_le_mul_left c₁ (succ_pow_le_two_pow_mul_add k (enc a).length)
  rw [Nat.mul_add, ← Nat.mul_assoc] at this
  beta_reduce
  omega

end Cslib.Complexity
