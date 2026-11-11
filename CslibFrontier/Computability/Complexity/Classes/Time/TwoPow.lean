/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time

/-!
# Exponential time bounds in a space bound

The simulations of space-bounded nondeterministic and alternating machines by deterministic ones
run within time `2 ^ (c * (log₂ n + S n + 1))`, where `S n = c₁ * s n + c₂` is the space bound of
the simulated machine. These lemmas put such a bound into the shape `2 ^ O(log₂ n + s n)`, and into
`2 ^ O(s n)` when `log₂ n ≤ s n`.

## Main results

* `Cslib.Complexity.DTIME_two_pow_log2_add_mul_add_subset`: the constants of the space bound move
  into the exponent's factor.
* `Cslib.Complexity.DTIME_two_pow_log2_add_subset`: above logarithmic space, the logarithm is
  absorbed.
* `Cslib.Complexity.DTIME_two_pow_mul_log2_succ_subset`: in logarithmic space, the bound is
  polynomial.
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- **The constants of a space bound move into the exponent's factor**: the class
`DTIME (2 ^ (c * (log₂ n + (c₁ * s n + c₂) + 1)))` is within
`DTIME (2 ^ (c * (c₁ + c₂ + 1) * (log₂ n + s n + 1)))`. -/
theorem DTIME_two_pow_log2_add_mul_add_subset (c c₁ c₂ : ℕ) (s : ℕ → ℕ) :
    DTIME enc (fun n => 2 ^ (c * (Nat.log2 n + (c₁ * s n + c₂) + 1))) ⊆
      DTIME enc fun n => 2 ^ (c * (c₁ + c₂ + 1) * (Nat.log2 n + s n + 1)) := by
  refine DTIME_mono fun n => Nat.pow_le_pow_right (by omega) ?_
  rw [Nat.mul_assoc]
  refine Nat.mul_le_mul_left c ?_
  nlinarith

/-- **Above logarithmic space, the logarithm is absorbed**: when `log₂ n ≤ s n`,
`DTIME (2 ^ (c * (log₂ n + s n + 1))) ⊆ DTIME (2 ^ (2 * c * s n))`. -/
theorem DTIME_two_pow_log2_add_subset {c : ℕ} {s : ℕ → ℕ} (hs : ∀ n, Nat.log2 n ≤ s n) :
    DTIME enc (fun n => 2 ^ (c * (Nat.log2 n + s n + 1))) ⊆
      DTIME enc fun n => 2 ^ (2 * c * s n) := by
  refine DTIME_mono_of_le_mul_add (C := 2 ^ c) fun n => ?_
  calc 2 ^ (c * (Nat.log2 n + s n + 1))
      ≤ 2 ^ (2 * c * s n + c) := Nat.pow_le_pow_right (by omega) (by nlinarith [hs n])
    _ = 2 ^ c * 2 ^ (2 * c * s n) := by rw [pow_add, Nat.mul_comm]
    _ ≤ 2 ^ c * 2 ^ (2 * c * s n) + 2 ^ c := Nat.le_add_right _ _

/-- **In logarithmic space, the bound is polynomial**:
`DTIME (2 ^ (d * (log₂ n + 1))) ⊆ DTIME (n ^ d)`, since `2 ^ log₂ n ≤ n`. -/
theorem DTIME_two_pow_mul_log2_succ_subset (d : ℕ) :
    DTIME enc (fun n => 2 ^ (d * (Nat.log2 n + 1))) ⊆ DTIME enc fun n => n ^ d := by
  refine DTIME_mono_of_le_mul_add (C := 2 ^ d) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  calc 2 ^ (d * (Nat.log2 n + 1))
      = 2 ^ d * (2 ^ Nat.log2 n) ^ d := by ring
    _ ≤ 2 ^ d * n ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.log2_self_le hn.ne') d)
    _ ≤ 2 ^ d * n ^ d + 2 ^ d := Nat.le_add_right _ _

end Cslib.Complexity
