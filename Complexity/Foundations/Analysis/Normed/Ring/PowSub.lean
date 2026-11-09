/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Powers of contractions in a seminormed ring

If `‖a‖ ≤ 1` and `‖b‖ ≤ 1` in a seminormed ring, then `‖a ^ m - b ^ m‖ ≤ m ‖a - b‖`. The ring need
not be commutative and `‖1‖` may exceed `1`, so `a` and `b` may be matrices under an operator norm.
Mathlib has the commutative scalar bound `abs_pow_sub_pow_le` and telescoping identities such as
`Commute.geom_sum₂_mul`, but no such bound for noncommuting elements.

## Main results

* `norm_pow_sub_pow_le_of_norm_le_one`: `‖a ^ m - b ^ m‖ ≤ m ‖a - b‖` for `‖a‖, ‖b‖ ≤ 1`.
-/

public section

/-- **Powers of contractions.** In a seminormed ring, `‖a ^ m - b ^ m‖ ≤ m ‖a - b‖` when
`‖a‖ ≤ 1` and `‖b‖ ≤ 1`. The proof telescopes `a ^ (m + 1) - b ^ (m + 1) =
a (a ^ m - b ^ m) + (a - b) b ^ m`; commutativity is not needed. -/
theorem norm_pow_sub_pow_le_of_norm_le_one {R : Type*} [SeminormedRing R] {a b : R}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (m : ℕ) : ‖a ^ m - b ^ m‖ ≤ m * ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hbm : ‖b ^ m‖ ≤ 1 := (norm_pow_le' b hm).trans (pow_le_one₀ (norm_nonneg _) hb)
    have key : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      rw [pow_succ', pow_succ', mul_sub, sub_mul]
      abel
    rw [key]
    calc ‖a * (a ^ m - b ^ m) + (a - b) * b ^ m‖
        ≤ ‖a‖ * ‖a ^ m - b ^ m‖ + ‖a - b‖ * ‖b ^ m‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * (m * ‖a - b‖) + ‖a - b‖ * 1 := by gcongr
      _ = (m + 1 : ℕ) * ‖a - b‖ := by
        push_cast
        ring
