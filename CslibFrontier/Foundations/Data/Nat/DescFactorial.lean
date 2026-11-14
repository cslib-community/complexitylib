/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Falling-factorial comparison bounds against powers

Elementary lower bounds on `A.descFactorial r` relative to `A ^ r`:

* `Nat.two_mul_pow_le_two_mul_descFactorial_add`: for every `A, r : ℕ`,
  `2 * A ^ r ≤ 2 * A.descFactorial r + r * (r - 1) * A ^ (r - 1)` (the exact combinatorial union
  bound for collisions of uniform maps `Fin r → Fin A`).
* `Nat.pow_le_two_mul_descFactorial`: whenever `2 * r ^ 2 ≤ A`, `A ^ r ≤ 2 * A.descFactorial r`.

## Main results

* `Nat.two_mul_pow_le_two_mul_descFactorial_add`
* `Nat.pow_le_two_mul_descFactorial`
-/

public section

namespace Nat

/-- Birthday deficit bound between `A ^ r` and the falling factorial `A.descFactorial r`:
for every `A, r : ℕ`, `2 * A ^ r ≤ 2 * A.descFactorial r + r * (r - 1) * A ^ (r - 1)`. -/
theorem two_mul_pow_le_two_mul_descFactorial_add (A : ℕ) :
    ∀ r : ℕ, 2 * A ^ r ≤ 2 * A.descFactorial r + r * (r - 1) * A ^ (r - 1)
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    induction m with
    | zero =>
      change 2 * A ^ 2 ≤ 2 * A.descFactorial 2 + 2 * 1 * A ^ 1
      rcases le_or_gt A 1 with hA | hA
      · interval_cases A <;> simp
      · rw [Nat.descFactorial_succ, Nat.descFactorial_one]
        zify [Nat.one_le_of_lt hA]
        nlinarith
    | succ m ih =>
      change 2 * A ^ (m + 3) ≤ 2 * A.descFactorial (m + 3) + (m + 3) * (m + 2) * A ^ (m + 2)
      change 2 * A ^ (m + 2) ≤ 2 * A.descFactorial (m + 2) + (m + 2) * (m + 1) * A ^ (m + 1) at ih
      rcases le_or_gt A (m + 2) with hA | hA
      · have h2A : 2 * A ≤ (m + 3) * (m + 2) := by nlinarith
        calc 2 * A ^ (m + 3)
            = (2 * A) * A ^ (m + 2) := by rw [pow_succ']; ring
          _ ≤ ((m + 3) * (m + 2)) * A ^ (m + 2) := Nat.mul_le_mul_right _ h2A
          _ ≤ 2 * A.descFactorial (m + 3) + (m + 3) * (m + 2) * A ^ (m + 2) :=
              Nat.le_add_left _ _
      · have hA_mul : A * A.descFactorial (m + 2) =
            A.descFactorial (m + 3) + (m + 2) * A.descFactorial (m + 2) := by
          calc A * A.descFactorial (m + 2)
              = (A - (m + 2) + (m + 2)) * A.descFactorial (m + 2) :=
                congrArg (· * _) (Nat.sub_add_cancel hA.le).symm
            _ = (A - (m + 2)) * A.descFactorial (m + 2) + (m + 2) * A.descFactorial (m + 2) :=
                Nat.add_mul _ _ _
            _ = A.descFactorial (m + 3) + (m + 2) * A.descFactorial (m + 2) := by
                rw [← Nat.descFactorial_succ A (m + 2)]
        have hdesc_le : A.descFactorial (m + 2) ≤ A ^ (m + 2) := Nat.descFactorial_le_pow A (m + 2)
        calc 2 * A ^ (m + 3)
            = (2 * A ^ (m + 2)) * A := by ring
          _ ≤ (2 * A.descFactorial (m + 2) + (m + 2) * (m + 1) * A ^ (m + 1)) * A :=
              Nat.mul_le_mul_right A ih
          _ = 2 * (A * A.descFactorial (m + 2)) + (m + 2) * (m + 1) * A ^ (m + 2) := by ring
          _ = 2 * A.descFactorial (m + 3) +
                (2 * (m + 2) * A.descFactorial (m + 2) + (m + 2) * (m + 1) * A ^ (m + 2)) := by
              rw [hA_mul]; ring
          _ ≤ 2 * A.descFactorial (m + 3) +
                (2 * (m + 2) * A ^ (m + 2) + (m + 2) * (m + 1) * A ^ (m + 2)) :=
              Nat.add_le_add_left
                (Nat.add_le_add_right (Nat.mul_le_mul_left _ hdesc_le) _) _
          _ = 2 * A.descFactorial (m + 3) + (m + 3) * (m + 2) * A ^ (m + 2) := by ring

/-- Falling-factorial lower bound `A ^ r ≤ 2 * A.descFactorial r` whenever `2 * r ^ 2 ≤ A`. -/
theorem pow_le_two_mul_descFactorial {A r : ℕ} (h : 2 * r ^ 2 ≤ A) :
    A ^ r ≤ 2 * A.descFactorial r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have htop := two_mul_pow_le_two_mul_descFactorial_add A r
  have h2r : r * (r - 1) * A ^ (r - 1) ≤ A ^ r := by
    have hrr : 2 * (r * (r - 1)) ≤ 2 * r ^ 2 := by
      have : r * (r - 1) ≤ r * r := Nat.mul_le_mul_left r (Nat.sub_le r 1)
      nlinarith
    have hr_le : r * (r - 1) ≤ A := by omega
    calc r * (r - 1) * A ^ (r - 1)
        ≤ A * A ^ (r - 1) := Nat.mul_le_mul_right _ hr_le
      _ = A ^ (r - 1 + 1) := by rw [pow_succ']
      _ = A ^ r := congrArg (A ^ ·) (Nat.sub_add_cancel hr)
  omega

end Nat
