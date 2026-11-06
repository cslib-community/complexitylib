/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Linarith

/-!
# The ceiling of the fourth root

`Nat.ceilQuarter n` is `⌈n ^ (1/4)⌉`, the least `J` with `n ≤ J ^ 4`. It is positive for `n ≥ 1`,
at most `n`, and its square is at most `4 n`.

## Main definitions

* `Nat.ceilQuarter`: `⌈n ^ (1/4)⌉`.

## Main results

* `Nat.le_ceilQuarter_pow`, `Nat.ceilQuarter_pos`, `Nat.ceilQuarter_le_self`,
  `Nat.ceilQuarter_mul_self_le`: its bounds.
-/

public section

namespace Nat

/-- **`⌈n ^ (1/4)⌉`**, the least `J` with `n ≤ J ^ 4`. -/
@[expose] def ceilQuarter (n : ℕ) : ℕ :=
  Nat.find (⟨n, Nat.le_self_pow (by norm_num) n⟩ : ∃ J, n ≤ J ^ 4)

theorem le_ceilQuarter_pow (n : ℕ) : n ≤ ceilQuarter n ^ 4 :=
  Nat.find_spec (⟨n, Nat.le_self_pow (by norm_num) n⟩ : ∃ J, n ≤ J ^ 4)

theorem ceilQuarter_pos {n : ℕ} (hn : 1 ≤ n) : 0 < ceilQuarter n := by
  rcases Nat.eq_zero_or_pos (ceilQuarter n) with h0 | h
  · have := le_ceilQuarter_pow n
    rw [h0, zero_pow (by norm_num)] at this
    omega
  · exact h

theorem ceilQuarter_le_self (n : ℕ) : ceilQuarter n ≤ n :=
  Nat.find_min' _ (Nat.le_self_pow (by norm_num) n)

/-- `J² ≤ 4 n` for `J = ⌈n ^ (1/4)⌉` and `n ≥ 1`. -/
theorem ceilQuarter_mul_self_le {n : ℕ} (hn : 1 ≤ n) : ceilQuarter n * ceilQuarter n ≤ 4 * n := by
  set J := ceilQuarter n
  have hJ := ceilQuarter_pos hn
  have hmin : ¬ n ≤ (J - 1) ^ 4 :=
    Nat.find_min (⟨n, Nat.le_self_pow (by norm_num) n⟩ : ∃ J, n ≤ J ^ 4)
      (show J - 1 < ceilQuarter n by omega)
  have h2 : (J - 1) * (J - 1) ≤ (J - 1) ^ 4 := by
    rcases Nat.eq_zero_or_pos (J - 1) with h | h
    · simp [h]
    · calc (J - 1) * (J - 1) = (J - 1) ^ 2 := (sq _).symm
        _ ≤ (J - 1) ^ 4 := Nat.pow_le_pow_right h (by norm_num)
  rcases Nat.lt_or_ge J 2 with hJ2 | hJ2
  · have : J = 1 := by omega
    rw [this]
    omega
  · have : J ≤ 2 * (J - 1) := by omega
    nlinarith

end Nat
