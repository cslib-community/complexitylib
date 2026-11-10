/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, multiset coefficients)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ratios of multiset coefficients

The number `n.multichoose k` of multisets of size `k` in `n` elements satisfies
`n.multichoose (k + 1) * (k + 1) = n.multichoose k * (n + k)`. Iterating this recurrence
compares the coefficients at two sizes with a power of one ratio. These are the successive
ratio bounds for the dimensions of spaces of homogeneous polynomials in
[OpenAI, §3][OpenAI2026DepthFive].

## Main results

* `Nat.multichoose_succ_mul`: the recurrence in the size.
* `Nat.multichoose_succ_sub_mul_pow_le`: lowering the size by `i` multiplies the coefficient
  by at most `(a / (a + n)) ^ i`.
* `Nat.multichoose_add_mul_pow_le`: raising the size by `j` multiplies the coefficient by at
  most `((b + n) / b) ^ j`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §3 (unrefereed preprint)
-/

public section

namespace Nat

/-- The recurrence of multiset coefficients in the size of the multiset. -/
theorem multichoose_succ_mul (n k : ℕ) :
    n.multichoose (k + 1) * (k + 1) = n.multichoose k * (n + k) := by
  cases n with
  | zero => cases k <;> simp
  | succ n =>
    rw [multichoose_eq, multichoose_eq, show n + 1 + (k + 1) - 1 = n + k + 1 by lia,
      show n + 1 + k - 1 = n + k by lia, ← add_one_mul_choose_eq]
    ring

/-- Lowering the size from `a` to `a - i` multiplies a multiset coefficient in `n + 1` elements
by at most `(a / (a + n)) ^ i`. -/
theorem multichoose_succ_sub_mul_pow_le (n : ℕ) {a i : ℕ} (h : i ≤ a) :
    (n + 1).multichoose (a - i) * (a + n) ^ i ≤ (n + 1).multichoose a * a ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨c, rfl⟩ : ∃ c, a = c + (i + 1) := ⟨a - (i + 1), by lia⟩
    have ih := ih (by lia)
    rw [show c + (i + 1) - i = c + 1 by lia] at ih
    rw [show c + (i + 1) - (i + 1) = c by lia]
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < n + 1 + c by lia)
    calc (n + 1).multichoose c * (c + (i + 1) + n) ^ (i + 1) * (n + 1 + c)
        = (n + 1).multichoose c * (n + 1 + c) * (c + (i + 1) + n) ^ (i + 1) := by ring
      _ = (n + 1).multichoose (c + 1) * (c + (i + 1) + n) ^ i *
            ((c + 1) * (c + (i + 1) + n)) := by rw [← multichoose_succ_mul]; ring
      _ ≤ (n + 1).multichoose (c + (i + 1)) * (c + (i + 1)) ^ i *
            ((c + (i + 1)) * (n + 1 + c)) := Nat.mul_le_mul ih (by nlinarith [Nat.zero_le (i * n)])
      _ = (n + 1).multichoose (c + (i + 1)) * (c + (i + 1)) ^ (i + 1) * (n + 1 + c) := by ring

/-- Raising the size from `b` to `b + j` multiplies a multiset coefficient in `n` elements by at
most `((b + n) / b) ^ j`. -/
theorem multichoose_add_mul_pow_le (n b j : ℕ) :
    n.multichoose (b + j) * b ^ j ≤ n.multichoose b * (b + n) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < b + j + 1 by lia)
    calc n.multichoose (b + (j + 1)) * b ^ (j + 1) * (b + j + 1)
        = n.multichoose (b + j + 1) * (b + j + 1) * b ^ (j + 1) := by ring_nf
      _ = n.multichoose (b + j) * b ^ j * (b * (n + (b + j))) := by
        rw [multichoose_succ_mul]; ring
      _ ≤ n.multichoose b * (b + n) ^ j * ((b + n) * (b + j + 1)) :=
        Nat.mul_le_mul ih (by nlinarith [Nat.zero_le (n * j), Nat.zero_le n, Nat.zero_le b])
      _ = n.multichoose b * (b + n) ^ (j + 1) * (b + j + 1) := by ring

end Nat
