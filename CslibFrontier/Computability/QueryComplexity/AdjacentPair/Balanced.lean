/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Fin.BalancedBlocks
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Balanced square-root block sizes

The partition used in [AroraBarak07], Chapter 11 Exercise 2, has `Nat.sqrt n` contiguous blocks
of size approximately `sqrt n`. The quotient/remainder split `Fin.balancedBlockSize` covers every
input length, not just squares. For `n ≥ 4` every block has at least `Nat.sqrt n ≥ 2` and at most
`3 * Nat.sqrt n` coordinates.

## Main definitions

* `Cslib.BitString.sqrtBlockSizes`: the block sizes of the balanced `Nat.sqrt n`-block split.

## Main results

* `Cslib.BitString.sum_sqrtBlockSizes`: the blocks cover all `n` coordinates, for every `n`.
* `Cslib.BitString.sqrt_le_sqrtBlockSizes`: every block has at least `Nat.sqrt n` coordinates.
* `Cslib.BitString.sqrtBlockSizes_le`: every block has at most `3 * Nat.sqrt n` coordinates.
-/

public section

namespace Cslib.BitString

/-- The sizes of the `Nat.sqrt n` balanced contiguous blocks of `n` coordinates: with
`k = Nat.sqrt n`, `q = n / k` and `r = n % k`, block `i` has size `q + [i < r]`. -/
@[expose] def sqrtBlockSizes (n : ℕ) : Fin (Nat.sqrt n) → ℕ :=
  Fin.balancedBlockSize n (Nat.sqrt n)

/-- The square-root blocks cover every coordinate. For `n = 0` there are no blocks. -/
theorem sum_sqrtBlockSizes (n : ℕ) : ∑ i, sqrtBlockSizes n i = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Fin.sum_balancedBlockSize n (Nat.sqrt_pos.mpr hn)

/-- Each square-root block has at least `Nat.sqrt n` coordinates. -/
theorem sqrt_le_sqrtBlockSizes (n : ℕ) (i : Fin (Nat.sqrt n)) :
    Nat.sqrt n ≤ sqrtBlockSizes n i := by
  have hk : 0 < Nat.sqrt n := Fin.pos i
  have hq : Nat.sqrt n ≤ n / Nat.sqrt n :=
    (Nat.le_div_iff_mul_le hk).mpr (Nat.sqrt_le n)
  exact hq.trans (Fin.div_le_balancedBlockSize _ _ _)

/-- For `n ≥ 4` each square-root block has room for an adjacent pair. -/
theorem two_le_sqrtBlockSizes {n : ℕ} (hn : 4 ≤ n) (i : Fin (Nat.sqrt n)) :
    2 ≤ sqrtBlockSizes n i :=
  (Nat.le_sqrt.mpr hn).trans (sqrt_le_sqrtBlockSizes n i)

/-- Each square-root block has at most three times as many coordinates as there are blocks. -/
theorem sqrtBlockSizes_le (n : ℕ) (i : Fin (Nat.sqrt n)) :
    sqrtBlockSizes n i ≤ 3 * Nat.sqrt n := by
  unfold sqrtBlockSizes Fin.balancedBlockSize
  have hk : 0 < Nat.sqrt n := Fin.pos i
  have hs : n < Nat.sqrt n * (Nat.sqrt n + 2) + 1 := by
    have := Nat.lt_succ_sqrt n
    simp only [Nat.succ_eq_add_one] at this
    nlinarith
  have hdm := Nat.div_add_mod n (Nat.sqrt n)
  split_ifs with hi
  · have hq : n / Nat.sqrt n < Nat.sqrt n + 2 :=
      Nat.lt_of_mul_lt_mul_left (a := Nat.sqrt n) (by omega)
    omega
  · have hq : n / Nat.sqrt n < Nat.sqrt n + 3 :=
      Nat.lt_of_mul_lt_mul_left (a := Nat.sqrt n) (by
        have : Nat.sqrt n * (Nat.sqrt n + 3) = Nat.sqrt n * (Nat.sqrt n + 2) + Nat.sqrt n := by
          ring
        omega)
    omega

end Cslib.BitString
