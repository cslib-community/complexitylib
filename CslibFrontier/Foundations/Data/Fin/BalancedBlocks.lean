/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Balanced block sizes

Splitting `n` items into `k` contiguous blocks as evenly as possible gives the first `n % k`
blocks size `n / k + 1` and the others size `n / k`. Together with Mathlib's
`finSigmaFinEquiv`, these sizes lay out `Fin n` as consecutive blocks for every `n` and every
positive `k`, not only when `k` divides `n`.

## Main definitions

* `Fin.balancedBlockSize`: the size of block `i` in the balanced split of `n` into `k` blocks.

## Main results

* `Fin.sum_balancedBlockSize`: the block sizes add up to `n` when `0 < k`.
* `Fin.div_le_balancedBlockSize`, `Fin.balancedBlockSize_le_div_add_one`: every block has
  size `n / k` or `n / k + 1`.
-/

public section

namespace Fin

/-- The size of block `i` when `n` items are split into `k` contiguous blocks as evenly as
possible: the first `n % k` blocks receive one extra item. -/
@[expose] def balancedBlockSize (n k : ℕ) (i : Fin k) : ℕ :=
  n / k + if i.val < n % k then 1 else 0

/-- Every balanced block has at least `n / k` items. -/
theorem div_le_balancedBlockSize (n k : ℕ) (i : Fin k) : n / k ≤ balancedBlockSize n k i :=
  Nat.le_add_right _ _

/-- Every balanced block has at most `n / k + 1` items. -/
theorem balancedBlockSize_le_div_add_one (n k : ℕ) (i : Fin k) :
    balancedBlockSize n k i ≤ n / k + 1 := by
  unfold balancedBlockSize
  split_ifs <;> omega

/-- The balanced block sizes cover all `n` items when there is at least one block. -/
theorem sum_balancedBlockSize (n : ℕ) {k : ℕ} (hk : 0 < k) :
    ∑ i, balancedBlockSize n k i = n := by
  have hr : n % k ≤ k := (Nat.mod_lt n hk).le
  have hcount : (∑ i : Fin k, if i.val < n % k then 1 else 0) = n % k := by
    rw [Finset.sum_boole, Nat.cast_id, Fin.card_filter_val_lt, min_eq_right hr]
  simp only [balancedBlockSize, Finset.sum_add_distrib, hcount, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.div_add_mod n k

end Fin
