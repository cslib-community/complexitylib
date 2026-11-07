/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: candidate
public import Complexity.Foundations.Data.BitString.Block
/-!
# Fixed-width blocks of a padded bit list

`BitString.padBlocks n L x` reads the bit list `x` as `L / n` consecutive blocks of `n` bits, block
`i` being `BitString.listBlock n x i` padded with `false` past the end of `x`. Only the first
`(L / n) * n` positions take part: the block count is the floor `L / n`, so when `n ∤ L` the last
`L % n` positions below `L` are dropped, and bits of `x` at positions `≥ (L / n) * n` are ignored.
The reading is exact (`padBlocks_getElem_apply` reads every bit of `x`) when `n ∣ L` and
`x.length ≤ L`.

## Main definitions

* `Cslib.BitString.padBlocks`: the first `L / n` padded width-`n` blocks of a bit list.

## Main results

* `Cslib.BitString.length_padBlocks`: there are exactly `L / n` blocks.
* `Cslib.BitString.padBlocks_getElem_apply`: bit `j` of block `i` is bit `i * n + j` of the list,
  or `false` past its end.
-/
@[expose] public section
namespace Cslib.BitString
/-- The first `L / n` blocks of `n` bits of the bit list `x`: block `i` is `listBlock n x i`,
  padded with `false` past the end of `x`. The block count is the floor `L / n`, so positions
  `≥ (L / n) * n` are dropped; the reading is exact when `n ∣ L` and `x.length ≤ L`. -/
def padBlocks (n L : ℕ) (x : List Bool) : List (BitString n) :=
  List.ofFn fun i : Fin (L / n) => fun j : Fin n => (listBlock n x i).getD j false
/-- `padBlocks n L x` has `L / n` blocks, whatever the length of `x`. -/
@[simp] theorem length_padBlocks (n L : ℕ) (x : List Bool) : (padBlocks n L x).length = L / n := by
  simp [padBlocks]
/-- Bit `j` of block `i` of `padBlocks n L x` is bit `i * n + j` of `x`, or `false` past its end. -/
theorem padBlocks_getElem_apply (n L : ℕ) (x : List Bool) (i : ℕ) (hi : i < L / n) (j : Fin n) :
    ((padBlocks n L x)[i]'(by simpa using hi)) j = x.getD (i * n + j) false := by
  have h : ∀ (l : List (BitString n)) (hl : l = padBlocks n L x) (h' : i < l.length),
      l[i] j = x.getD (i * n + j) false := by
    rintro l hl h'
    subst hl
    unfold padBlocks at h' ⊢
    rw [List.getElem_ofFn]
    simp only [listBlock, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt j.isLt,
      List.getElem?_drop]
  exact h _ rfl _
end Cslib.BitString
