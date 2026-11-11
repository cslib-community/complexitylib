/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, products of lists padded by ones)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.OfFn

/-!
# Products of lists padded by ones

Extending a tuple `A : Fin m → α` in a monoid by ones to a tuple of length `N ≥ m` does not
change the product of its list (`List.prod_ofFn_dite_lt`). The monoid need not be commutative,
so this applies to products of matrices. With `List.ofFn_mul` it lets a product of `m` factors
be grouped into blocks of equal length when `m` is not a multiple of the block length.

## Main results

* `List.prod_ofFn_dite_lt`: a product padded by ones equals the unpadded product.
-/

public section

namespace List

variable {α : Type*} [Monoid α]

/-- Padding a tuple by ones does not change the product of its list. -/
theorem prod_ofFn_dite_lt {m N : ℕ} (h : m ≤ N) (A : Fin m → α) :
    (ofFn fun i : Fin N => if hi : (i : ℕ) < m then A ⟨i, hi⟩ else 1).prod = (ofFn A).prod := by
  induction N with
  | zero =>
    obtain rfl : m = 0 := by omega
    simp
  | succ N ih =>
    rcases h.eq_or_lt with rfl | hlt
    · exact congrArg (fun f => (ofFn f).prod) (funext fun i => dite_eq_left i.2)
    · rw [ofFn_succ', concat_eq_append, prod_append, prod_singleton,
        dite_eq_right (by simp only [Fin.val_last]; omega), mul_one]
      exact ih (by omega)

end List
