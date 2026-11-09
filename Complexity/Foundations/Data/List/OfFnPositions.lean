/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib Data/List/OfFn)

public import Complexity.Init
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Positional operations on function-indexed lists

Reversal, cyclic movement of the first entry, and positional deletion act on the original
finite index type. Empty output words and repeated values are retained. These identities
supply actual scope coordinates without a distinctness assumption on values.
-/

public section

namespace List

/-- Reversing the finite word reverses its positional indices, even when values repeat. -/
theorem reverse_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (ofFn f).reverse = ofFn (fun i => f i.rev) := by
  apply ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn, Fin.rev]
    apply congrArg f
    apply Fin.ext
    change n - 1 - i = n - (i + 1)
    omega

/-- Positive cyclic index rotation moves the first list entry to the end, retaining every
position even when values repeat. -/
theorem ofFn_cons_finRotate {α : Type*} {n : ℕ} (a : α) (f : Fin n → α) :
    ofFn (Fin.cons a f ∘ finRotate (n + 1)) = ofFn f ++ [a] := by
  have h : (Fin.cons a f ∘ finRotate (n + 1) : Fin (n + 1) → α) = Fin.snoc f a :=
    (Fin.snoc_eq_cons_rotate f a).symm
  rw [h, ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, concat_eq_append]

/-- Deleting one actual list position retains the `succAbove` order of all survivors.
This is positional deletion, not value deletion, and allows repeated values. -/
theorem eraseIdx_ofFn {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    (ofFn f).eraseIdx j.val = ofFn (fun i => f (j.succAbove i)) := by
  apply ext_getElem
  · rw [length_eraseIdx_of_lt (by simpa only [length_ofFn] using j.isLt)]
    simp
  · intro i hi hj
    rw [getElem_eraseIdx]
    simp only [List.getElem_ofFn, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs <;> apply congrArg f <;> apply Fin.ext <;> rfl

end List
