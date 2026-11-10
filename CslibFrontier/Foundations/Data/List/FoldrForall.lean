/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib: `List.apply_foldr_iff_forall` in `Mathlib/Data/List/Basic.lean`,
-- `List.apply_foldr_map_univ_toList_iff` in `Mathlib/Data/Fintype/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Basic

/-!
# Predicates that distribute over a fold

A predicate `p` that holds of the initial value and satisfies `p (op x y) ↔ p x ∧ p y` holds of
`l.foldr op init` exactly when it holds of every element of `l`. Typical instances are the truth,
rank bound and free-variable bound of a finite conjunction of formulas, built as a fold of a binary
conjunction from a true formula.

## Main results

* `List.apply_foldr_iff_forall`: a predicate distributing over `op` holds of a fold exactly when
  it holds of every folded element.
* `List.apply_foldr_map_univ_toList_iff`: the same for a fold over an enumeration of a finite type.
-/

public section

namespace List

variable {α : Type*} {op : α → α → α} {init : α} {p : α → Prop}

/-- A predicate `p` that holds of `init` and distributes over `op`, in the sense that
`p (op x y) ↔ p x ∧ p y`, holds of `l.foldr op init` exactly when it holds of every element of
`l`. -/
theorem apply_foldr_iff_forall (hop : ∀ x y, p (op x y) ↔ p x ∧ p y) (hinit : p init)
    (l : List α) : p (l.foldr op init) ↔ ∀ x ∈ l, p x := by
  induction l with
  | nil => simp only [foldr_nil, not_mem_nil, false_imp_iff, imp_true_iff, hinit]
  | cons x l ih => rw [foldr_cons, hop, ih, forall_mem_cons]

/-- A predicate `p` that holds of `init` and distributes over `op` holds of the fold of `op` over
the values of `f` on an enumeration of a finite type exactly when it holds of every value. -/
theorem apply_foldr_map_univ_toList_iff {β : Type*} [Fintype β]
    (hop : ∀ x y, p (op x y) ↔ p x ∧ p y) (hinit : p init) (f : β → α) :
    p (((Finset.univ : Finset β).toList.map f).foldr op init) ↔ ∀ b, p (f b) := by
  rw [apply_foldr_iff_forall hop hinit]
  simp only [mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]

end List
