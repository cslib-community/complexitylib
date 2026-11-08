/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import Complexity.DataStructure.BTree.Erase.Basic
public import Complexity.DataStructure.BTree.MinMax

/-!
# Removing the least and greatest entries of classic B-trees

`eraseMinM` and `eraseMaxM` remove and return the least and greatest entries of a B-tree: they
find the extreme entry with `minM` or `maxM` and erase its key with `eraseM`, over an arbitrary
monad with a comparator and a node-visit action. The pure operations are the `Id`
instantiations with `leI` and `visit := pure ()`. Costs are not stated here.

## Main definitions

* `eraseMinM`, `eraseMin?`: remove and return the least entry.
* `eraseMaxM`, `eraseMax?`: remove and return the greatest entry.

## Main results

* `Cslib.IsMonadHom.map_eraseMinM`, `Cslib.IsMonadHom.map_eraseMaxM`: a monad morphism commutes
  with the operations.
* `eraseMin?_eq`, `eraseMax?_eq`: the model equations, on any tree: the first or last entry of
  `toList` together with the erasure of its key.
* `toList_of_eraseMin?_eq_some`, `toList_of_eraseMax?_eq_some`: on a well-formed tree, the
  entries split into the removed entry and those of a well-formed rest.

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Erase/MinMax.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Erase/MinMax.lean).
-/

public section

universe w

namespace Cslib.DataStructure.BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Remove and return the least entry: find it with `minM`, then erase its key. -/
@[expose] def eraseMinM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    m (Option ((α × β) × BTree α β)) := do
  match ← minM visit tr with
  | none => pure none
  | some p => return some (p, ← eraseM t le visit p.1 tr)

/-- Removing the least entry finds it with `minM`, then erases its key. -/
theorem eraseMinM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    eraseMinM t le visit tr = (do
      match ← minM visit tr with
      | none => pure none
      | some p => return some (p, ← eraseM t le visit p.1 tr)) := rfl

/-- Remove and return the greatest entry: find it with `maxM`, then erase its key. -/
@[expose] def eraseMaxM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    m (Option ((α × β) × BTree α β)) := do
  match ← maxM visit tr with
  | none => pure none
  | some p => return some (p, ← eraseM t le visit p.1 tr)

/-- Removing the greatest entry finds it with `maxM`, then erases its key. -/
theorem eraseMaxM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    eraseMaxM t le visit tr = (do
      match ← maxM visit tr with
      | none => pure none
      | some p => return some (p, ← eraseM t le visit p.1 tr)) := rfl

/-- The empty tree has no least entry to remove. -/
@[simp] theorem eraseMinM_leaf [LawfulMonad m] (t : ℕ) (le : α → α → m Bool) (visit : m Unit) :
    eraseMinM t le visit (.leaf : BTree α β) = pure none := by
  simp [eraseMinM_def, minM_leaf]

/-- The empty tree has no greatest entry to remove. -/
@[simp] theorem eraseMaxM_leaf [LawfulMonad m] (t : ℕ) (le : α → α → m Bool) (visit : m Unit) :
    eraseMaxM t le visit (.leaf : BTree α β) = pure none := by
  simp [eraseMaxM_def, maxM_leaf]

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the removal of the least entry. -/
theorem _root_.Cslib.IsMonadHom.map_eraseMinM (hf : IsMonadHom m n f) (t : ℕ)
    (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    f (eraseMinM t le visit tr) = eraseMinM t (fun a b => f (le a b)) (f visit) tr := by
  simp only [eraseMinM_def, hf.map_bind, hf.map_minM]
  refine bind_congr fun o => ?_
  cases o <;> simp [hf.map_bind, hf.map_pure, hf.map_eraseM]

/-- A monad morphism commutes with the removal of the greatest entry. -/
theorem _root_.Cslib.IsMonadHom.map_eraseMaxM (hf : IsMonadHom m n f) (t : ℕ)
    (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    f (eraseMaxM t le visit tr) = eraseMaxM t (fun a b => f (le a b)) (f visit) tr := by
  simp only [eraseMaxM_def, hf.map_bind, hf.map_maxM]
  refine bind_congr fun o => ?_
  cases o <;> simp [hf.map_bind, hf.map_pure, hf.map_eraseM]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Remove and return the least entry, pure. -/
@[expose] def eraseMin? (t : ℕ) (tr : BTree α β) : Option ((α × β) × BTree α β) :=
  Id.run (eraseMinM t leI (pure ()) tr)

/-- Remove and return the greatest entry, pure. -/
@[expose] def eraseMax? (t : ℕ) (tr : BTree α β) : Option ((α × β) × BTree α β) :=
  Id.run (eraseMaxM t leI (pure ()) tr)

/-- `eraseMin?` is the `Id` instantiation of `eraseMinM`. -/
theorem eraseMin?_def : eraseMin? t tr = Id.run (eraseMinM t leI (pure ()) tr) := (rfl)

/-- `eraseMax?` is the `Id` instantiation of `eraseMaxM`. -/
theorem eraseMax?_def : eraseMax? t tr = Id.run (eraseMaxM t leI (pure ()) tr) := (rfl)

/-- `eraseMin?` is the minimum together with the erasure of its key. -/
theorem eraseMin?_eq_map_min? : eraseMin? t tr = (min? tr).map fun p => (p, erase t p.1 tr) := by
  unfold eraseMin? eraseMinM min?
  -- In `Id`, bind is application and `pure` is the identity, so each branch of the monadic
  -- `match` on the found entry is the corresponding branch of `Option.map` by definition.
  cases minM (m := Id) (pure ()) tr <;> rfl

/-- `eraseMax?` is the maximum together with the erasure of its key. -/
theorem eraseMax?_eq_map_max? : eraseMax? t tr = (max? tr).map fun p => (p, erase t p.1 tr) := by
  rw [max?_def]
  unfold eraseMax? eraseMaxM
  -- as in `eraseMin?_eq_map_min?`, each branch in `Id` is the `Option.map` branch by definition
  cases maxM (m := Id) (pure ()) tr <;> rfl

/-- The empty tree has no least entry to remove. -/
@[simp] theorem eraseMin?_leaf : eraseMin? t (.leaf : BTree α β) = none := by
  simp [eraseMin?_eq_map_min?]

/-- The empty tree has no greatest entry to remove. -/
@[simp] theorem eraseMax?_leaf : eraseMax? t (.leaf : BTree α β) = none := by
  simp [eraseMax?_eq_map_max?]

/-- Model equation of `eraseMin?`: the first entry and the tree with its key erased. -/
theorem eraseMin?_eq : eraseMin? t tr = tr.toList.head?.map fun p => (p, erase t p.1 tr) := by
  rw [eraseMin?_eq_map_min?, min?_eq]

/-- Model equation of `eraseMax?`: the last entry and the tree with its key erased. -/
theorem eraseMax?_eq : eraseMax? t tr = tr.toList.getLast?.map fun p => (p, erase t p.1 tr) := by
  rw [eraseMax?_eq_map_max?, max?_eq]

/-- `eraseMin?` returns `p` and `tr'` exactly when `p` is the first entry and `tr'` the tree with
its key erased. -/
theorem eraseMin?_eq_some_iff {p : α × β} {tr' : BTree α β} :
    eraseMin? t tr = some (p, tr') ↔ tr.toList.head? = some p ∧ tr' = erase t p.1 tr := by
  rw [eraseMin?_eq, Option.map_eq_some_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    exact ⟨hq, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- `eraseMax?` returns `p` and `tr'` exactly when `p` is the last entry and `tr'` the tree with
its key erased. -/
theorem eraseMax?_eq_some_iff {p : α × β} {tr' : BTree α β} :
    eraseMax? t tr = some (p, tr') ↔ tr.toList.getLast? = some p ∧ tr' = erase t p.1 tr := by
  rw [eraseMax?_eq, Option.map_eq_some_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    exact ⟨hq, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- On a tree with sorted entries, `eraseMin?` splits the entries into the first and the rest. -/
theorem toList_of_eraseMin?_eq_some_of_isSortedAssoc (h : tr.toList.IsSortedAssoc)
    {p : α × β} {tr' : BTree α β} (he : eraseMin? t tr = some (p, tr')) :
    tr.toList = p :: tr'.toList := by
  obtain ⟨hq, rfl⟩ := eraseMin?_eq_some_iff.1 he
  obtain ⟨l, hl⟩ : ∃ l, tr.toList = p :: l := by
    cases hc : tr.toList with
    | nil => simp [hc] at hq
    | cons a l => simp only [hc, List.head?_cons, Option.some.injEq] at hq; exact ⟨l, hq ▸ rfl⟩
  have hs := h
  rw [hl, List.isSortedAssoc_cons_iff] at hs
  rw [toList_erase_of_isSortedAssoc h, hl, SortedAssoc.erase_cons]
  simp only [↓reduceIte]
  rw [SortedAssoc.erase_of_forall_ne fun r hr => (hs.1 r hr).ne']

/-- On a tree with sorted entries, `eraseMax?` splits the entries into the rest and the last. -/
theorem toList_of_eraseMax?_eq_some_of_isSortedAssoc (h : tr.toList.IsSortedAssoc)
    {p : α × β} {tr' : BTree α β} (he : eraseMax? t tr = some (p, tr')) :
    tr.toList = tr'.toList ++ [p] := by
  obtain ⟨hq, rfl⟩ := eraseMax?_eq_some_iff.1 he
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 hq
  have hs := h
  rw [hl, List.isSortedAssoc_append_iff] at hs
  rw [toList_erase_of_isSortedAssoc h, hl, SortedAssoc.erase_append,
    SortedAssoc.erase_of_forall_ne fun r hr => (hs.2.2 r hr p (by simp)).ne]
  simp [SortedAssoc.erase_cons]

/-- On a well-formed tree, `eraseMin?` splits the entries into the first and the rest, and the
rest is well-formed. -/
theorem toList_of_eraseMin?_eq_some (h : IsWF t tr) {p : α × β} {tr' : BTree α β}
    (he : eraseMin? t tr = some (p, tr')) : tr.toList = p :: tr'.toList ∧ IsWF t tr' := by
  refine ⟨toList_of_eraseMin?_eq_some_of_isSortedAssoc h.sorted he, ?_⟩
  exact (eraseMin?_eq_some_iff.1 he).2 ▸ h.erase _

/-- On a well-formed tree, `eraseMax?` splits the entries into the rest and the last, and the
rest is well-formed. -/
theorem toList_of_eraseMax?_eq_some (h : IsWF t tr) {p : α × β} {tr' : BTree α β}
    (he : eraseMax? t tr = some (p, tr')) : tr.toList = tr'.toList ++ [p] ∧ IsWF t tr' := by
  refine ⟨toList_of_eraseMax?_eq_some_of_isSortedAssoc h.sorted he, ?_⟩
  exact (eraseMax?_eq_some_iff.1 he).2 ▸ h.erase _

end Pure

end Cslib.DataStructure.BTree
