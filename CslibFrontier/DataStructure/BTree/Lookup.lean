/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Basic
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Search in classic B-trees

Search in the B-trees of `Cslib.DataStructure.BTree`, following [CLRS2009], Chapter 18: scan a
node's keys in order, stop at the query, or descend into the child before the first key above it.

Each operation is defined once, over an arbitrary monad `m`, taking a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`, with no order instance in scope,
so that every comparison goes through `le`. The pure operations are the `Id` instantiations with
the decidable comparator `leI` of a linear order and `visit := pure ()`, in the pattern of
CSLib's `List.mergeSortM` and `List.idRun_mergeSortM`. Costs are not stated here.

`lookupM` recurses on `.node c rest`, which is not a structural subterm, so it is defined by
well-founded recursion on `sizeOf`; `decide` and `rfl` cannot evaluate `lookup`, and concrete
lookups use the equation lemmas `lookup_node_nil` and `lookup_node_cons` through `simp`.

## Main definitions

* `slotM`, `slot`: within-node linear search, the position of the first key not below the query.
* `lookupM`, `lookup`: search for the value at a key.
* `containsM`, `contains`: membership test.

## Main results

* `Cslib.IsMonadHom.map_slotM`, `Cslib.IsMonadHom.map_lookupM`,
  `Cslib.IsMonadHom.map_containsM`: a monad morphism commutes with the operations, so that
  instantiations in other monads keep the pure value.
* `slot_eq_length_takeWhile`: the pure within-node search counts the keys below the query.
* `lookup_eq_of_isSortedAssoc`, `lookup_eq`: on a tree with sorted entries, and in particular on a
  well-formed tree, `lookup` is `List.lookup` on `toList`.
* `contains_iff_mem_keys`: a key is in a well-formed tree exactly when it is among its keys.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Lookup.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Lookup.lean).
-/

public section

universe w

namespace Cslib.DataStructure

namespace BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Within-node linear search: the position of the first key not below `k`. At most one
comparison per key. -/
@[expose] def slotM (le : α → α → m Bool) (k : α) : List (Triple α β) → m ℕ
  | [] => pure 0
  | (k', _, _) :: rest => do
    if ← le k k' then pure 0 else return (← slotM le k rest) + 1

/-- Lookup. Walking along a node's triples is free; `visit` fires when the search commits to a
child or stops at a key, so each node is visited once. Equality is two `le` queries. -/
@[expose] def lookupM (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BTree α β → m (Option β)
  | .leaf => pure none
  | .node first [] => do
    visit
    lookupM le visit k first
  | .node first ((k', v, c) :: rest) => do
    if ← le k k' then
      visit
      if ← le k' k then
        pure (some v)
      else
        lookupM le visit k first
    else
      lookupM le visit k (.node c rest)
termination_by tr => sizeOf tr

/-- Membership test. -/
@[expose] def containsM (le : α → α → m Bool) (visit : m Unit) (k : α) (tr : BTree α β) :
    m Bool := do
  return (← lookupM le visit k tr).isSome

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the within-node search. -/
theorem _root_.Cslib.IsMonadHom.map_slotM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (k : α) (rest : List (Triple α β)) :
    f (slotM le k rest) = slotM (fun a b => f (le a b)) k rest := by
  induction rest with
  | nil => simp [slotM, hf.map_pure]
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    simp [slotM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with lookup. -/
theorem _root_.Cslib.IsMonadHom.map_lookupM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (lookupM le visit k tr) = lookupM (fun a b => f (le a b)) (f visit) k tr := by
  fun_induction lookupM le visit k tr <;>
    simp [lookupM, hf.map_bind, hf.map_pure, apply_ite f, *]

/-- A monad morphism commutes with the membership test. -/
theorem _root_.Cslib.IsMonadHom.map_containsM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (containsM le visit k tr) = containsM (fun a b => f (le a b)) (f visit) k tr := by
  simp [containsM, hf.map_bind, hf.map_pure, hf.map_lookupM]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- The decidable comparator of a linear order, in the identity monad. -/
abbrev leI (a b : α) : Id Bool := pure (decide (a ≤ b))

/-- Pure within-node search: the `Id` instantiation of `slotM`. -/
@[expose] def slot (k : α) (rest : List (Triple α β)) : ℕ := Id.run (slotM leI k rest)

/-- Pure lookup: the `Id` instantiation of `lookupM` with `visit := pure ()`. -/
def lookup (k : α) (tr : BTree α β) : Option β := Id.run (lookupM leI (pure ()) k tr)

/-- Pure membership test: the `Id` instantiation of `containsM` with `visit := pure ()`. -/
def contains (k : α) (tr : BTree α β) : Bool := Id.run (containsM leI (pure ()) k tr)

/-- `slot` is the `Id` instantiation of `slotM`. -/
theorem slot_def (k : α) (rest : List (Triple α β)) :
    slot k rest = Id.run (slotM leI k rest) := (rfl)

/-- `lookup` is the `Id` instantiation of `lookupM`. -/
theorem lookup_def (k : α) : lookup k tr = Id.run (lookupM leI (pure ()) k tr) := (rfl)

/-- `contains` is the `Id` instantiation of `containsM`. -/
theorem contains_def (k : α) : contains k tr = Id.run (containsM leI (pure ()) k tr) := (rfl)

/-- The within-node search in a node without keys stops at position zero. -/
@[simp] theorem slot_nil (k : α) : slot (β := β) k [] = 0 := rfl

/-- The within-node search stops at the first key not below `k`, and otherwise moves on. -/
@[simp] theorem slot_cons (k k' : α) (v : β) (c : BTree α β) (rest : List (Triple α β)) :
    slot k ((k', v, c) :: rest) = if k ≤ k' then 0 else slot k rest + 1 := by
  by_cases hk : k ≤ k' <;> simp [slot, slotM, leI, hk]

/-- Lookup in a node without keys descends into its only child. -/
@[simp] theorem lookup_node_nil (k : α) (first : BTree α β) :
    lookup k (.node first []) = lookup k first := by
  simp [lookup, lookupM]

/-- Lookup at a node's first key: stop on equality, descend into the child before the key when
the query is below it, and otherwise move on to the remaining keys. -/
@[simp] theorem lookup_node_cons (k k' : α) (v : β) (first c : BTree α β)
    (rest : List (Triple α β)) :
    lookup k (.node first ((k', v, c) :: rest)) =
      if k ≤ k' then (if k' ≤ k then some v else lookup k first) else lookup k (.node c rest) := by
  by_cases h₁ : k ≤ k' <;> by_cases h₂ : k' ≤ k <;> simp [lookup, lookupM, leI, h₁, h₂]

/-- Membership is success of lookup. -/
@[simp] theorem contains_eq_isSome_lookup (k : α) : contains k tr = (lookup k tr).isSome := (rfl)

/-- The pure within-node search counts the keys below `k` before the first key not below it. -/
theorem slot_eq_length_takeWhile (k : α) (rest : List (Triple α β)) :
    slot k rest = (rest.takeWhile fun e => decide (e.1 < k)).length := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    unfold slot at ih ⊢
    by_cases hk : k ≤ k'
    · simp [slotM, hk, not_lt.2 hk]
    · simp [slotM, hk, lt_of_not_ge hk, ih]

/-- The pure within-node search is the index of the first key not below `k`; this is the form
that insertion and rank will use. -/
theorem slot_eq_findIdx (k : α) (rest : List (Triple α β)) :
    slot k rest = rest.findIdx fun e => decide (k ≤ e.1) := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    simp [slot_cons, List.findIdx_cons, ih]

/-- The position found by the within-node search is at most the number of keys. -/
theorem slot_le_length (k : α) (rest : List (Triple α β)) : slot k rest ≤ rest.length := by
  rw [slot_eq_length_takeWhile]
  exact (List.takeWhile_sublist _).length_le

/-- Lookup in the empty tree fails. -/
@[simp] theorem lookup_leaf (k : α) : lookup k (.leaf : BTree α β) = none := by
  simp [lookup, lookupM]

/-- Model equation: on a tree with sorted entries, lookup is lookup in `toList`. -/
theorem lookup_eq_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    lookup k tr = List.lookup k tr.toList := by
  fun_induction lookupM (m := Id) leI (pure ()) k tr with
  | case1 => simp
  | case2 first ih => simpa using ih (by simpa using h)
  | case3 first k' v c rest ih₁ ih₂ =>
    rw [toList_node, toListRest_cons, List.cons_append] at h ⊢
    rw [toList_node] at ih₂
    obtain ⟨h₁, h₂, hlt, hgt⟩ := List.isSortedAssoc_append_cons_iff.1 h
    rw [lookup_node_cons]
    rcases lt_trichotomy k k' with hk | rfl | hk
    · simp only [hk.le, not_le.2 hk, ↓reduceIte]
      rw [ih₁ h₁, List.lookup_append_of_forall_gt fun p hp => ?_]
      rcases List.mem_cons.1 hp with rfl | hp
      exacts [hk, hk.trans (hgt p hp)]
    · simp [List.lookup_append_of_forall_lt hlt]
    · simp only [not_le.2 hk, ↓reduceIte]
      rw [ih₂ h₂, List.lookup_append_of_forall_lt fun p hp => (hlt p hp).trans hk,
        List.lookup_cons_of_ne hk.ne']

/-- Model equation on well-formed trees. -/
theorem lookup_eq (h : IsWF t tr) (k : α) : lookup k tr = List.lookup k tr.toList :=
  lookup_eq_of_isSortedAssoc h.sorted k

/-- On a tree with sorted entries, membership is success of lookup in `toList`. -/
theorem contains_eq_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    contains k tr = (List.lookup k tr.toList).isSome := by
  rw [contains_eq_isSome_lookup, lookup_eq_of_isSortedAssoc h]

/-- On a tree with sorted entries, a key is in the tree exactly when it is among its keys. -/
theorem contains_iff_mem_keys_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    contains k tr = true ↔ k ∈ tr.keys := by
  simp only [contains_eq_of_isSortedAssoc h, Option.isSome_iff_exists, h.lookup_eq_some_iff,
    mem_keys, mem_def]

/-- Membership on well-formed trees is success of lookup in `toList`. -/
theorem contains_eq (h : IsWF t tr) (k : α) : contains k tr = (List.lookup k tr.toList).isSome :=
  contains_eq_of_isSortedAssoc h.sorted k

/-- A key is in a well-formed tree exactly when it is among the tree's keys. -/
theorem contains_iff_mem_keys (h : IsWF t tr) (k : α) : contains k tr = true ↔ k ∈ tr.keys :=
  contains_iff_mem_keys_of_isSortedAssoc h.sorted k

end Pure

end BTree

end Cslib.DataStructure
