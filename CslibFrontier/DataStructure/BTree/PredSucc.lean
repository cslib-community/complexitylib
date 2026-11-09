/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Lookup
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Predecessor and successor in classic B-trees

Strict predecessor and successor queries scan the keys of a node and descend into one child,
retaining a separator entry as a fallback. [CLRS2009] leaves the predecessor as Exercise 18.2-3;
the descent here follows the search of its Section 18.2. On a tree whose `toList` is sorted, run
with the comparator of the key order, the predecessor is the greatest entry with key strictly
below the query and the successor is the least entry with key strictly above it, so a key equal
to the query is never returned. For an arbitrary comparator or an unsorted tree, the definitions
describe only the descent.

`predM` and `succM` take a monadic comparator and a node-visit action, with no order instance.
Scanning triples within a node is free: `visit` fires once when the scan chooses a child,
including at nodes with no keys, and never at an empty leaf. Fallbacks require no extra descent.
The definitions use well-founded recursion on `sizeOf`; their equation lemmas are the interface
for evaluation and for other monadic instantiations.

## Main definitions

* `predM`, `pred?`: the entry with the greatest key strictly below the query.
* `succM`, `succ?`: the entry with the least key strictly above the query.

## Main results

* `Cslib.IsMonadHom.map_predM`, `Cslib.IsMonadHom.map_succM`: a monad morphism commutes with the
  queries.
* `pred?_eq_of_isSortedAssoc`, `succ?_eq_of_isSortedAssoc`: on a tree with sorted entries, the
  queries are `SortedAssoc.pred?` and `SortedAssoc.succ?` on `toList`; `pred?_eq` and `succ?_eq`
  specialize them to well-formed trees.
* `pred?_eq_some_iff`, `succ?_eq_some_iff`: on a well-formed tree, the greatest entry below and
  the least entry above the query.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 18.2][CLRS2009]

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/PredSucc.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/PredSucc.lean).
-/

public section

universe w

namespace Cslib.DataStructure.BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Strict predecessor search. Scan past the keys `k'` for which `le k k'` fails, retaining each
as a fallback; at the first key `k'` with `le k k'`, visit the node and descend into the child
before it. If there is no such key, visit the node and descend into its last child. When `le`
decides the key order and `toList` is sorted, the result is the greatest entry with key strictly
below `k`; see `pred?_eq`. -/
def predM (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BTree α β → m (Option (α × β))
  | .leaf => pure none
  | .node first [] => do
    visit
    predM le visit k first
  | .node first ((k', v, c) :: rest) => do
    if ← le k k' then
      visit
      predM le visit k first
    else
      return (← predM le visit k (.node c rest)).or (some (k', v))
termination_by tr => sizeOf tr

/-- Strict successor search. Scan past the keys `k'` with `le k' k`; at the first key `k'` for
which that fails, visit the node and descend into the child before it, retaining `(k', v)` as a
fallback. If there is no such key, visit the node and descend into its last child. When `le`
decides the key order and `toList` is sorted, the result is the least entry with key strictly
above `k`; see `succ?_eq`. -/
def succM (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BTree α β → m (Option (α × β))
  | .leaf => pure none
  | .node first [] => do
    visit
    succM le visit k first
  | .node first ((k', v, c) :: rest) => do
    if ← le k' k then
      succM le visit k (.node c rest)
    else
      visit
      return (← succM le visit k first).or (some (k', v))
termination_by tr => sizeOf tr

/-- The empty tree has no predecessor and is not visited. -/
theorem predM_leaf (le : α → α → m Bool) (visit : m Unit) (k : α) :
    predM le visit k (.leaf : BTree α β) = pure none := by
  rw [predM]

/-- A node without keys is visited before searching its only child. -/
theorem predM_node_nil (le : α → α → m Bool) (visit : m Unit) (k : α)
    (first : BTree α β) :
    predM le visit k (.node first []) = (do
      visit
      predM le visit k first) := by
  rw [predM]

/-- A predecessor scan either descends before the first separator or continues with that
separator as a fallback, without an additional visit. -/
theorem predM_node_cons (le : α → α → m Bool) (visit : m Unit) (k k' : α) (v : β)
    (first c : BTree α β) (rest : List (Triple α β)) :
    predM le visit k (.node first ((k', v, c) :: rest)) = (do
      if ← le k k' then
        visit
        predM le visit k first
      else
        return (← predM le visit k (.node c rest)).or (some (k', v))) := by
  rw [predM]

/-- The empty tree has no successor and is not visited. -/
theorem succM_leaf (le : α → α → m Bool) (visit : m Unit) (k : α) :
    succM le visit k (.leaf : BTree α β) = pure none := by
  rw [succM]

/-- A node without keys is visited before searching its only child. -/
theorem succM_node_nil (le : α → α → m Bool) (visit : m Unit) (k : α)
    (first : BTree α β) :
    succM le visit k (.node first []) = (do
      visit
      succM le visit k first) := by
  rw [succM]

/-- A successor scan either continues past the first separator for free or visits the node
and descends before that separator, retaining it as a fallback. -/
theorem succM_node_cons (le : α → α → m Bool) (visit : m Unit) (k k' : α) (v : β)
    (first c : BTree α β) (rest : List (Triple α β)) :
    succM le visit k (.node first ((k', v, c) :: rest)) = (do
      if ← le k' k then
        succM le visit k (.node c rest)
      else
        visit
        return (← succM le visit k first).or (some (k', v))) := by
  rw [succM]

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the predecessor search. -/
theorem _root_.Cslib.IsMonadHom.map_predM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (predM le visit k tr) = predM (fun a b => f (le a b)) (f visit) k tr := by
  match tr with
  | .leaf => simp [predM_leaf, hf.map_pure]
  | .node first [] => simp [predM_node_nil, hf.map_bind, hf.map_predM le visit k first]
  | .node first ((k', v, c) :: rest) =>
    simp [predM_node_cons, hf.map_bind, hf.map_pure, apply_ite f, hf.map_predM le visit k first,
      hf.map_predM le visit k (.node c rest)]
termination_by sizeOf tr

/-- A monad morphism commutes with the successor search. -/
theorem _root_.Cslib.IsMonadHom.map_succM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (succM le visit k tr) = succM (fun a b => f (le a b)) (f visit) k tr := by
  match tr with
  | .leaf => simp [succM_leaf, hf.map_pure]
  | .node first [] => simp [succM_node_nil, hf.map_bind, hf.map_succM le visit k first]
  | .node first ((k', v, c) :: rest) =>
    simp [succM_node_cons, hf.map_bind, hf.map_pure, apply_ite f, hf.map_succM le visit k first,
      hf.map_succM le visit k (.node c rest)]
termination_by sizeOf tr

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Pure strict predecessor: the `Id` instantiation of `predM` with a trivial visit action. -/
def pred? (k : α) (tr : BTree α β) : Option (α × β) :=
  Id.run (predM leI (pure ()) k tr)

/-- Pure strict successor: the `Id` instantiation of `succM` with a trivial visit action. -/
def succ? (k : α) (tr : BTree α β) : Option (α × β) :=
  Id.run (succM leI (pure ()) k tr)

/-- `pred?` is the `Id` instantiation of `predM`. -/
theorem pred?_def (k : α) : pred? k tr = Id.run (predM leI (pure ()) k tr) := (rfl)

/-- `succ?` is the `Id` instantiation of `succM`. -/
theorem succ?_def (k : α) : succ? k tr = Id.run (succM leI (pure ()) k tr) := (rfl)

/-- The empty tree has no predecessor. -/
@[simp] theorem pred?_leaf (k : α) : pred? k (.leaf : BTree α β) = none := by
  simp [pred?, predM_leaf]

/-- A node without keys has the predecessor of its only child. -/
@[simp] theorem pred?_node_nil (k : α) (first : BTree α β) :
    pred? k (.node first []) = pred? k first := by
  simp [pred?, predM_node_nil]

/-- The predecessor lies before the first separator at least `k`; a smaller separator is a
fallback for the search in the remaining suffix. -/
@[simp] theorem pred?_node_cons (k k' : α) (v : β) (first c : BTree α β)
    (rest : List (Triple α β)) :
    pred? k (.node first ((k', v, c) :: rest)) =
      if k ≤ k' then pred? k first else (pred? k (.node c rest)).or (some (k', v)) := by
  by_cases hk : k ≤ k' <;> simp [pred?, predM_node_cons, leI, hk]

/-- The empty tree has no successor. -/
@[simp] theorem succ?_leaf (k : α) : succ? k (.leaf : BTree α β) = none := by
  simp [succ?, succM_leaf]

/-- A node without keys has the successor of its only child. -/
@[simp] theorem succ?_node_nil (k : α) (first : BTree α β) :
    succ? k (.node first []) = succ? k first := by
  simp [succ?, succM_node_nil]

/-- The successor search skips separators at most `k`; the first larger separator is a
fallback for the search in the child before it. -/
@[simp] theorem succ?_node_cons (k k' : α) (v : β) (first c : BTree α β)
    (rest : List (Triple α β)) :
    succ? k (.node first ((k', v, c) :: rest)) =
      if k' ≤ k then succ? k (.node c rest) else (succ? k first).or (some (k', v)) := by
  by_cases hk : k' ≤ k <;> simp [succ?, succM_node_cons, leI, hk]

/-- Model equation: on a tree with sorted entries, `pred?` is the model's strict predecessor
in `toList`. -/
theorem pred?_eq_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    pred? k tr = SortedAssoc.pred? k tr.toList := by
  fun_induction predM (m := Id) leI (pure ()) k tr with
  | case1 => simp
  | case2 first ih => simpa using ih (by simpa using h)
  | case3 first k' v c rest ih₁ ih₂ =>
    rw [toList_node, toListRest_cons, List.cons_append] at h ⊢
    rw [toList_node] at ih₂
    obtain ⟨h₁, h₂, _, hgt⟩ := List.isSortedAssoc_append_cons_iff.1 h
    rw [pred?_node_cons]
    by_cases hk : k ≤ k'
    · have hn : SortedAssoc.pred? k ((k', v) :: (c.toList ++ toListRest rest)) = none := by
        apply SortedAssoc.pred?_eq_none_iff.2
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hk
        · exact hk.trans (hgt p hp).le
      simp only [hk, ↓reduceIte, SortedAssoc.pred?_append, hn, Option.none_or, ih₁ h₁]
    · have hs : SortedAssoc.pred? k [(k', v)] = some (k', v) := by
        simp only [SortedAssoc.pred?_singleton, lt_of_not_ge hk, ↓reduceIte]
      rw [← List.singleton_append (x := (k', v))]
      simp only [hk, ↓reduceIte, SortedAssoc.pred?_append, hs, Option.or_assoc,
        Option.some_or, ih₂ h₂]

/-- Model equation: on a tree with sorted entries, `succ?` is the model's strict successor
in `toList`. -/
theorem succ?_eq_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    succ? k tr = SortedAssoc.succ? k tr.toList := by
  fun_induction succM (m := Id) leI (pure ()) k tr with
  | case1 => simp
  | case2 first ih => simpa using ih (by simpa using h)
  | case3 first k' v c rest ih₁ ih₂ =>
    rw [toList_node, toListRest_cons, List.cons_append] at h ⊢
    rw [toList_node] at ih₁
    obtain ⟨h₁, h₂, hlt, _⟩ := List.isSortedAssoc_append_cons_iff.1 h
    rw [succ?_node_cons, ← List.singleton_append (x := (k', v))]
    by_cases hk : k' ≤ k
    · have hn : SortedAssoc.succ? k first.toList = none :=
        SortedAssoc.succ?_eq_none_iff.2 fun p hp => (hlt p hp).le.trans hk
      have hs : SortedAssoc.succ? k [(k', v)] = none := by
        simp only [SortedAssoc.succ?_singleton, not_lt.2 hk, ↓reduceIte]
      simp only [hk, ↓reduceIte, SortedAssoc.succ?_append, hn, hs, Option.none_or, ih₁ h₂]
    · have hs : SortedAssoc.succ? k [(k', v)] = some (k', v) := by
        simp only [SortedAssoc.succ?_singleton, lt_of_not_ge hk, ↓reduceIte]
      simp only [hk, ↓reduceIte, SortedAssoc.succ?_append, hs, Option.some_or, ih₂ h₁]

/-- Model equation for strict predecessor on well-formed trees. -/
theorem pred?_eq (h : IsWF t tr) (k : α) : pred? k tr = SortedAssoc.pred? k tr.toList :=
  pred?_eq_of_isSortedAssoc h.sorted k

/-- Model equation for strict successor on well-formed trees. -/
theorem succ?_eq (h : IsWF t tr) (k : α) : succ? k tr = SortedAssoc.succ? k tr.toList :=
  succ?_eq_of_isSortedAssoc h.sorted k

/-- On a tree with sorted entries, there is no predecessor exactly when every key is at
least the query. -/
theorem pred?_eq_none_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    pred? k tr = none ↔ ∀ q ∈ tr, k ≤ q.1 := by
  simp only [pred?_eq_of_isSortedAssoc h, SortedAssoc.pred?_eq_none_iff, mem_def]

/-- On a tree with sorted entries, there is no successor exactly when every key is at most
the query. -/
theorem succ?_eq_none_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    succ? k tr = none ↔ ∀ q ∈ tr, q.1 ≤ k := by
  simp only [succ?_eq_of_isSortedAssoc h, SortedAssoc.succ?_eq_none_iff, mem_def]

/-- On a tree with sorted entries, the predecessor is exactly the greatest entry whose key
is strictly below the query. -/
theorem pred?_eq_some_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) {p : α × β} :
    pred? k tr = some p ↔ p ∈ tr ∧ p.1 < k ∧ ∀ q ∈ tr, q.1 < k → q.1 ≤ p.1 := by
  simpa only [pred?_eq_of_isSortedAssoc h, mem_def] using
    (SortedAssoc.pred?_eq_some_iff (k := k) (p := p) h)

/-- On a tree with sorted entries, the successor is exactly the least entry whose key
is strictly above the query. -/
theorem succ?_eq_some_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) {p : α × β} :
    succ? k tr = some p ↔ p ∈ tr ∧ k < p.1 ∧ ∀ q ∈ tr, k < q.1 → p.1 ≤ q.1 := by
  simpa only [succ?_eq_of_isSortedAssoc h, mem_def] using
    (SortedAssoc.succ?_eq_some_iff (k := k) (p := p) h)

/-- A well-formed tree has no predecessor of `k` exactly when all its keys are at least `k`. -/
theorem pred?_eq_none_iff (h : IsWF t tr) (k : α) :
    pred? k tr = none ↔ ∀ q ∈ tr, k ≤ q.1 :=
  pred?_eq_none_iff_of_isSortedAssoc h.sorted k

/-- A well-formed tree has no successor of `k` exactly when all its keys are at most `k`. -/
theorem succ?_eq_none_iff (h : IsWF t tr) (k : α) :
    succ? k tr = none ↔ ∀ q ∈ tr, q.1 ≤ k :=
  succ?_eq_none_iff_of_isSortedAssoc h.sorted k

/-- In a well-formed tree, `pred? k` is exactly the greatest entry strictly below `k`. -/
theorem pred?_eq_some_iff (h : IsWF t tr) (k : α) {p : α × β} :
    pred? k tr = some p ↔ p ∈ tr ∧ p.1 < k ∧ ∀ q ∈ tr, q.1 < k → q.1 ≤ p.1 :=
  pred?_eq_some_iff_of_isSortedAssoc h.sorted k

/-- In a well-formed tree, `succ? k` is exactly the least entry strictly above `k`. -/
theorem succ?_eq_some_iff (h : IsWF t tr) (k : α) {p : α × β} :
    succ? k tr = some p ↔ p ∈ tr ∧ k < p.1 ∧ ∀ q ∈ tr, k < q.1 → p.1 ≤ q.1 :=
  succ?_eq_some_iff_of_isSortedAssoc h.sorted k

end Pure

end Cslib.DataStructure.BTree
