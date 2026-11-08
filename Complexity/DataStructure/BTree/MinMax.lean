/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import Complexity.DataStructure.BTree.Basic
public import Cslib.Foundations.Control.Monad.IsMonadHom

/-!
# Minimum and maximum in classic B-trees

The extremal-entry queries follow the leftmost or rightmost child, as in [CLRS2009], Chapter 18.
Each is defined once over an arbitrary monad, with a node-visit action, then instantiated at `Id`
for the pure query. No comparator or order instance is needed: the queries use the tree's
structural order. A visit is charged once for each node on the descent, leaves excluded and nodes
without keys included; scanning a node's triples for its last child charges no further visits.

The model equations hold on any tree, without sortedness or occupancy, and the queries return
`none` exactly when the tree has no entries, including malformed trees whose nodes have no keys.

## Main definitions

* `minM`, `min?`: the entry of the leftmost key.
* `maxM`, `max?`: the entry of the rightmost key.

## Main results

* `Cslib.IsMonadHom.map_minM`, `Cslib.IsMonadHom.map_maxM`: a monad morphism commutes with the
  queries.
* `min?_eq`, `max?_eq`: the queries are `head?` and `getLast?` of `toList`, on any tree.
* `min?_eq_some_iff`, `max?_eq_some_iff`: on a well-formed tree, the least and greatest entries
  by key.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/MinMax.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/MinMax.lean).
-/

public section

universe w

namespace Cslib.DataStructure.BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- First entry in structural order: descend through first children, falling back to the
node's first entry when its first child has no entries. `visit` fires once per node, before
descending into its first child, and no comparisons are needed. -/
@[expose] def minM (visit : m Unit) : BTree α β → m (Option (α × β))
  | .leaf => pure none
  | .node first rest => do
    visit
    match ← minM visit first with
    | some p => pure (some p)
    | none => pure (rest.head?.map fun (e : Triple α β) => (e.1, e.val))

-- `maxM` recurses on `.node c (e :: rest)`, which is not a structural subterm, so it is defined
-- by well-founded recursion on `sizeOf` and left unexposed; later modules rewrite with the
-- monadic equations `maxM_leaf`, `maxM_node_nil`, `maxM_node_singleton` and
-- `maxM_node_cons_cons`. `minM` and `min?` are exposed because `minM` is structurally recursive,
-- so `decide` evaluates `min?`.

/-- Greatest entry, the last in structural order: walk along each node's triples, which is free,
and descend into the last child, falling back to the last entry when that child has no entries.
`visit` fires once per node: when the walk reaches the node's last triple, or, at a node without
keys, before descending into its only child. -/
def maxM (visit : m Unit) : BTree α β → m (Option (α × β))
  | .leaf => pure none
  | .node first [] => do
    visit
    maxM visit first
  | .node _ [(k, v, c)] => do
    visit
    match ← maxM visit c with
    | some p => pure (some p)
    | none => pure (some (k, v))
  | .node _ ((_, _, c) :: e :: rest) => maxM visit (.node c (e :: rest))
termination_by tr => sizeOf tr

/-- The empty tree has no minimum entry and is not visited. -/
theorem minM_leaf (visit : m Unit) : minM visit (.leaf : BTree α β) = pure none := (rfl)

/-- At a node, `visit` fires before the first child's minimum, which takes priority over the
node's first entry. -/
theorem minM_node (visit : m Unit) (first : BTree α β) (rest : List (Triple α β)) :
    minM visit (.node first rest) = (do
      visit
      match ← minM visit first with
      | some p => pure (some p)
      | none => pure (rest.head?.map fun (e : Triple α β) => (e.1, e.val))) := (rfl)

/-- The empty tree has no maximum entry and is not visited. -/
theorem maxM_leaf (visit : m Unit) : maxM visit (.leaf : BTree α β) = pure none := by
  rw [maxM]

/-- A node without keys is visited, then the maximum of its only child is returned. -/
theorem maxM_node_nil (visit : m Unit) (first : BTree α β) :
    maxM visit (.node first []) = (do
      visit
      maxM visit first) := by
  rw [maxM]

/-- At the last triple, the node is visited, then the last child's maximum takes priority over
the last entry. -/
theorem maxM_node_singleton (visit : m Unit) (first c : BTree α β) (k : α) (v : β) :
    maxM visit (.node first [(k, v, c)]) = (do
      visit
      match ← maxM visit c with
      | some p => pure (some p)
      | none => pure (some (k, v))) := by
  rw [maxM]

/-- Walking past a triple is free: the maximum continues on the remaining suffix of the node,
with no visit. -/
theorem maxM_node_cons_cons (visit : m Unit) (first c : BTree α β) (k : α) (v : β)
    (e : Triple α β) (rest : List (Triple α β)) :
    maxM visit (.node first ((k, v, c) :: e :: rest)) = maxM visit (.node c (e :: rest)) := by
  rw [maxM]

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the minimum search. -/
theorem _root_.Cslib.IsMonadHom.map_minM (hf : IsMonadHom m n f) (visit : m Unit)
    (tr : BTree α β) : f (minM visit tr) = minM (f visit) tr := by
  fun_induction minM visit tr with
  | case1 => simp [minM, hf.map_pure]
  | case2 first rest ih =>
    simp only [minM, hf.map_bind, ih]
    congr; funext; congr; funext o
    cases o <;> simp [hf.map_pure]

/-- A monad morphism commutes with the maximum search. -/
theorem _root_.Cslib.IsMonadHom.map_maxM (hf : IsMonadHom m n f) (visit : m Unit)
    (tr : BTree α β) : f (maxM visit tr) = maxM (f visit) tr := by
  match tr with
  | .leaf => simp [maxM_leaf, hf.map_pure]
  | .node first [] => simp [maxM_node_nil, hf.map_bind, hf.map_maxM visit first]
  | .node first [(k, v, c)] =>
    simp only [maxM_node_singleton, hf.map_bind, hf.map_maxM visit c]
    congr; funext; congr; funext o
    cases o <;> simp [hf.map_pure]
  | .node first ((k, v, c) :: e :: rest) =>
    simp [maxM_node_cons_cons, hf.map_maxM visit (.node c (e :: rest))]
termination_by sizeOf tr

end Transfer

section Pure

variable {α β : Type} {tr : BTree α β}

/-- Pure minimum query: the `Id` instantiation of `minM` with a trivial visit action. -/
@[expose] def min? (tr : BTree α β) : Option (α × β) := Id.run (minM (pure ()) tr)

/-- Pure maximum query: the `Id` instantiation of `maxM` with a trivial visit action. -/
def max? (tr : BTree α β) : Option (α × β) := Id.run (maxM (pure ()) tr)

/-- `min?` is the `Id` instantiation of `minM`. -/
theorem min?_def : min? tr = Id.run (minM (pure ()) tr) := (rfl)

/-- `max?` is the `Id` instantiation of `maxM`. -/
theorem max?_def : max? tr = Id.run (maxM (pure ()) tr) := (rfl)

/-- The empty tree has no minimum entry. -/
@[simp] theorem min?_leaf : min? (.leaf : BTree α β) = none := by
  simp [min?, minM]

/-- The empty tree has no maximum entry. -/
@[simp] theorem max?_leaf : max? (.leaf : BTree α β) = none := by
  simp [max?, maxM_leaf]

/-- The first child's minimum takes priority over the node's first entry. -/
@[simp] theorem min?_node (first : BTree α β) (rest : List (Triple α β)) :
    min? (.node first rest) =
      (min? first).or (rest.head?.map fun (e : Triple α β) => (e.1, e.val)) := by
  simp only [min?, minM, Id.run_bind]
  cases Id.run (minM (pure ()) first) <;> rfl

/-- A node without keys has the maximum of its only child. -/
@[simp] theorem max?_node_nil (first : BTree α β) :
    max? (.node first []) = max? first := by
  simp [max?, maxM_node_nil]

/-- At the last triple, the last child's maximum takes priority over the last entry. -/
@[simp] theorem max?_node_singleton (first c : BTree α β) (k : α) (v : β) :
    max? (.node first [(k, v, c)]) = (max? c).or (some (k, v)) := by
  simp only [max?, maxM_node_singleton, Id.run_bind]
  cases Id.run (maxM (pure ()) c) <;> rfl

/-- Scanning past a triple leaves the maximum query on the remaining suffix of the node. -/
@[simp] theorem max?_node_cons_cons (first c : BTree α β) (k : α) (v : β)
    (e : Triple α β) (rest : List (Triple α β)) :
    max? (.node first ((k, v, c) :: e :: rest)) = max? (.node c (e :: rest)) := by
  simp [max?, maxM_node_cons_cons]

/-- Model equation: the minimum query returns the first entry of `toList`, on any tree. -/
theorem min?_eq : min? tr = tr.toList.head? := by
  induction tr with
  | leaf => simp
  | node first rest ih _ =>
    rw [min?_node, toList_node, List.head?_append, ih]
    cases rest <;> simp

/-- Model equation: the maximum query returns the last entry of `toList`, on any tree. -/
theorem max?_eq : max? tr = tr.toList.getLast? := by
  fun_induction maxM (m := Id) (pure ()) tr with
  | case1 => simp
  | case2 first ih => simpa using ih
  | case3 first k v c ih =>
    simp only [max?_node_singleton, ih, toList_node, toListRest_cons, toListRest_nil,
      List.append_nil, List.getLast?_append_cons]
    simp [List.getLast?_cons]
  | case4 first k v c e rest ih =>
    rw [max?_node_cons_cons, ih]
    simp only [toList_node, toListRest_cons, List.cons_append, List.getLast?_append_cons]
    exact (List.getLast?_cons_of_ne_nil (by simp)).symm

/-- The minimum query fails exactly when there are no entries. -/
@[simp] theorem min?_eq_none_iff : min? tr = none ↔ tr.size = 0 := by
  simp [min?_eq, ← length_toList]

/-- The maximum query fails exactly when there are no entries. -/
@[simp] theorem max?_eq_none_iff : max? tr = none ↔ tr.size = 0 := by
  simp [max?_eq, ← length_toList]

variable [LinearOrder α] {t : ℕ} {p : α × β}

/-- On a tree with sorted entries, `min?` returns exactly the entry of least key. -/
theorem min?_eq_some_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) :
    min? tr = some p ↔ p ∈ tr ∧ ∀ q ∈ tr, p.1 ≤ q.1 := by
  simpa only [min?_eq, mem_def] using h.head?_eq_some_iff

/-- On a tree with sorted entries, `max?` returns exactly the entry of greatest key. -/
theorem max?_eq_some_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) :
    max? tr = some p ↔ p ∈ tr ∧ ∀ q ∈ tr, q.1 ≤ p.1 := by
  simpa only [max?_eq, mem_def] using h.getLast?_eq_some_iff

/-- In a well-formed tree, `min?` returns exactly the entry of least key. -/
theorem min?_eq_some_iff (h : IsWF t tr) :
    min? tr = some p ↔ p ∈ tr ∧ ∀ q ∈ tr, p.1 ≤ q.1 :=
  min?_eq_some_iff_of_isSortedAssoc h.sorted

/-- In a well-formed tree, `max?` returns exactly the entry of greatest key. -/
theorem max?_eq_some_iff (h : IsWF t tr) :
    max? tr = some p ↔ p ∈ tr ∧ ∀ q ∈ tr, q.1 ≤ p.1 :=
  max?_eq_some_iff_of_isSortedAssoc h.sorted

end Pure

end Cslib.DataStructure.BTree
