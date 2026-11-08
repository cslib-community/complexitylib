/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import Complexity.DataStructure.BTree.Lookup

/-!
# Closed-interval queries in classic B-trees

`rangeM` traverses a B-tree in order, pruning children whose separator bounds exclude the closed
interval. It takes a monadic comparator and a node-visit action, with no order instance; `range`
runs the same algorithm in `Id` with the comparator of a linear order. Each node entered is
visited once, before its triples are scanned. Scanning triples with `rangeRestM` adds no visits,
and empty leaves are never visited. Neither occupancy nor balance is needed for the model
equation, only sorted entries. The constructor equations support evaluation without unfolding
the well-founded recursion.

## Main definitions

* `rangeM`, `rangeRestM`, `range`: the entries with keys in a closed interval, in order.

## Main results

* `Cslib.IsMonadHom.map_rangeM`: a monad morphism commutes with the query.
* `range_eq_of_isSortedAssoc`, `range_eq`: on a tree with sorted entries, and in particular on a
  well-formed tree, `range` is `SortedAssoc.range` on `toList`.
* `mem_range_iff`: range membership is tree membership with the key in the interval.

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Range.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Range.lean).
-/

public section

universe w

namespace Cslib.DataStructure.BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

mutual
/-- Entries in the closed interval, in key order when the comparator decides the key order
and `toList` is sorted. Visit each node on entry; enter a child only when its adjacent
separators permit an entry in the interval. -/
def rangeM (le : α → α → m Bool) (visit : m Unit) (lo hi : α) :
    BTree α β → m (List (α × β))
  | .leaf => pure []
  | .node first rest => do
    visit
    rangeRestM le visit lo hi first rest
termination_by tr => sizeOf tr

/-- Scan a node's remaining triples without additional visits. `first` precedes the triples;
any separator before it has already passed the upper-bound comparison. -/
def rangeRestM (le : α → α → m Bool) (visit : m Unit) (lo hi : α) (first : BTree α β) :
    List (Triple α β) → m (List (α × β))
  | [] => rangeM le visit lo hi first
  | (k, v, c) :: rest => do
    let loLeK ← le lo k
    let below ← if loLeK then rangeM le visit lo hi first else pure []
    if ← le k hi then
      let after ← rangeRestM le visit lo hi c rest
      pure (below ++ (if loLeK then [(k, v)] else []) ++ after)
    else
      pure below
termination_by rest => sizeOf first + sizeOf rest
end

/-- The empty leaf returns no entries and is not visited. -/
theorem rangeM_leaf (le : α → α → m Bool) (visit : m Unit) (lo hi : α) :
    rangeM le visit lo hi (.leaf : BTree α β) = pure [] := by
  rw [rangeM]

/-- A node is visited once before scanning its triples. -/
theorem rangeM_node (le : α → α → m Bool) (visit : m Unit) (lo hi : α)
    (first : BTree α β) (rest : List (Triple α β)) :
    rangeM le visit lo hi (.node first rest) = (do
      visit
      rangeRestM le visit lo hi first rest) := by
  rw [rangeM]

/-- After the last separator, search the last child. -/
theorem rangeRestM_nil (le : α → α → m Bool) (visit : m Unit) (lo hi : α)
    (first : BTree α β) :
    rangeRestM le visit lo hi first [] = rangeM le visit lo hi first := by
  rw [rangeRestM]

/-- A separator bounds the child before it from above and all remaining entries from below.
The scan stops when the separator exceeds `hi`. -/
theorem rangeRestM_cons (le : α → α → m Bool) (visit : m Unit) (lo hi k : α) (v : β)
    (first c : BTree α β) (rest : List (Triple α β)) :
    rangeRestM le visit lo hi first ((k, v, c) :: rest) = (do
      let loLeK ← le lo k
      let below ← if loLeK then rangeM le visit lo hi first else pure []
      if ← le k hi then
        let after ← rangeRestM le visit lo hi c rest
        pure (below ++ (if loLeK then [(k, v)] else []) ++ after)
      else
        pure below) := by
  rw [rangeRestM]

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

mutual
/-- A monad morphism commutes with closed-interval queries. -/
theorem _root_.Cslib.IsMonadHom.map_rangeM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (lo hi : α) (tr : BTree α β) :
    f (rangeM le visit lo hi tr) = rangeM (fun a b => f (le a b)) (f visit) lo hi tr := by
  match tr with
  | .leaf => simp [rangeM_leaf, hf.map_pure]
  | .node first rest =>
    simp [rangeM_node, hf.map_bind, hf.map_rangeRestM le visit lo hi first rest]
termination_by sizeOf tr

/-- A monad morphism commutes with the scan of a node's triples in a closed-interval query. -/
theorem _root_.Cslib.IsMonadHom.map_rangeRestM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (lo hi : α) (first : BTree α β) (rest : List (Triple α β)) :
    f (rangeRestM le visit lo hi first rest) =
      rangeRestM (fun a b => f (le a b)) (f visit) lo hi first rest := by
  match rest with
  | [] => simp [rangeRestM_nil, hf.map_rangeM le visit lo hi first]
  | (k, v, c) :: rest =>
    simp [rangeRestM_cons, hf.map_bind, hf.map_pure, apply_ite f,
      hf.map_rangeM le visit lo hi first, hf.map_rangeRestM le visit lo hi c rest]
termination_by sizeOf first + sizeOf rest
end

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Pure closed-interval query: the `Id` instantiation of `rangeM` with a trivial visit. -/
def range (lo hi : α) (tr : BTree α β) : List (α × β) :=
  Id.run (rangeM leI (pure ()) lo hi tr)

/-- `range` is the `Id` instantiation of `rangeM`. -/
theorem range_def (lo hi : α) :
    range lo hi tr = Id.run (rangeM leI (pure ()) lo hi tr) := (rfl)

/-- The empty tree has no entries in any interval. -/
@[simp] theorem range_leaf (lo hi : α) : range lo hi (.leaf : BTree α β) = [] := by
  simp [range, rangeM_leaf]

/-- A node without keys delegates the query to its only child. -/
@[simp] theorem range_node_nil (lo hi : α) (first : BTree α β) :
    range lo hi (.node first []) = range lo hi first := by
  simp [range, rangeM_node, rangeRestM_nil]

/-- At the first separator, prune the preceding child below `lo`, and stop the remaining
scan above `hi`; include the separator itself exactly when it lies in the closed interval. -/
@[simp] theorem range_node_cons (lo hi k : α) (v : β) (first c : BTree α β)
    (rest : List (Triple α β)) :
    range lo hi (.node first ((k, v, c) :: rest)) =
      (if lo ≤ k then range lo hi first else []) ++
        (if k ≤ hi then (if lo ≤ k then [(k, v)] else []) ++ range lo hi (.node c rest)
         else []) := by
  by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi <;>
    simp [range, rangeM_node, rangeRestM_cons, leI, hlo, hhi]

/-- The output length at the first separator: the preceding child's contribution when the
separator is at least `lo`, and, when it is at most `hi`, the separator itself if it is at least
`lo` and the contribution of the node without its first child and separator. -/
theorem length_range_node_cons (lo hi k : α) (v : β) (first c : BTree α β)
    (rest : List (Triple α β)) :
    (range lo hi (.node first ((k, v, c) :: rest))).length =
      (if lo ≤ k then (range lo hi first).length else 0) +
        (if k ≤ hi then (range lo hi (.node c rest)).length + (if lo ≤ k then 1 else 0)
         else 0) := by
  by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi <;> simp [hlo, hhi]

/-- Model equation: on a tree with sorted entries, the query returns the model's restriction
of `toList` to the closed interval. -/
theorem range_eq_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (lo hi : α) :
    range lo hi tr = SortedAssoc.range lo hi tr.toList := by
  induction tr using (measure (sizeOf : BTree α β → ℕ)).wf.induction with
  | h tr ih =>
    cases tr with
    | leaf => simp
    | node first rest =>
      cases rest with
      | nil =>
        simpa using ih first (by simp_wf; omega) (by simpa using h)
      | cons e rest =>
        obtain ⟨k, v, c⟩ := e
        rw [toList_node, toListRest_cons, List.cons_append] at h ⊢
        obtain ⟨h₁, h₂, hlt, hgt⟩ := List.isSortedAssoc_append_cons_iff.1 h
        have ih₁ := ih first (by simp_wf; omega) h₁
        have ih₂ := ih (.node c rest) (by simp_wf; omega) (by simpa using h₂)
        rw [toList_node] at ih₂
        rw [range_node_cons, SortedAssoc.range_append, SortedAssoc.range_cons]
        -- Separator sortedness justifies pruning the child before the separator or the
        -- entire suffix after it when the corresponding comparison fails.
        have hbelow (hlo : ¬lo ≤ k) : SortedAssoc.range lo hi first.toList = [] :=
          SortedAssoc.range_eq_nil_iff.2 fun p hp =>
            Or.inl ((hlt p hp).trans (lt_of_not_ge hlo))
        have hafter (hhi : ¬k ≤ hi) :
            SortedAssoc.range lo hi (c.toList ++ toListRest rest) = [] :=
          SortedAssoc.range_eq_nil_iff.2 fun p hp =>
            Or.inr ((lt_of_not_ge hhi).trans (hgt p hp))
        by_cases hlo : lo ≤ k
        · by_cases hhi : k ≤ hi
          · simp [hlo, hhi, ih₁, ih₂]
          · rw [hafter hhi]
            simp [hlo, hhi, ih₁]
        · rw [hbelow hlo]
          by_cases hhi : k ≤ hi
          · simp [hlo, hhi, ih₂]
          · rw [hafter hhi]
            simp [hlo, hhi]

/-- Model equation for closed-interval queries on well-formed trees. -/
theorem range_eq (h : IsWF t tr) (lo hi : α) :
    range lo hi tr = SortedAssoc.range lo hi tr.toList :=
  range_eq_of_isSortedAssoc h.sorted lo hi

/-- On a tree with sorted entries, the output contains exactly the tree's entries whose keys
lie in the closed interval. -/
@[simp] theorem mem_range_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (lo hi : α)
    (p : α × β) :
    p ∈ range lo hi tr ↔ p ∈ tr ∧ lo ≤ p.1 ∧ p.1 ≤ hi := by
  simp only [range_eq_of_isSortedAssoc h, SortedAssoc.mem_range_iff, mem_def]

/-- In a well-formed tree, range membership is tree membership with the closed-interval
condition on the key. -/
theorem mem_range_iff (h : IsWF t tr) (lo hi : α) (p : α × β) :
    p ∈ range lo hi tr ↔ p ∈ tr ∧ lo ≤ p.1 ∧ p.1 ≤ hi :=
  mem_range_iff_of_isSortedAssoc h.sorted lo hi p

end Pure

end Cslib.DataStructure.BTree
