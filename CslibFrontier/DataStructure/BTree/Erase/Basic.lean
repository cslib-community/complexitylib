/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Insert

/-!
# Erasure from classic B-trees

Erasure in the B-trees of `Cslib.DataStructure.BTree`, by the bottom-up algorithm of the
functional literature, the mirror image of `Cslib.DataStructure.BTree.Insert`. The repair follows
the functional deletion of [Mundler2021]: `mergeSplit` merges two nodes and splits the result
with the insertion splitter, as its `node⇩i` does, and `rebalanceRightM` and `rebalanceLastM` are
its `rebalance_middle_tree` and `rebalance_last_tree`. [Mundler2021] replaces an interior key by
its predecessor; this version uses the successor, which sits in the same triple of the
interleaved representation.

Erasure from a subtree may leave it one key short (`underflows`); the parent repairs such a child
against an adjacent sibling by merging the two around their separator and splitting the result
again when it has more than `2 * t - 1` keys (`mergeSplit`, through `InsertResult.ofNode`). That
single repair covers both borrowing and merging in [CLRS2009], Chapter 18. A child is repaired
against its right sibling, and the last child against its left one. An empty root collapses into
its only child (`collapse`), so the height falls only there. A key found in an interior node is
replaced by its successor, the least entry of the child after it, which `popMinM` removes with
the same repairs; erasure is not restricted to leaves.

Each operation is defined once over an arbitrary monad `m`, with a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`. `eraseSubtreeM` and `eraseRestM`
are the recursion of `eraseM`, with the scan and the equality test of `lookupM`. `visit` fires
on entering each node of the search path, including the path of `popMinM` to the successor, and
once more for each sibling a repair inspects, so a descent visits at most two nodes per level.
The pure operations are the `Id` instantiations with `leI` and `visit := pure ()`.
`eraseRestM` takes the child before the triples together with the computation of its erasure, so
that the definitions are structurally recursive and `@[expose]`d: `decide` evaluates erasure on
concrete trees from other modules, and the monadic constructor equations hold by `rfl`. Costs are
not stated here.

## Main definitions

* `underflows`, `mergeSplit`, `collapse`: underflow, the sibling repair and the root collapse.
* `rebalanceRightM`, `rebalanceLastM`, `popMinM`: repairs and removal of the least entry.
* `eraseSubtreeM`, `eraseRestM`, `eraseM`, `erase`: erasure.
* `Underfull`, `EraseFits`: the shape of a child after erasure and the invariant of a result.

## Main results

* `Cslib.IsMonadHom.map_eraseM`: a monad morphism commutes with erasure.
* `toList_erase_of_isSortedAssoc`, `toList_erase`: the model equation, `toList` of the erasure
  is `SortedAssoc.erase` on `toList`.
* `eraseFits_eraseSubtree`: the shape invariant.
* `IsWF.erase`: erasure preserves well-formedness.
* `height_erase`: the height stays or falls by one.
* `size_erase`, `lookup_erase`: size and lookup after erasure.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]
* [N. Mündler, *A Verified Imperative Implementation of B-Trees*][Mundler2021]

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Erase/Basic.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Erase/Basic.lean).
-/

public section

universe w

namespace Cslib.DataStructure.BTree

section Structure

variable {α β : Type}

/-- A non-empty node with fewer than `t - 1` keys: a child that erasure left one key short. -/
@[expose] def underflows (t : ℕ) : BTree α β → Bool
  | .leaf => false
  | .node _ rest => decide (rest.length < t - 1)

/-- Merge two adjacent siblings around their separator into one node, split again by
`InsertResult.ofNode` when it has more than `2 * t - 1` keys. -/
@[expose] def mergeSplit (t : ℕ) : BTree α β → α → β → BTree α β → InsertResult α β
  | .node lf lr, k, v, .node rf rr => .ofNode t lf (lr ++ (k, v, rf) :: rr)
  | l, k, v, r => .split l k v r

/-- Drop an empty root: a node without keys is replaced by its only child. -/
@[expose] def collapse : BTree α β → BTree α β
  | .node first [] => first
  | tr => tr

end Structure

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Repair a child `c` followed by its right sibling `s` with separator `(k, v)` and the
triples `rest`: if `c` underflows, inspect `s` (one visit) and merge them. -/
@[expose] def rebalanceRightM (t : ℕ) (visit : m Unit) (c : BTree α β) (k : α) (v : β)
    (s : BTree α β) (rest : List (Triple α β)) :
    m (BTree α β × List (Triple α β)) :=
  if underflows t c then do
    visit
    pure ((mergeSplit t c k v s).withRest rest)
  else pure (c, (k, v, s) :: rest)

/-- Repair a last child `c` after its left sibling `prev` with separator `(k, v)`: if `c`
underflows, inspect `prev` (one visit) and merge them. -/
@[expose] def rebalanceLastM (t : ℕ) (visit : m Unit) (prev : BTree α β) (k : α) (v : β)
    (c : BTree α β) : m (BTree α β × List (Triple α β)) :=
  if underflows t c then do
    visit
    pure ((mergeSplit t prev k v c).withRest [])
  else pure (prev, [(k, v, c)])

/-- Repair against the right sibling visits and merges exactly when the child underflows. -/
theorem rebalanceRightM_def (t : ℕ) (visit : m Unit) (c : BTree α β) (k : α) (v : β)
    (s : BTree α β) (rest : List (Triple α β)) :
    rebalanceRightM t visit c k v s rest =
      if underflows t c then (do visit; pure ((mergeSplit t c k v s).withRest rest))
      else pure (c, (k, v, s) :: rest) := rfl

/-- Repair against the left sibling visits and merges exactly when the last child underflows. -/
theorem rebalanceLastM_def (t : ℕ) (visit : m Unit) (prev : BTree α β) (k : α) (v : β)
    (c : BTree α β) :
    rebalanceLastM t visit prev k v c =
      if underflows t c then (do visit; pure ((mergeSplit t prev k v c).withRest []))
      else pure (prev, [(k, v, c)]) := rfl

/-- Remove the least entry of a subtree, repairing on the way back up; the result may
underflow by one key. -/
@[expose] def popMinM (t : ℕ) (visit : m Unit) :
    BTree α β → m (Option ((α × β) × BTree α β))
  | .leaf => pure none
  | .node first rest => do
    visit
    match ← popMinM t visit first, rest with
    | none, [] => pure none
    | none, (k, v, c) :: rest' => pure (some ((k, v), .node c rest'))
    | some (e, first'), [] => pure (some (e, .node first' []))
    | some (e, first'), (k, v, c) :: rest' => do
      let p ← rebalanceRightM t visit first' k v c rest'
      pure (some (e, .node p.1 p.2))

mutual
/-- Erasure from a subtree; the result may underflow by one key. -/
@[expose] def eraseSubtreeM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BTree α β → m (BTree α β)
  | .leaf => pure .leaf
  | .node first rest => do
    visit
    let p ← eraseRestM t le visit k first (eraseSubtreeM t le visit k first) rest
    pure (.node p.1 p.2)

/-- Erasure among the triples after the child `prev`, whose erasure is `prevErased`. -/
@[expose] def eraseRestM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BTree α β) (prevErased : m (BTree α β)) :
    List (Triple α β) → m (BTree α β × List (Triple α β))
  | [] => do return (← prevErased, [])
  | (k', v', c) :: rest => do
    if ← le k k' then
      if ← le k' k then
        match ← popMinM t visit c with
        | none => pure (prev, rest)
        | some ((k₂, v₂), c') =>
          match rest with
          | [] => rebalanceLastM t visit prev k₂ v₂ c'
          | (k₃, v₃, c₃) :: rest₃ => do
            let p ← rebalanceRightM t visit c' k₃ v₃ c₃ rest₃
            pure (prev, (k₂, v₂, p.1) :: p.2)
      else
        rebalanceRightM t visit (← prevErased) k' v' c rest
    else
      match rest with
      | [] => do rebalanceLastM t visit prev k' v' (← eraseSubtreeM t le visit k c)
      | _ :: _ => do
        let p ← eraseRestM t le visit k c (eraseSubtreeM t le visit k c) rest
        pure (prev, (k', v', p.1) :: p.2)
end

/-- Remove the entry with key `k`, if any, from a B-tree of minimum degree `t`, comparing with
`le` and calling `visit` on each node of the search path and on each sibling a repair inspects;
an emptied root collapses into its only child. -/
@[expose] def eraseM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (tr : BTree α β) : m (BTree α β) := do
  return collapse (← eraseSubtreeM t le visit k tr)

/-- Erasure is erasure from the root subtree followed by collapsing an empty root. -/
theorem eraseM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (tr : BTree α β) :
    eraseM t le visit k tr = (do return collapse (← eraseSubtreeM t le visit k tr)) := rfl

/-- Erasure from the empty tree is the empty tree, without a visit. -/
@[simp] theorem eraseSubtreeM_leaf (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) :
    eraseSubtreeM t le visit k (.leaf : BTree α β) = pure .leaf := rfl

/-- Erasure from the empty tree is the empty tree, without a visit. -/
@[simp] theorem eraseM_leaf [LawfulMonad m] (t : ℕ) (le : α → α → m Bool) (visit : m Unit)
    (k : α) : eraseM t le visit k (.leaf : BTree α β) = pure .leaf := by
  simp [eraseM_def, collapse]

/-- A node is visited once on entry, then its triples are searched. -/
theorem eraseSubtreeM_node (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (first : BTree α β) (rest : List (Triple α β)) :
    eraseSubtreeM t le visit k (.node first rest) = (do
      visit
      let p ← eraseRestM t le visit k first (eraseSubtreeM t le visit k first) rest
      pure (.node p.1 p.2)) := rfl

/-- Past the last triple, the erasure of the preceding child is the result. -/
theorem eraseRestM_nil (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BTree α β) (prevErased : m (BTree α β)) :
    eraseRestM t le visit k prev prevErased [] = (do return (← prevErased, [])) := rfl

/-- At a triple: on equality, replace the entry by the least entry of its child and repair the
child; below the key, erase from the preceding child and repair it against this child; above
it, move on, repairing the last child against its left sibling. -/
theorem eraseRestM_cons (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BTree α β) (prevErased : m (BTree α β)) (k' : α) (v' : β) (c : BTree α β)
    (rest : List (Triple α β)) :
    eraseRestM t le visit k prev prevErased ((k', v', c) :: rest) = (do
      if ← le k k' then
        if ← le k' k then
          match ← popMinM t visit c with
          | none => pure (prev, rest)
          | some ((k₂, v₂), c') =>
            match rest with
            | [] => rebalanceLastM t visit prev k₂ v₂ c'
            | (k₃, v₃, c₃) :: rest₃ => do
              let p ← rebalanceRightM t visit c' k₃ v₃ c₃ rest₃
              pure (prev, (k₂, v₂, p.1) :: p.2)
        else
          rebalanceRightM t visit (← prevErased) k' v' c rest
      else
        match rest with
        | [] => do rebalanceLastM t visit prev k' v' (← eraseSubtreeM t le visit k c)
        | _ :: _ => do
          let p ← eraseRestM t le visit k c (eraseSubtreeM t le visit k c) rest
          pure (prev, (k', v', p.1) :: p.2)) := rfl

/-- The least entry of the empty tree does not exist, and nothing is visited. -/
@[simp] theorem popMinM_leaf (t : ℕ) (visit : m Unit) :
    popMinM t visit (.leaf : BTree α β) = pure none := rfl

/-- A node is visited once on entry, its first child searched, and the result repaired. -/
theorem popMinM_node (t : ℕ) (visit : m Unit) (first : BTree α β)
    (rest : List (Triple α β)) :
    popMinM t visit (.node first rest) = (do
      visit
      match ← popMinM t visit first, rest with
      | none, [] => pure none
      | none, (k, v, c) :: rest' => pure (some ((k, v), .node c rest'))
      | some (e, first'), [] => pure (some (e, .node first' []))
      | some (e, first'), (k, v, c) :: rest' => do
        let p ← rebalanceRightM t visit first' k v c rest'
        pure (some (e, .node p.1 p.2))) := rfl

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the repair against the right sibling. -/
theorem _root_.Cslib.IsMonadHom.map_rebalanceRightM (hf : IsMonadHom m n f) (t : ℕ)
    (visit : m Unit) (c : BTree α β) (k : α) (v : β) (s : BTree α β)
    (rest : List (Triple α β)) :
    f (rebalanceRightM t visit c k v s rest) = rebalanceRightM t (f visit) c k v s rest := by
  simp [rebalanceRightM_def, apply_ite f, hf.map_bind, hf.map_pure]

/-- A monad morphism commutes with the repair against the left sibling. -/
theorem _root_.Cslib.IsMonadHom.map_rebalanceLastM (hf : IsMonadHom m n f) (t : ℕ)
    (visit : m Unit) (prev : BTree α β) (k : α) (v : β) (c : BTree α β) :
    f (rebalanceLastM t visit prev k v c) = rebalanceLastM t (f visit) prev k v c := by
  simp [rebalanceLastM_def, apply_ite f, hf.map_bind, hf.map_pure]

/-- A monad morphism commutes with the removal of the least entry of a subtree. -/
theorem _root_.Cslib.IsMonadHom.map_popMinM (hf : IsMonadHom m n f) (t : ℕ) (visit : m Unit)
    (tr : BTree α β) : f (popMinM t visit tr) = popMinM t (f visit) tr := by
  match tr with
  | .leaf => simp [hf.map_pure]
  | .node first rest =>
    simp only [popMinM_node, hf.map_bind, hf.map_popMinM t visit first]
    refine bind_congr fun _ => bind_congr fun o => ?_
    rcases o with _ | ⟨e, first'⟩ <;> rcases rest with _ | ⟨⟨k, v, c⟩, rest'⟩ <;>
      simp [hf.map_bind, hf.map_pure, hf.map_rebalanceRightM]
termination_by sizeOf tr

mutual
/-- A monad morphism commutes with erasure from a subtree. -/
theorem _root_.Cslib.IsMonadHom.map_eraseSubtreeM (hf : IsMonadHom m n f) (t : ℕ)
    (le : α → α → m Bool) (visit : m Unit) (k : α) (tr : BTree α β) :
    f (eraseSubtreeM t le visit k tr) = eraseSubtreeM t (fun a b => f (le a b)) (f visit) k tr := by
  match tr with
  | .leaf => simp [hf.map_pure]
  | .node first rest =>
    simp [eraseSubtreeM_node, hf.map_bind, hf.map_pure,
      hf.map_eraseRestM t le visit k first _ rest, hf.map_eraseSubtreeM t le visit k first]
termination_by sizeOf tr

/-- A monad morphism commutes with erasure among the triples of a node. -/
theorem _root_.Cslib.IsMonadHom.map_eraseRestM (hf : IsMonadHom m n f) (t : ℕ)
    (le : α → α → m Bool) (visit : m Unit) (k : α) (prev : BTree α β)
    (prevErased : m (BTree α β)) (rest : List (Triple α β)) :
    f (eraseRestM t le visit k prev prevErased rest) =
      eraseRestM t (fun a b => f (le a b)) (f visit) k prev (f prevErased) rest := by
  match rest with
  | [] => simp [eraseRestM_nil, hf.map_bind, hf.map_pure]
  | (k', v', c) :: rest =>
    simp only [eraseRestM_cons, hf.map_bind]
    refine bind_congr fun b => ?_
    cases b
    · rcases rest with _ | ⟨e, rest⟩
      · simp [hf.map_bind, hf.map_rebalanceLastM, hf.map_eraseSubtreeM t le visit k c]
      · simp [hf.map_bind, hf.map_pure, hf.map_eraseSubtreeM t le visit k c,
          hf.map_eraseRestM t le visit k c _ (e :: rest)]
    · simp only [↓reduceIte, hf.map_bind]
      refine bind_congr fun b => ?_
      cases b
      · simp [hf.map_bind, hf.map_rebalanceRightM]
      · simp only [↓reduceIte, hf.map_bind, hf.map_popMinM]
        refine bind_congr fun o => ?_
        rcases o with _ | ⟨⟨k₂, v₂⟩, c'⟩ <;> rcases rest with _ | ⟨⟨k₃, v₃, c₃⟩, rest₃⟩ <;>
          simp [hf.map_bind, hf.map_pure, hf.map_rebalanceLastM, hf.map_rebalanceRightM]
termination_by sizeOf rest
end

/-- A monad morphism commutes with erasure. -/
theorem _root_.Cslib.IsMonadHom.map_eraseM (hf : IsMonadHom m n f) (t : ℕ)
    (le : α → α → m Bool) (visit : m Unit) (k : α) (tr : BTree α β) :
    f (eraseM t le visit k tr) = eraseM t (fun a b => f (le a b)) (f visit) k tr := by
  simp [eraseM_def, hf.map_bind, hf.map_pure, hf.map_eraseSubtreeM]

end Transfer

section PureStructure

variable {α β : Type} {t : ℕ}

/-- Pure repair of a child against its right sibling. -/
@[expose] def rebalanceRight (t : ℕ) (c : BTree α β) (k : α) (v : β) (s : BTree α β)
    (rest : List (Triple α β)) : BTree α β × List (Triple α β) :=
  Id.run (rebalanceRightM t (pure ()) c k v s rest)

/-- Pure repair of a last child against its left sibling. -/
@[expose] def rebalanceLast (t : ℕ) (prev : BTree α β) (k : α) (v : β) (c : BTree α β) :
    BTree α β × List (Triple α β) :=
  Id.run (rebalanceLastM t (pure ()) prev k v c)

/-- Pure removal of the least entry. -/
@[expose] def popMin (t : ℕ) (tr : BTree α β) : Option ((α × β) × BTree α β) :=
  Id.run (popMinM t (pure ()) tr)

/-- `rebalanceRight` is the `Id` instantiation of `rebalanceRightM`. -/
theorem rebalanceRight_def (c : BTree α β) (k : α) (v : β) (s : BTree α β)
    (rest : List (Triple α β)) :
    rebalanceRight t c k v s rest = Id.run (rebalanceRightM t (pure ()) c k v s rest) := (rfl)

/-- `rebalanceLast` is the `Id` instantiation of `rebalanceLastM`. -/
theorem rebalanceLast_def (prev : BTree α β) (k : α) (v : β) (c : BTree α β) :
    rebalanceLast t prev k v c = Id.run (rebalanceLastM t (pure ()) prev k v c) := (rfl)

/-- `popMin` is the `Id` instantiation of `popMinM`. -/
theorem popMin_def (tr : BTree α β) : popMin t tr = Id.run (popMinM t (pure ()) tr) := (rfl)

/-- Pure repair against the right sibling merges only an underflowing child. -/
theorem rebalanceRight_eq_ite (c : BTree α β) (k : α) (v : β) (s : BTree α β)
    (rest : List (Triple α β)) :
    rebalanceRight t c k v s rest =
      if underflows t c then (mergeSplit t c k v s).withRest rest else (c, (k, v, s) :: rest) := by
  unfold rebalanceRight rebalanceRightM
  -- as in `popMin_node`, each branch in `Id` is the pure branch by definition
  split <;> rfl

/-- Pure repair against the left sibling merges only an underflowing last child. -/
theorem rebalanceLast_eq_ite (prev : BTree α β) (k : α) (v : β) (c : BTree α β) :
    rebalanceLast t prev k v c =
      if underflows t c then (mergeSplit t prev k v c).withRest [] else (prev, [(k, v, c)]) := by
  unfold rebalanceLast rebalanceLastM
  -- as in `popMin_node`, each branch in `Id` is the pure branch by definition
  split <;> rfl

/-- The empty tree has no least entry. -/
@[simp] theorem popMin_leaf : popMin t (.leaf : BTree α β) = none := rfl

/-- Removing the least entry from a node: from its first child, repaired, or the node's first
entry when the first child has none. -/
theorem popMin_node (first : BTree α β) (rest : List (Triple α β)) :
    popMin t (.node first rest) =
      match popMin t first, rest with
      | none, [] => none
      | none, (k, v, c) :: rest' => some ((k, v), .node c rest')
      | some (e, first'), [] => some (e, .node first' [])
      | some (e, first'), (k, v, c) :: rest' =>
        let p := rebalanceRight t first' k v c rest'
        some (e, .node p.1 p.2) := by
  -- In `Id`, bind is application and `pure` is the identity, so after unfolding, each branch of
  -- the monadic `match` is the corresponding pure branch by definition.
  simp only [popMin, popMinM, rebalanceRight]
  rcases popMinM t (pure ()) first with _ | ⟨e, first'⟩ <;>
    rcases rest with _ | ⟨⟨k, v, c⟩, rest⟩ <;> rfl

/-- Merging keeps the entries of both siblings and their separator. -/
@[simp] theorem toList_mergeSplit (l : BTree α β) (k : α) (v : β) (r : BTree α β) :
    (mergeSplit t l k v r).toList = l.toList ++ (k, v) :: r.toList := by
  unfold mergeSplit
  split
  · simp
  · rfl

/-- Repair against the right sibling keeps the entries. -/
theorem toList_rebalanceRight (c : BTree α β) (k : α) (v : β) (s : BTree α β)
    (rest : List (Triple α β)) :
    (rebalanceRight t c k v s rest).1.toList ++ toListRest (rebalanceRight t c k v s rest).2 =
      c.toList ++ toListRest ((k, v, s) :: rest) := by
  rw [rebalanceRight_eq_ite]
  split
  · rw [← InsertResult.toList_withRest, toList_mergeSplit, toListRest_cons]
    simp
  · rfl

/-- Repair against the left sibling keeps the entries. -/
theorem toList_rebalanceLast (prev : BTree α β) (k : α) (v : β) (c : BTree α β) :
    (rebalanceLast t prev k v c).1.toList ++ toListRest (rebalanceLast t prev k v c).2 =
      prev.toList ++ toListRest [(k, v, c)] := by
  rw [rebalanceLast_eq_ite]
  split
  · rw [← InsertResult.toList_withRest, toList_mergeSplit, toListRest_cons]
    simp
  · rfl

/-- Removing the least entry: `none` exactly on a tree without entries, and otherwise the
first entry followed by the entries of the rest. -/
theorem toList_popMin {tr : BTree α β} :
    (popMin t tr = none → tr.toList = []) ∧
      ∀ e tr', popMin t tr = some (e, tr') → tr.toList = e :: tr'.toList := by
  induction tr with
  | leaf => simp
  | node first rest ihf _ =>
    rw [popMin_node]
    rcases hf : popMin t first with _ | ⟨e, first'⟩ <;>
      rcases rest with _ | ⟨⟨k, v, c⟩, rest⟩
    · simp [ihf.1 hf]
    · simp [ihf.1 hf]
    · simp [ihf.2 _ _ hf]
    · refine ⟨by simp, fun e' tr' h => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [toList_node, toList_node, toList_rebalanceRight, ihf.2 _ _ hf, List.cons_append]

/-- Collapsing an empty root keeps the entries. -/
@[simp] theorem toList_collapse (tr : BTree α β) : (collapse tr).toList = tr.toList := by
  unfold collapse
  split
  · simp
  · rfl

/-! ### Shape -/

/-- A subtree of height `h` that may be one key short: balanced, with occupied children, at
most `2 * t - 1` keys, and at least `t - 2` keys when it is a node. -/
structure Underfull (t h : ℕ) (c : BTree α β) : Prop where
  /-- The subtree is balanced. -/
  balanced : Balanced c
  /-- The subtree has height `h`. -/
  height_eq : c.height = h
  /-- Every child of the root is occupied. -/
  children_occupied : ∀ x ∈ c.children, Occupied t x
  /-- The root has at most `2 * t - 1` keys. -/
  rootKeys_le : c.rootKeys ≤ 2 * t - 1
  /-- A node root has at least `t - 2` keys. -/
  le_rootKeys : c ≠ .leaf → t - 2 ≤ c.rootKeys

/-- The shape of the result `c` of erasing from `tr`: balanced, of the same height, with
occupied children, and at most one root key fewer. -/
structure EraseFits (t : ℕ) (tr c : BTree α β) : Prop where
  /-- The result is balanced. -/
  balanced : Balanced c
  /-- The result has the height of `tr`. -/
  height_eq : c.height = tr.height
  /-- Every child of the result's root is occupied. -/
  children_occupied : ∀ x ∈ c.children, Occupied t x
  /-- The result's root has no more keys than that of `tr`. -/
  rootKeys_le : c.rootKeys ≤ tr.rootKeys
  /-- The result's root has at most one key fewer than that of `tr`. -/
  rootKeys_le_succ : tr.rootKeys ≤ c.rootKeys + 1

/-- A repaired child, or a repaired pair of children around a separator, all good. -/
def InsertResult.Mended (t h : ℕ) : InsertResult α β → Prop
  | .tree c => Good t h c
  | .split l _ _ r => Good t h l ∧ Good t h r

/-- A good subtree is at most one key short. -/
theorem Good.underfull {c : BTree α β} {h : ℕ} (hc : Good t h c) : Underfull t h c :=
  ⟨hc.balanced, hc.height_eq, fun _ hx => hc.occupied.of_mem_children hx, hc.occupied.rootKeys_le,
    fun hne => by have := hc.occupied.le_rootKeys hne; omega⟩

/-- A good tree of positive height is a node. -/
theorem Good.ne_leaf {c : BTree α β} {h : ℕ} (hc : Good t h c) (hh : 1 ≤ h) : c ≠ .leaf := by
  rintro rfl
  have := hc.height_eq
  simp at this
  omega

/-- A subtree that does not underflow is occupied. -/
theorem Underfull.occupied {c : BTree α β} {h : ℕ} (hc : Underfull t h c)
    (hu : underflows t c = false) : Occupied t c := by
  have ho := hc.children_occupied
  have hk := hc.rootKeys_le
  cases c with
  | leaf => exact .leaf
  | node f r =>
    simp only [underflows, decide_eq_false_iff_not, not_lt] at hu
    simp only [rootKeys_node] at hk
    exact .node hu hk (ho f List.mem_cons_self)
      fun e he => ho _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))

/-- A subtree that does not underflow is good. -/
theorem Underfull.good {c : BTree α β} {h : ℕ} (hc : Underfull t h c)
    (hu : underflows t c = false) : Good t h c :=
  ⟨hc.balanced, hc.height_eq, hc.occupied hu⟩

/-- Only a node underflows. -/
theorem ne_leaf_of_underflows {c : BTree α β} (hu : underflows t c = true) : c ≠ .leaf := by
  rintro rfl
  simp [underflows] at hu

/-- A subtree one key short that underflows has exactly `t - 2` keys. -/
theorem Underfull.rootKeys_eq_of_underflows {c : BTree α β} {h : ℕ} (hc : Underfull t h c)
    (hu : underflows t c = true) : c.rootKeys = t - 2 := by
  have := hc.le_rootKeys (ne_leaf_of_underflows hu)
  cases c with
  | leaf => simp [underflows] at hu
  | node f r =>
    simp only [underflows, decide_eq_true_eq] at hu
    simp only [rootKeys_node] at this ⊢
    omega

/-- A subtree that underflows has positive height. -/
theorem Underfull.one_le_height_of_underflows {c : BTree α β} {h : ℕ} (hc : Underfull t h c)
    (hu : underflows t c = true) : 1 ≤ h := by
  have hne := ne_leaf_of_underflows hu
  rw [← hc.height_eq]
  exact Nat.one_le_iff_ne_zero.2 fun h0 => hne (height_eq_zero_iff.1 h0)

/-- Erasure from an occupied subtree leaves it at most one key short. -/
theorem EraseFits.underfull {tr c : BTree α β} (hf : EraseFits t tr c) (ho : Occupied t tr) :
    Underfull t tr.height c := by
  refine ⟨hf.balanced, hf.height_eq, hf.children_occupied, hf.rootKeys_le.trans ho.rootKeys_le,
    fun hne => ?_⟩
  have htr : tr ≠ .leaf := by
    rintro rfl
    exact hne (height_eq_zero_iff.1 (by simpa using hf.height_eq))
  have := ho.le_rootKeys htr
  have := hf.rootKeys_le_succ
  omega

/-- Erasure from a good subtree leaves it at most one key short, given the shape of the erasure
under the occupancy facts a good subtree provides. -/
theorem Good.underfull_of_eraseFits (ht : 2 ≤ t) {c c' : BTree α β} {h : ℕ} (hc : Good t h c)
    (hf : (∀ x ∈ c.children, Occupied t x) → (c ≠ .leaf → 1 ≤ c.rootKeys) → EraseFits t c c') :
    Underfull t h c' :=
  hc.height_eq ▸ (hf (fun _ hx => hc.occupied.of_mem_children hx)
    (hc.occupied.one_le_rootKeys ht)).underfull hc.occupied

/-- Re-splitting a node of between `t - 1` and `2 * t - 1 + t + 1` keys (`3 * t` when `1 ≤ t`)
over good children gives good results. -/
theorem InsertResult.mended_ofNode {first : BTree α β}
    {rest : List (Triple α β)} {h : ℕ} (hf : Good t h first)
    (hr : ∀ e ∈ rest, Good t h e.child) (hlo : t - 1 ≤ rest.length)
    (hhi : rest.length ≤ 2 * t - 1 + t + 1) :
    (InsertResult.ofNode t first rest).Mended t (h + 1) := by
  by_cases hle : rest.length ≤ 2 * t - 1
  · simp only [InsertResult.ofNode, hle, ↓reduceIte]
    exact good_node hf hr hlo hle
  · obtain ⟨l, k, v, r, heq, hl, hr'⟩ :=
      InsertResult.exists_good_split_ofNode hf hr (by omega) (by omega)
    rw [heq]
    exact ⟨hl, hr'⟩

/-- Placing a repaired result among good triples keeps them good, adding at most one key. -/
theorem InsertResult.mended_withRest {x : InsertResult α β} {h : ℕ} (hx : x.Mended t h)
    {rest : List (Triple α β)} (hr : ∀ e ∈ rest, Good t h e.child) :
    Good t h (x.withRest rest).1 ∧ (∀ e ∈ (x.withRest rest).2, Good t h e.child) ∧
      rest.length ≤ (x.withRest rest).2.length ∧
      (x.withRest rest).2.length ≤ rest.length + 1 := by
  cases x with
  | tree c => exact ⟨hx, hr, le_rfl, Nat.le_succ _⟩
  | split l k v r =>
    exact ⟨hx.1, List.forall_mem_cons.2 ⟨hx.2, hr⟩, Nat.le_succ _, le_rfl⟩

/-- Merging two adjacent nodes of height `h + 1` with between `t - 2` and `3 * t - 3` keys in
total gives good results. -/
theorem mended_mergeSplit {l r : BTree α β} {h : ℕ} (hl : Underfull t (h + 1) l)
    (hr : Underfull t (h + 1) r) (hl₀ : l ≠ .leaf) (hr₀ : r ≠ .leaf) (k : α) (v : β)
    (hlo : t - 1 ≤ l.rootKeys + r.rootKeys + 1) (hhi : l.rootKeys + r.rootKeys + 1 ≤ 3 * t - 2) :
    (mergeSplit t l k v r).Mended t (h + 1) := by
  cases l with
  | leaf => exact absurd rfl hl₀
  | node lf lr =>
  cases r with
  | leaf => exact absurd rfl hr₀
  | node rf rr =>
  have hgood : ∀ {c x : BTree α β}, Underfull t (h + 1) c → x ∈ c.children → Good t h x :=
    fun {c x} hc hx => ⟨hc.balanced.of_mem_children hx,
      by have := hc.balanced.height_of_mem_children hx; rw [hc.height_eq] at this; omega,
      hc.children_occupied x hx⟩
  simp only [rootKeys_node] at hlo hhi
  refine InsertResult.mended_ofNode (hgood hl List.mem_cons_self) (fun e he => ?_)
    (by simp; omega) (by simp; omega)
  rcases List.mem_append.1 he with he | he
  · exact hgood hl (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
  · rcases List.mem_cons.1 he with rfl | he
    · exact hgood hr List.mem_cons_self
    · exact hgood hr (List.mem_cons_of_mem _ (List.mem_map_of_mem he))

/-- Repair against the right sibling: the results are good, with one key fewer or none. -/
theorem good_rebalanceRight (ht : 2 ≤ t) {c s : BTree α β} {h : ℕ} (hc : Underfull t h c)
    (hs : Good t h s) (k : α) (v : β) {rest : List (Triple α β)}
    (hr : ∀ e ∈ rest, Good t h e.child) :
    Good t h (rebalanceRight t c k v s rest).1 ∧
      (∀ e ∈ (rebalanceRight t c k v s rest).2, Good t h e.child) ∧
      rest.length ≤ (rebalanceRight t c k v s rest).2.length ∧
      (rebalanceRight t c k v s rest).2.length ≤ rest.length + 1 := by
  rw [rebalanceRight_eq_ite]
  split
  · next hu =>
    have hck := hc.rootKeys_eq_of_underflows hu
    have hh := hc.one_le_height_of_underflows hu
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    have hs₀ := hs.ne_leaf hh
    have := hs.occupied.le_rootKeys hs₀
    have := hs.occupied.rootKeys_le
    exact InsertResult.mended_withRest (mended_mergeSplit hc hs.underfull
      (ne_leaf_of_underflows hu) hs₀ k v (by omega) (by omega)) hr
  · next hu =>
    exact ⟨hc.good (by simpa using hu), List.forall_mem_cons.2 ⟨hs, hr⟩, Nat.le_succ _, le_rfl⟩

/-- Repair of a last child against its left sibling: the results are good, with at most one
triple. -/
theorem good_rebalanceLast (ht : 2 ≤ t) {prev c : BTree α β} {h : ℕ} (hp : Good t h prev)
    (hc : Underfull t h c) (k : α) (v : β) :
    Good t h (rebalanceLast t prev k v c).1 ∧
      (∀ e ∈ (rebalanceLast t prev k v c).2, Good t h e.child) ∧
      (rebalanceLast t prev k v c).2.length ≤ 1 := by
  rw [rebalanceLast_eq_ite]
  split
  · next hu =>
    have hck := hc.rootKeys_eq_of_underflows hu
    have hh := hc.one_le_height_of_underflows hu
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    have hp₀ := hp.ne_leaf hh
    have := hp.occupied.le_rootKeys hp₀
    have := hp.occupied.rootKeys_le
    obtain ⟨h₁, h₂, -, h₃⟩ := InsertResult.mended_withRest (rest := [])
      (mended_mergeSplit hp.underfull hc hp₀ (ne_leaf_of_underflows hu) k v (by omega)
        (by omega)) (by simp)
    exact ⟨h₁, h₂, by simpa using h₃⟩
  · next hu =>
    exact ⟨hp, List.forall_mem_cons.2 ⟨hc.good (by simpa using hu), by simp⟩, by simp⟩

/-- Shape of the removal of the least entry. -/
theorem eraseFits_popMin (ht : 2 ≤ t) {tr : BTree α β} (hb : Balanced tr)
    (ho : ∀ c ∈ tr.children, Occupied t c) (hpos : tr ≠ .leaf → 1 ≤ tr.rootKeys)
    {e : α × β} {tr' : BTree α β} (hp : popMin t tr = some (e, tr')) : EraseFits t tr tr' := by
  induction tr generalizing e tr' with
  | leaf => simp at hp
  | node first rest ihf _ =>
    obtain ⟨hf, hr⟩ := good_of_balanced_node hb ho
    have hh := hb.height_node
    have hpos := hpos (by simp)
    simp only [rootKeys_node] at hpos
    rw [popMin_node] at hp
    rcases hpf : popMin t first with _ | ⟨e₁, first'⟩ <;>
      rcases rest with _ | ⟨⟨k, v, c⟩, rest⟩
    · simp at hpos
    · -- the first child is empty: the node gives up its first entry
      simp only [hpf, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨-, rfl⟩ := hp
      obtain ⟨hc, hrest⟩ := List.forall_mem_cons.1 hr
      obtain ⟨hb', hh', hco⟩ := node_of_good hc hrest
      exact ⟨hb', by rw [hh', hh], hco, by simp, by simp⟩
    · simp at hpos
    · -- the least entry comes from the first child, which is then repaired
      simp only [hpf, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨-, rfl⟩ := hp
      obtain ⟨hc, hrest⟩ := List.forall_mem_cons.1 hr
      have hu := hf.underfull_of_eraseFits ht fun ho hpos => ihf hf.balanced ho hpos hpf
      obtain ⟨g₁, g₂, l₁, l₂⟩ := good_rebalanceRight ht hu hc k v hrest
      obtain ⟨hb', hh', hco⟩ := node_of_good g₁ g₂
      exact ⟨hb', by rw [hh', hh], hco, by simpa using l₂, by simpa using l₁⟩

end PureStructure

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α}

/-- Pure erasure from a subtree. -/
@[expose] def eraseSubtree (t : ℕ) (k : α) (tr : BTree α β) : BTree α β :=
  Id.run (eraseSubtreeM t leI (pure ()) k tr)

/-- Pure erasure among the triples after `prev`, whose erasure is `prevErased`. -/
@[expose] def eraseRest (t : ℕ) (k : α) (prev prevErased : BTree α β)
    (rest : List (Triple α β)) : BTree α β × List (Triple α β) :=
  Id.run (eraseRestM t leI (pure ()) k prev (pure prevErased) rest)

/-- Remove the entry with key `k`, if any, from a B-tree of minimum degree `t`: the `Id`
instantiation of `eraseM`. An emptied root collapses into its only child. -/
@[expose] def erase (t : ℕ) (k : α) (tr : BTree α β) : BTree α β :=
  Id.run (eraseM t leI (pure ()) k tr)

/-- `eraseSubtree` is the `Id` instantiation of `eraseSubtreeM`. -/
theorem eraseSubtree_def (tr : BTree α β) :
    eraseSubtree t k tr = Id.run (eraseSubtreeM t leI (pure ()) k tr) := (rfl)

/-- `eraseRest` is the `Id` instantiation of `eraseRestM`, with `prevErased` returned purely. -/
theorem eraseRest_def (prev pe : BTree α β) (rest : List (Triple α β)) :
    eraseRest t k prev pe rest = Id.run (eraseRestM t leI (pure ()) k prev (pure pe) rest) := (rfl)

/-- `erase` is the `Id` instantiation of `eraseM`. -/
theorem erase_def (tr : BTree α β) : erase t k tr = Id.run (eraseM t leI (pure ()) k tr) := (rfl)

/-- Erasure from the empty tree. -/
@[simp] theorem eraseSubtree_leaf : eraseSubtree t k (.leaf : BTree α β) = .leaf := rfl

/-- Erasure from the empty tree is the empty tree. -/
@[simp] theorem erase_leaf : erase t k (.leaf : BTree α β) = .leaf := rfl

/-- Erasure from a node is erasure among its triples. -/
theorem eraseSubtree_node (first : BTree α β) (rest : List (Triple α β)) :
    eraseSubtree t k (.node first rest) =
      .node (eraseRest t k first (eraseSubtree t k first) rest).1
        (eraseRest t k first (eraseSubtree t k first) rest).2 := rfl

/-- Past the last triple, the erasure of the preceding child. -/
@[simp] theorem eraseRest_nil (prev pe : BTree α β) :
    eraseRest t k prev pe [] = (pe, []) := rfl

/-- Pure erasure at a triple. -/
theorem eraseRest_cons (prev pe : BTree α β) (k' : α) (v' : β) (c : BTree α β)
    (rest : List (Triple α β)) :
    eraseRest t k prev pe ((k', v', c) :: rest) =
      if k ≤ k' then
        if k' ≤ k then
          match popMin t c with
          | none => (prev, rest)
          | some ((k₂, v₂), c') =>
            match rest with
            | [] => rebalanceLast t prev k₂ v₂ c'
            | (k₃, v₃, c₃) :: rest₃ =>
              let p := rebalanceRight t c' k₃ v₃ c₃ rest₃
              (prev, (k₂, v₂, p.1) :: p.2)
        else rebalanceRight t pe k' v' c rest
      else
        match rest with
        | [] => rebalanceLast t prev k' v' (eraseSubtree t k c)
        | _ :: _ =>
          let p := eraseRest t k c (eraseSubtree t k c) rest
          (prev, (k', v', p.1) :: p.2) := by
  by_cases h₁ : k ≤ k' <;> by_cases h₂ : k' ≤ k <;>
    simp only [eraseRest, eraseRestM, leI, h₁, h₂, decide_true, decide_false, ↓reduceIte,
      popMin, rebalanceRight, rebalanceLast, eraseSubtree] <;>
    -- as in `popMin_node`, each branch in `Id` is the pure branch by definition
    rfl

/-- Erasure is erasure from the root subtree, then collapsing an empty root. -/
theorem erase_eq_collapse (tr : BTree α β) : erase t k tr = collapse (eraseSubtree t k tr) := rfl

/-- The search among the triples after `prev`, against the model: on sorted entries, given
that `prevErased` is the erasure of `prev`, the result has the entries of the model erasure. -/
theorem eraseRest_spec {rest : List (Triple α β)}
    (hc : ∀ e ∈ rest, e.child.toList.IsSortedAssoc →
      (eraseSubtree t k e.child).toList = SortedAssoc.erase k e.child.toList)
    (prev pe : BTree α β) (hs : (prev.toList ++ toListRest rest).IsSortedAssoc)
    (hpe : prev.toList.IsSortedAssoc → pe.toList = SortedAssoc.erase k prev.toList) :
    (eraseRest t k prev pe rest).1.toList ++ toListRest (eraseRest t k prev pe rest).2 =
      SortedAssoc.erase k (prev.toList ++ toListRest rest) := by
  induction rest generalizing prev pe with
  | nil =>
    rw [List.isSortedAssoc_append_iff] at hs
    simp [hpe hs.1]
  | cons e rest ih =>
    obtain ⟨k', v', c⟩ := e
    have hcc : c.toList.IsSortedAssoc →
        (eraseSubtree t k c).toList = SortedAssoc.erase k c.toList := hc _ List.mem_cons_self
    have ih := ih fun e he => hc e (List.mem_cons_of_mem _ he)
    rw [toListRest_cons, List.cons_append, List.isSortedAssoc_append_cons_iff] at hs
    obtain ⟨hpre, hcl, hlt, hgt⟩ := hs
    have hcs : c.toList.IsSortedAssoc := (List.isSortedAssoc_append_iff.1 hcl).1
    rw [eraseRest_cons, toListRest_cons, List.cons_append]
    by_cases h₁ : k ≤ k'
    · by_cases h₂ : k' ≤ k
      · -- the key is at this triple: its entry goes, replaced by the successor from its child
        obtain rfl : k = k' := le_antisymm h₁ h₂
        rw [SortedAssoc.erase_append_cons_self hlt hgt]
        simp only [h₁, ↓reduceIte]
        rcases hpm : popMin t c with _ | ⟨⟨k₂, v₂⟩, c'⟩
        · simp [toList_popMin.1 hpm]
        · have hcm := toList_popMin.2 _ _ hpm
          rcases rest with _ | ⟨⟨k₃, v₃, c₃⟩, rest₃⟩
          · simp only
            rw [toList_rebalanceLast, hcm]
            simp
          · simp only [toListRest_cons, List.cons_append]
            rw [toList_rebalanceRight, hcm]
            simp
      · -- the key is below this triple: erase from the child before it, then repair that child
        have hk : k < k' := lt_of_le_of_ne h₁ fun h => h₂ (h ▸ le_rfl)
        simp only [h₁, h₂, ↓reduceIte]
        have htail : SortedAssoc.erase k ((k', v') :: (c.toList ++ toListRest rest)) =
            (k', v') :: (c.toList ++ toListRest rest) := by
          refine SortedAssoc.erase_of_forall_ne fun p hp => ?_
          rcases List.mem_cons.1 hp with rfl | hp
          · exact hk.ne'
          · exact (hk.trans (hgt p hp)).ne'
        rw [toList_rebalanceRight, hpe hpre, toListRest_cons, SortedAssoc.erase_append, htail]
        simp
    · -- the key is above this triple: move on, or at the last triple erase from its child
      have hk : k' < k := lt_of_not_ge h₁
      have hpre' : SortedAssoc.erase k prev.toList = prev.toList :=
        SortedAssoc.erase_of_forall_ne fun p hp => ((hlt p hp).trans hk).ne
      simp only [h₁, ↓reduceIte]
      rcases rest with _ | ⟨e, rest⟩
      · simp only
        rw [toList_rebalanceLast]
        simp [SortedAssoc.erase_append, SortedAssoc.erase_cons, hk.ne, hpre', hcc hcs]
      · simp only [toListRest_cons, List.cons_append]
        rw [ih c (eraseSubtree t k c) hcl hcc]
        simp [SortedAssoc.erase_cons, hk.ne, hpre']

/-- Model equation of erasure from a subtree with sorted entries. -/
theorem toList_eraseSubtree_of_isSortedAssoc {tr : BTree α β} (h : tr.toList.IsSortedAssoc) :
    (eraseSubtree t k tr).toList = SortedAssoc.erase k tr.toList := by
  induction tr with
  | leaf => rfl
  | node first rest ihf ihr =>
    rw [eraseSubtree_node, toList_node, toList_node]
    exact eraseRest_spec ihr first _ h ihf

/-- Model equation of erasure on a tree with sorted entries. -/
theorem toList_erase_of_isSortedAssoc {tr : BTree α β} (h : tr.toList.IsSortedAssoc) :
    (erase t k tr).toList = SortedAssoc.erase k tr.toList := by
  rw [erase_eq_collapse, toList_collapse, toList_eraseSubtree_of_isSortedAssoc h]

/-- Shape of the erasure among the triples after a good child `prev`, whose erasure `pe` is at
most one key short: the results are good, with at most one key fewer. -/
theorem good_eraseRest (ht : 2 ≤ t) {h : ℕ} {rest : List (Triple α β)}
    (hc : ∀ e ∈ rest, Good t h e.child ∧ Underfull t h (eraseSubtree t k e.child))
    {prev pe : BTree α β} (hp : Good t h prev) (hpe : Underfull t h pe) (hne : rest ≠ []) :
    Good t h (eraseRest t k prev pe rest).1 ∧
      (∀ e ∈ (eraseRest t k prev pe rest).2, Good t h e.child) ∧
      (eraseRest t k prev pe rest).2.length ≤ rest.length ∧
      rest.length ≤ (eraseRest t k prev pe rest).2.length + 1 := by
  induction rest generalizing prev pe with
  | nil => exact absurd rfl hne
  | cons e rest ih =>
    obtain ⟨k', v', c⟩ := e
    have hcg : Good t h c ∧ Underfull t h (eraseSubtree t k c) := hc _ List.mem_cons_self
    have hrest : ∀ e ∈ rest, Good t h e.child := fun e he => (hc e (List.mem_cons_of_mem _ he)).1
    have ih := fun {prev pe : BTree α β} => @ih (fun e he => hc e (List.mem_cons_of_mem _ he))
      prev pe
    rw [eraseRest_cons]
    by_cases h₁ : k ≤ k'
    · by_cases h₂ : k' ≤ k
      · simp only [h₁, h₂, ↓reduceIte]
        rcases hpm : popMin t c with _ | ⟨⟨k₂, v₂⟩, c'⟩
        · exact ⟨hp, hrest, by simp, by simp⟩
        · have hcu := hcg.1.underfull_of_eraseFits ht fun ho hpos =>
            eraseFits_popMin ht hcg.1.balanced ho hpos hpm
          rcases rest with _ | ⟨⟨k₃, v₃, c₃⟩, rest₃⟩
          · obtain ⟨r₁, r₂, r₃⟩ := good_rebalanceLast ht hp hcu k₂ v₂
            exact ⟨r₁, r₂, by simpa using r₃, by simp⟩
          · obtain ⟨r₁, r₂, r₃, r₄⟩ := good_rebalanceRight ht hcu (hrest _ List.mem_cons_self)
              k₃ v₃ fun e he => hrest e (List.mem_cons_of_mem _ he)
            exact ⟨hp, List.forall_mem_cons.2 ⟨r₁, r₂⟩, by simpa using r₄, by simpa using r₃⟩
      · simp only [h₁, h₂, ↓reduceIte]
        obtain ⟨r₁, r₂, r₃, r₄⟩ := good_rebalanceRight ht hpe hcg.1 k' v' hrest
        exact ⟨r₁, r₂, by simpa using r₄, by simpa using r₃⟩
    · simp only [h₁, ↓reduceIte]
      rcases rest with _ | ⟨e, rest⟩
      · obtain ⟨r₁, r₂, r₃⟩ := good_rebalanceLast ht hp hcg.2 k' v'
        exact ⟨r₁, r₂, by simpa using r₃, by simp⟩
      · obtain ⟨r₁, r₂, r₃, r₄⟩ := ih hcg.1 hcg.2 (List.cons_ne_nil _ _)
        exact ⟨hp, List.forall_mem_cons.2 ⟨r₁, r₂⟩, by simpa using r₃, by simpa using r₄⟩

/-- Shape invariant of erasure from a subtree. -/
theorem eraseFits_eraseSubtree (ht : 2 ≤ t) {tr : BTree α β} (hb : Balanced tr)
    (ho : ∀ c ∈ tr.children, Occupied t c) (hpos : tr ≠ .leaf → 1 ≤ tr.rootKeys) :
    EraseFits t tr (eraseSubtree t k tr) := by
  induction tr with
  | leaf => exact ⟨.leaf, rfl, by simp, le_rfl, Nat.le_succ _⟩
  | node first rest ihf ihr =>
    obtain ⟨hf, hr⟩ := good_of_balanced_node hb ho
    have hh := hb.height_node
    have hpos := hpos (by simp)
    simp only [rootKeys_node] at hpos ⊢
    have hne : rest ≠ [] := by rintro rfl; simp at hpos
    -- erasure from a good child leaves it at most one key short
    have hpe := hf.underfull_of_eraseFits ht (ihf hf.balanced)
    have hc : ∀ e ∈ rest, Good t first.height e.child ∧
        Underfull t first.height (eraseSubtree t k e.child) := fun e he =>
      ⟨hr e he, (hr e he).underfull_of_eraseFits ht (ihr e he (hr e he).balanced)⟩
    obtain ⟨r₁, r₂, r₃, r₄⟩ := good_eraseRest ht hc hf hpe hne
    rw [eraseSubtree_node]
    obtain ⟨hb', hh', hco⟩ := node_of_good r₁ r₂
    exact ⟨hb', by rw [hh', hh], hco, r₃, r₄⟩

variable {tr : BTree α β}

/-- Model equation of erasure on well-formed trees. -/
theorem toList_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).toList = SortedAssoc.erase k tr.toList :=
  toList_erase_of_isSortedAssoc h.sorted

/-- Erasure preserves well-formedness. -/
theorem IsWF.erase (h : IsWF t tr) (k : α) : IsWF t (erase t k tr) := by
  have ht := h.two_le
  have hrk := h.rootKeys_le
  have hfit := eraseFits_eraseSubtree (k := k) ht h.balanced h.occupied_of_mem_children
    h.rootKeys_pos
  have hb := hfit.balanced
  have hco := hfit.children_occupied
  have hk₁ := hfit.rootKeys_le
  clear hfit
  have hs : (BTree.erase t k tr).toList.IsSortedAssoc := by
    rw [toList_erase h]
    exact SortedAssoc.isSortedAssoc_erase h.sorted
  rw [erase_eq_collapse] at hs ⊢
  generalize eraseSubtree t k tr = c at *
  rcases c with _ | ⟨f, _ | ⟨e, r⟩⟩
  · exact ⟨ht, by simp [collapse], by simp [collapse], by simp [collapse], .leaf, hs⟩
  · simp only [collapse] at hs ⊢
    have hf : Occupied t f := hco f (by simp)
    exact hf.isWF ht (hb.of_mem_children (c := f) (by simp)) hs
  · simp only [collapse, rootKeys_node] at hs hk₁ ⊢
    exact ⟨ht, by simp only [rootKeys_node]; omega, fun _ => by simp, hco, hb, hs⟩

/-- On a well-formed tree, erasure either keeps the height or lowers it by one. -/
theorem height_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).height = tr.height ∨ (erase t k tr).height + 1 = tr.height := by
  have hfit := eraseFits_eraseSubtree (k := k) h.two_le h.balanced h.occupied_of_mem_children
    h.rootKeys_pos
  have hb := hfit.balanced
  have hh := hfit.height_eq
  clear hfit
  rw [erase_eq_collapse]
  generalize eraseSubtree t k tr = c at *
  rcases c with _ | ⟨f, _ | ⟨e, r⟩⟩
  · exact Or.inl hh
  · exact Or.inr (by simp only [collapse]; rw [← hh, hb.height_node])
  · exact Or.inl hh

/-- Erasure never raises the height. -/
theorem height_erase_le (h : IsWF t tr) (k : α) : (erase t k tr).height ≤ tr.height := by
  rcases height_erase h k with h | h <;> omega

/-- Erasure lowers the height by at most one. -/
theorem height_le_height_erase_add_one (h : IsWF t tr) (k : α) :
    tr.height ≤ (erase t k tr).height + 1 := by
  rcases height_erase h k with h | h <;> omega

/-- On a tree with sorted entries, erasure removes one entry when the key is present and none
otherwise. -/
theorem size_erase_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    (erase t k tr).size = if (lookup k tr).isSome then tr.size - 1 else tr.size := by
  rw [← length_toList (tr := erase t k tr), toList_erase_of_isSortedAssoc h,
    SortedAssoc.length_erase h, lookup_eq_of_isSortedAssoc h, length_toList]

/-- Erasure removes one entry when the key is present and none otherwise. -/
theorem size_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).size = if (lookup k tr).isSome then tr.size - 1 else tr.size :=
  size_erase_of_isSortedAssoc h.sorted k

/-- On a tree with sorted entries, lookup after erasure fails at the erased key and is
unchanged elsewhere. -/
@[simp] theorem lookup_erase_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k k' : α) :
    lookup k' (erase t k tr) = if k' = k then none else lookup k' tr := by
  have hs : (erase t k tr).toList.IsSortedAssoc := by
    rw [toList_erase_of_isSortedAssoc h]
    exact SortedAssoc.isSortedAssoc_erase h
  rw [lookup_eq_of_isSortedAssoc hs, toList_erase_of_isSortedAssoc h,
    lookup_eq_of_isSortedAssoc h]
  split_ifs with hk
  · subst hk
    exact SortedAssoc.lookup_erase_self
  · exact SortedAssoc.lookup_erase_of_ne hk

/-- Lookup after erasure fails at the erased key and is unchanged elsewhere. -/
@[simp] theorem lookup_erase (h : IsWF t tr) (k k' : α) :
    lookup k' (erase t k tr) = if k' = k then none else lookup k' tr :=
  lookup_erase_of_isSortedAssoc h.sorted k k'

/-- On a tree with sorted entries, erasing an absent key leaves the entries unchanged. -/
theorem toList_erase_of_lookup_eq_none_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) {k : α}
    (hk : lookup k tr = none) : (erase t k tr).toList = tr.toList := by
  rw [toList_erase_of_isSortedAssoc h,
    SortedAssoc.erase_of_lookup_eq_none (by rwa [← lookup_eq_of_isSortedAssoc h])]

/-- Erasing an absent key from a well-formed tree leaves the entries unchanged. -/
theorem toList_erase_of_lookup_eq_none (h : IsWF t tr) {k : α} (hk : lookup k tr = none) :
    (erase t k tr).toList = tr.toList :=
  toList_erase_of_lookup_eq_none_of_isSortedAssoc h.sorted hk

end Pure

end Cslib.DataStructure.BTree
