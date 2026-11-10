/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Lookup

/-!
# Insertion into classic B-trees

Insert-or-replace in the B-trees of `Cslib.DataStructure.BTree`, by the bottom-up algorithm of
the functional literature: a recursive call returns either a tree of the same height or an
overflow split around a median entry (`InsertResult`), and the parent absorbs the overflow,
splitting in turn when it then has `2 * t` keys (`InsertResult.ofNode`). An overflow at the root
grows a new root (`InsertResult.toTree`), so the height grows only there. The insertion into the
empty tree overflows at once, which makes the bottom level uniform with the rest. This is the
shape of the classic algorithm of [BayerMcCreight1972]; [CLRS2009], Chapter 18, splits full
nodes pre-emptively on the way down instead. The tree-or-split result follows the functional
insertion of [Mundler2021], whose `up⇩i` it mirrors.

Each operation is defined once over an arbitrary monad `m`, with a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`, as in
`Cslib.DataStructure.BTree.Lookup`. `insertOrSplitM` inserts into a subtree and `insertRestM`
searches among the triples of a node, with the scan and the equality test of `lookupM`. `visit`
fires once on entering each node of the search path, and never at the empty leaf. The pure
operations are the `Id` instantiations with `leI` and `visit := pure ()`. The definitions are
structurally recursive and `@[expose]`d, so `decide` evaluates insertion on concrete trees from
other modules, and the monadic constructor equations hold by `rfl`. Costs are not stated here.

## Main definitions

* `InsertResult`: a tree of the same height, or an overflow split around a median entry.
* `Good`: a balanced, occupied subtree of a given height, the shape of every child of a
  well-formed node.
* `InsertResult.Fits`: the shape invariant of a result relative to the subtree it replaces.
* `insertOrSplitM`, `insertRestM`, `insertM`, `insert`: insert-or-replace.

## Main results

* `Cslib.IsMonadHom.map_insertM`: a monad morphism commutes with insertion.
* `toList_insert_of_isSortedAssoc`, `toList_insert`: the model equation, `toList` of the
  insertion is `SortedAssoc.insert` on `toList`.
* `fits_insertOrSplit`: the shape invariant on balanced trees with occupied children.
* `IsWF.insert`: insertion preserves well-formedness.
* `height_insert`: the height stays or grows by one.
* `size_insert`, `lookup_insert`: size and lookup after insertion.

## References

* [R. Bayer and E. McCreight, *Organization and Maintenance of Large Ordered
  Indexes*][BayerMcCreight1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]
* [N. Mündler, *A Verified Imperative Implementation of B-Trees*][Mundler2021]

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Insert.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Insert.lean).
-/

public section

universe w

namespace Cslib.DataStructure.BTree

/-- The result of inserting into a subtree: a tree of the same height, or an overflow split
into two trees of the same height around a median entry. -/
inductive InsertResult (α : Type) (β : Type) : Type where
  /-- The subtree absorbed the entry. -/
  | tree (tr : BTree α β)
  /-- The subtree overflowed and split around the entry `(k, v)`. -/
  | split (left : BTree α β) (k : α) (v : β) (right : BTree α β)

namespace InsertResult

variable {α β : Type}

/-- The entries of a result in order. -/
@[expose] def toList : InsertResult α β → List (α × β)
  | tree tr => tr.toList
  | split l k v r => l.toList ++ (k, v) :: r.toList

/-- Put a result in the place of a child followed by the triples `rest`. -/
@[expose] def withRest : InsertResult α β → List (Triple α β) →
    BTree α β × List (Triple α β)
  | tree c, rest => (c, rest)
  | split l k v r, rest => (l, (k, v, r) :: rest)

/-- A node with contents `first` and `rest`, split when it has more than `2 * t - 1` keys:
the first `t` keys stay on the left, the next one is the median, and the rest go right. The
`[]` branch is unreachable for `t ≥ 1`. -/
@[expose] def ofNode (t : ℕ) (first : BTree α β) (rest : List (Triple α β)) :
    InsertResult α β :=
  if rest.length ≤ 2 * t - 1 then tree (.node first rest)
  else match rest.drop t with
    | [] => tree (.node first rest)
    | (k, v, c) :: right => split (.node first (rest.take t)) k v (.node c right)

/-- The tree of a result at the root: an overflow grows a new root. -/
@[expose] def toTree : InsertResult α β → BTree α β
  | tree tr => tr
  | split l k v r => .node l [(k, v, r)]

variable {t : ℕ}

/-- The entries of a tree result are the tree's. -/
@[simp] theorem toList_tree (tr : BTree α β) : (tree tr).toList = tr.toList := rfl

/-- The entries of a split are the left entries, the median, then the right entries. -/
@[simp] theorem toList_split (l r : BTree α β) (k : α) (v : β) :
    (split l k v r).toList = l.toList ++ (k, v) :: r.toList := rfl

/-- Growing a new root keeps the entries. -/
@[simp] theorem toList_toTree (x : InsertResult α β) : x.toTree.toList = x.toList := by
  cases x <;> simp [toTree]

/-- Placing a result in the place of a child keeps the entries, followed by those of `rest`. -/
theorem toList_withRest (x : InsertResult α β) (rest : List (Triple α β)) :
    x.toList ++ toListRest rest =
      (x.withRest rest).1.toList ++ toListRest (x.withRest rest).2 := by
  cases x <;> simp [withRest]

/-- Splitting an overflowing node keeps its entries. -/
@[simp] theorem toList_ofNode (first : BTree α β) (rest : List (Triple α β)) :
    (ofNode t first rest).toList = (BTree.node first rest).toList := by
  unfold ofNode
  split_ifs
  · rfl
  · split
    · rfl
    · next k v c right heq =>
      have : rest = rest.take t ++ (k, v, c) :: right := by
        rw [← heq, List.take_append_drop]
      conv_rhs => rw [this]
      simp only [toList_split, toList_node, toListRest_append, toListRest_cons, List.append_assoc,
        List.cons_append]

end InsertResult

/-! ### Shape -/

section Shape

variable {α β : Type} {t : ℕ}

/-- A subtree of height `h` that is balanced and occupied: what every child of a well-formed
node is. -/
structure Good (t h : ℕ) (c : BTree α β) : Prop where
  /-- The subtree is balanced. -/
  balanced : Balanced c
  /-- The subtree has height `h`. -/
  height_eq : c.height = h
  /-- Every node of the subtree is occupied. -/
  occupied : Occupied t c

/-- A node over good children of height `h` is balanced, of height `h + 1`, with occupied
children. -/
theorem node_of_good {first : BTree α β} {rest : List (Triple α β)} {h : ℕ}
    (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child) :
    Balanced (.node first rest) ∧ (BTree.node first rest).height = h + 1 ∧
      ∀ x ∈ (BTree.node first rest).children, Occupied t x := by
  obtain ⟨hb, hh⟩ := balanced_node_of_forall hf.balanced fun e he =>
    ⟨(hr e he).balanced, (hr e he).height_eq.trans hf.height_eq.symm⟩
  refine ⟨hb, by rw [hh, hf.height_eq], fun x hx => ?_⟩
  simp only [children_node, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨e, he, rfl⟩
  exacts [hf.occupied, (hr e he).occupied]

/-- A node with `t - 1` to `2 * t - 1` keys over good children of height `h` is good, of height
`h + 1`. -/
theorem good_node {first : BTree α β} {rest : List (Triple α β)} {h : ℕ}
    (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child) (h₁ : t - 1 ≤ rest.length)
    (h₂ : rest.length ≤ 2 * t - 1) : Good t (h + 1) (.node first rest) := by
  obtain ⟨hb, hh, -⟩ := node_of_good hf hr
  exact ⟨hb, hh, .node h₁ h₂ hf.occupied fun e he => (hr e he).occupied⟩

/-- The children of a balanced node whose children are occupied are good, of the height of
its first child. -/
theorem good_of_balanced_node {first : BTree α β} {rest : List (Triple α β)}
    (hb : Balanced (.node first rest)) (ho : ∀ c ∈ (BTree.node first rest).children, Occupied t c) :
    Good t first.height first ∧ ∀ e ∈ rest, Good t first.height e.child :=
  ⟨⟨hb.first, rfl, ho first List.mem_cons_self⟩, fun _ he =>
    ⟨hb.of_mem_rest he, hb.height_of_mem_rest he,
      ho _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))⟩⟩

namespace InsertResult

/-- A new root grown from a split of two balanced trees of equal height is balanced and one
taller. -/
theorem balanced_toTree_split {l r : BTree α β} (k : α) (v : β) (hl : Balanced l)
    (hr : Balanced r) (hh : r.height = l.height) :
    Balanced (split l k v r).toTree ∧ (split l k v r).toTree.height = l.height + 1 :=
  balanced_node_of_forall hl (by simpa using ⟨hr, hh⟩)

/-- A node over good children of height `h` with more than `2 * t - 1` keys, and at most `t + 1`
more, splits into two good trees of height `h + 1`: the first `t` keys go left, the next one is
the median, and the rest go right. -/
theorem exists_good_split_ofNode {first : BTree α β} {rest : List (Triple α β)}
    {h : ℕ} (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child)
    (hlo : 2 * t - 1 < rest.length) (hhi : rest.length ≤ 2 * t - 1 + t + 1) :
    ∃ l k v r, ofNode t first rest = split l k v r ∧ Good t (h + 1) l ∧ Good t (h + 1) r := by
  have hgt : ¬ rest.length ≤ 2 * t - 1 := by omega
  unfold ofNode
  simp only [hgt, ↓reduceIte]
  split
  · next heq =>
    rw [List.drop_eq_nil_iff] at heq
    omega
  · next k v c right heq =>
    have hmem : (k, v, c) ∈ rest := List.mem_of_mem_drop (heq ▸ List.mem_cons_self ..)
    have hright : ∀ e ∈ right, e ∈ rest := fun e he =>
      List.mem_of_mem_drop (heq ▸ List.mem_cons_of_mem _ he)
    have hrl : right.length = rest.length - t - 1 := by
      have := congrArg List.length heq
      simp only [List.length_drop, List.length_cons] at this
      omega
    have htl : (rest.take t).length = t := by simp; omega
    exact ⟨_, k, v, _, rfl,
      good_node hf (fun e he => hr e (List.mem_of_mem_take he)) (by omega) (by omega),
      good_node (hr _ hmem) (fun e he => hr e (hright e he)) (by omega) (by omega)⟩

/-- The shape invariant of the result of inserting into `tr`: either a tree of the same
height with at least as many root keys, still within `2 * t - 1`, or two good trees of the
same height. -/
def Fits (t : ℕ) (tr : BTree α β) : InsertResult α β → Prop
  | tree c => tr ≠ .leaf ∧ Balanced c ∧ c.height = tr.height ∧
      (∀ c' ∈ c.children, Occupied t c') ∧ tr.rootKeys ≤ c.rootKeys ∧ c.rootKeys ≤ 2 * t - 1
  | split l _ _ r => Good t tr.height l ∧ Good t tr.height r

/-- A node over good children of height `h` with at most one key more than the
`2 * t - 1` allowed, after the overflow split, fits any non-empty tree of height `h + 1` that had
no more keys. -/
theorem fits_ofNode {tr first : BTree α β} {rest : List (Triple α β)}
    {h : ℕ} (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child)
    (hlen : rest.length ≤ 2 * t - 1 + 1) (htr : tr ≠ .leaf) (hh : tr.height = h + 1)
    (hk : tr.rootKeys ≤ rest.length) : (ofNode t first rest).Fits t tr := by
  by_cases hle : rest.length ≤ 2 * t - 1
  · obtain ⟨hb, hhn, hco⟩ := node_of_good hf hr
    simp only [ofNode, hle, ↓reduceIte]
    exact ⟨htr, hb, hhn.trans hh.symm, hco, hk, hle⟩
  · -- the node overflowed by exactly one key
    obtain ⟨l, k, v, r, heq, hl, hr'⟩ :=
      exists_good_split_ofNode hf hr (by omega) (by omega)
    rw [heq]
    exact ⟨hh ▸ hl, hh ▸ hr'⟩

/-- Placing a fitting result in the place of an occupied child of height `h` among good
triples keeps every child good, and adds at most one key. -/
theorem fits_withRest {c : BTree α β} {x : InsertResult α β} (hx : x.Fits t c)
    (hc : Occupied t c) {h : ℕ} (hch : c.height = h) {rest : List (Triple α β)}
    (hr : ∀ e ∈ rest, Good t h e.child) :
    Good t h (x.withRest rest).1 ∧ (∀ e ∈ (x.withRest rest).2, Good t h e.child) ∧
      rest.length ≤ (x.withRest rest).2.length ∧
      (x.withRest rest).2.length ≤ rest.length + 1 := by
  cases x with
  | tree c' =>
    obtain ⟨hne, hb, hh, hco, hk₁, hk₂⟩ := hx
    refine ⟨⟨hb, hh.trans hch, ?_⟩, hr, le_rfl, Nat.le_succ _⟩
    cases c with
    | leaf => exact absurd rfl hne
    | node first' rest' =>
      have := hc.le_length
      cases c' with
      | leaf => exact .leaf
      | node f r =>
        simp only [rootKeys_node] at hk₁ hk₂
        exact .node (by omega) hk₂ (hco f List.mem_cons_self)
          fun e he => hco _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
  | split l k v r =>
    obtain ⟨hl, hr'⟩ := hx
    refine ⟨hch ▸ hl, fun e he => ?_, Nat.le_succ _, le_rfl⟩
    simp only [withRest, List.mem_cons] at he
    rcases he with rfl | he
    exacts [hch ▸ hr', hr e he]

end InsertResult

end Shape

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

mutual
/-- Bottom-up insertion into a subtree: the tree with the entry inserted, or its split when it
overflows. A node is visited once, on entry; the empty leaf is not visited and overflows at once
into the entry between two empty leaves. -/
@[expose] def insertOrSplitM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    BTree α β → m (InsertResult α β)
  | .leaf => pure (.split .leaf k v .leaf)
  | .node first rest => do
    visit
    match ← insertRestM t le visit k v rest with
    | some rest' => pure (.ofNode t first rest')
    | none =>
      let p := (← insertOrSplitM t le visit k v first).withRest rest
      pure (.ofNode t p.1 p.2)

/-- Insertion among the triples of a node, scanning them in order with the comparisons of
`lookupM`: `none` defers to the child before the triples, because the key is below the first
of them; `some rest'` is the new list of triples, with the value replaced at an equal key or
the result of the descent placed in the child after the last key below the query. -/
@[expose] def insertRestM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    List (Triple α β) → m (Option (List (Triple α β)))
  | [] => pure none
  | (k', v', c) :: rest => do
    if ← le k k' then
      if ← le k' k then pure (some ((k, v, c) :: rest)) else pure none
    else
      match ← insertRestM t le visit k v rest with
      | some rest' => pure (some ((k', v', c) :: rest'))
      | none =>
        let p := (← insertOrSplitM t le visit k v c).withRest rest
        pure (some ((k', v', p.1) :: p.2))
end

/-- Inserting into the empty tree overflows at once, without a visit: the parent absorbs the
new entry. -/
@[simp] theorem insertOrSplitM_leaf (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    insertOrSplitM t le visit k v (.leaf : BTree α β) = pure (.split .leaf k v .leaf) := rfl

/-- A node is visited once, before its triples are searched; the result is split when it
overflows. -/
theorem insertOrSplitM_node (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (first : BTree α β) (rest : List (Triple α β)) :
    insertOrSplitM t le visit k v (.node first rest) = (do
      visit
      match ← insertRestM t le visit k v rest with
      | some rest' => pure (.ofNode t first rest')
      | none =>
        let p := (← insertOrSplitM t le visit k v first).withRest rest
        pure (.ofNode t p.1 p.2)) := rfl

/-- The search past the last triple defers to the child before it. -/
@[simp] theorem insertRestM_nil (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    insertRestM t le visit k v ([] : List (Triple α β)) = pure none := rfl

/-- At a triple: replace on equality, defer to the preceding child when the key is below, and
otherwise move on, descending into this triple's child when every later key is above. -/
theorem insertRestM_cons (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (k' : α) (v' : β) (c : BTree α β) (rest : List (Triple α β)) :
    insertRestM t le visit k v ((k', v', c) :: rest) = (do
      if ← le k k' then
        if ← le k' k then pure (some ((k, v, c) :: rest)) else pure none
      else
        match ← insertRestM t le visit k v rest with
        | some rest' => pure (some ((k', v', c) :: rest'))
        | none =>
          let p := (← insertOrSplitM t le visit k v c).withRest rest
          pure (some ((k', v', p.1) :: p.2))) := rfl

/-- Insert-or-replace: the bottom-up insertion, growing a new root on overflow. -/
@[expose] def insertM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (tr : BTree α β) : m (BTree α β) := do
  return (← insertOrSplitM t le visit k v tr).toTree

/-- Insertion is the bottom-up insertion with an overflow at the root grown into a new root. -/
theorem insertM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (tr : BTree α β) :
    insertM t le visit k v tr = (do return (← insertOrSplitM t le visit k v tr).toTree) := rfl

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

mutual
/-- A monad morphism commutes with the bottom-up insertion into a subtree. -/
theorem _root_.Cslib.IsMonadHom.map_insertOrSplitM (hf : IsMonadHom m n f) (t : ℕ)
    (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) (tr : BTree α β) :
    f (insertOrSplitM t le visit k v tr) =
      insertOrSplitM t (fun a b => f (le a b)) (f visit) k v tr := by
  match tr with
  | .leaf => simp [hf.map_pure]
  | .node first rest =>
    simp only [insertOrSplitM_node, hf.map_bind, hf.map_insertRestM t le visit k v rest]
    refine bind_congr fun _ => bind_congr fun o => ?_
    cases o <;> simp [hf.map_bind, hf.map_pure, hf.map_insertOrSplitM t le visit k v first]
termination_by sizeOf tr

/-- A monad morphism commutes with the insertion among the triples of a node. -/
theorem _root_.Cslib.IsMonadHom.map_insertRestM (hf : IsMonadHom m n f) (t : ℕ)
    (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) (rest : List (Triple α β)) :
    f (insertRestM t le visit k v rest) =
      insertRestM t (fun a b => f (le a b)) (f visit) k v rest := by
  match rest with
  | [] => simp [hf.map_pure]
  | (k', v', c) :: rest =>
    simp only [insertRestM_cons, hf.map_bind, apply_ite f, hf.map_pure,
      hf.map_insertRestM t le visit k v rest]
    refine bind_congr fun b => ?_
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    refine bind_congr fun o => ?_
    cases o <;> simp [hf.map_bind, hf.map_pure, hf.map_insertOrSplitM t le visit k v c]
termination_by sizeOf rest
end

/-- A monad morphism commutes with insertion. -/
theorem _root_.Cslib.IsMonadHom.map_insertM (hf : IsMonadHom m n f) (t : ℕ)
    (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) (tr : BTree α β) :
    f (insertM t le visit k v tr) = insertM t (fun a b => f (le a b)) (f visit) k v tr := by
  simp [insertM, hf.map_bind, hf.map_pure, hf.map_insertOrSplitM]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α} {v : β}

/-- Pure bottom-up insertion into a subtree. -/
@[expose] def insertOrSplit (t : ℕ) (k : α) (v : β) (tr : BTree α β) : InsertResult α β :=
  Id.run (insertOrSplitM t leI (pure ()) k v tr)

/-- Pure insertion among the triples of a node. -/
@[expose] def insertRest (t : ℕ) (k : α) (v : β) (rest : List (Triple α β)) :
    Option (List (Triple α β)) :=
  Id.run (insertRestM t leI (pure ()) k v rest)

/-- Pure insertion. -/
@[expose] def insert (t : ℕ) (k : α) (v : β) (tr : BTree α β) : BTree α β :=
  Id.run (insertM t leI (pure ()) k v tr)

/-- `insertOrSplit` is the `Id` instantiation of `insertOrSplitM`. -/
theorem insertOrSplit_def (tr : BTree α β) :
    insertOrSplit t k v tr = Id.run (insertOrSplitM t leI (pure ()) k v tr) := (rfl)

/-- `insertRest` is the `Id` instantiation of `insertRestM`. -/
theorem insertRest_def (rest : List (Triple α β)) :
    insertRest t k v rest = Id.run (insertRestM t leI (pure ()) k v rest) := (rfl)

/-- `insert` is the `Id` instantiation of `insertM`. -/
theorem insert_def (tr : BTree α β) : insert t k v tr = Id.run (insertM t leI (pure ()) k v tr) :=
  (rfl)

/-- Insertion is the bottom-up insertion with an overflow grown into a new root. -/
theorem insert_eq_toTree (tr : BTree α β) : insert t k v tr = (insertOrSplit t k v tr).toTree :=
  rfl

/-- Inserting into the empty tree overflows at once. -/
@[simp] theorem insertOrSplit_leaf :
    insertOrSplit t k v (.leaf : BTree α β) = .split .leaf k v .leaf := rfl

/-- Insertion into a node: search its triples, descending into the first child when the key is
below them, then split on overflow. -/
theorem insertOrSplit_node (first : BTree α β) (rest : List (Triple α β)) :
    insertOrSplit t k v (.node first rest) =
      match insertRest t k v rest with
      | some rest' => .ofNode t first rest'
      | none =>
        let p := (insertOrSplit t k v first).withRest rest
        .ofNode t p.1 p.2 := by
  -- In `Id`, bind is application and `pure` is the identity, so after unfolding, each branch of
  -- the monadic `match` is the corresponding pure branch by definition.
  simp only [insertOrSplit, insertRest, insertOrSplitM]
  cases insertRestM t leI (pure ()) k v rest <;> rfl

/-- The search past the last triple defers to the child before it. -/
@[simp] theorem insertRest_nil : insertRest t k v ([] : List (Triple α β)) = none := rfl

/-- The search at a triple: replace on equality, defer when the key is below, and otherwise
move on, descending into this triple's child when every later key is above. -/
theorem insertRest_cons (k' : α) (v' : β) (c : BTree α β) (rest : List (Triple α β)) :
    insertRest t k v ((k', v', c) :: rest) =
      if k ≤ k' then (if k' ≤ k then some ((k, v, c) :: rest) else none)
      else match insertRest t k v rest with
        | some rest' => some ((k', v', c) :: rest')
        | none =>
          let p := (insertOrSplit t k v c).withRest rest
          some ((k', v', p.1) :: p.2) := by
  by_cases h₁ : k ≤ k' <;> by_cases h₂ : k' ≤ k <;>
    simp only [insertRest, insertOrSplit, insertRestM, leI, h₁, h₂, decide_true, decide_false,
      ↓reduceIte, Id.run_pure, pure_bind, bind_pure_comp] <;>
    -- as in `insertOrSplit_node`, each branch in `Id` is the pure branch by definition
    cases insertRestM t leI (pure ()) k v rest <;> rfl

/-- The search among the triples of a node, against the model: when it defers to the child
before the triples, the key is below all their entries; otherwise it performs the model
insertion after any sorted prefix of smaller keys. -/
theorem insertRest_spec {rest : List (Triple α β)}
    (hc : ∀ e ∈ rest, e.child.toList.IsSortedAssoc →
      (insertOrSplit t k v e.child).toList = SortedAssoc.insert k v e.child.toList)
    (pre : List (α × β)) (hs : (pre ++ toListRest rest).IsSortedAssoc) :
    (insertRest t k v rest = none → ∀ p ∈ toListRest rest, k < p.1) ∧
      ∀ r, insertRest t k v rest = some r →
        pre ++ toListRest r = SortedAssoc.insert k v (pre ++ toListRest rest) := by
  induction rest generalizing pre with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k', v', c⟩ := e
    have hs' := hs
    rw [toListRest_cons, List.cons_append, List.isSortedAssoc_append_cons_iff,
      List.isSortedAssoc_append_iff] at hs'
    obtain ⟨hpre, ⟨hcs, hrs, hcr⟩, hlt, hgt⟩ := hs'
    have hcc := hc _ (List.mem_cons_self ..) hcs
    have ih := ih (fun e he => hc e (List.mem_cons_of_mem _ he))
    simp only [toListRest_cons, List.cons_append] at hs ⊢
    rw [insertRest_cons]
    by_cases h₁ : k ≤ k'
    · by_cases h₂ : k' ≤ k
      · -- the key is at this triple: its value is replaced
        obtain rfl : k = k' := le_antisymm h₁ h₂
        refine ⟨by simp, fun r hr => ?_⟩
        simp only [h₁, ↓reduceIte, Option.some.injEq] at hr
        subst hr
        rw [SortedAssoc.insert_append_of_forall_lt hlt, SortedAssoc.insert_cons]
        simp
      · -- the key is below this triple: defer to the child before it
        have hk : k < k' := lt_of_le_of_ne h₁ fun h => h₂ (h ▸ le_rfl)
        refine ⟨fun _ p hp => ?_, fun r hr => by simp [h₁, h₂] at hr⟩
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hk
        · exact hk.trans (hgt p hp)
    · -- the key is above this triple: the search moves on, and the result is `some`
      have hk : k' < k := lt_of_not_ge h₁
      have ih := ih (pre ++ (k', v') :: c.toList) (by simpa using hs)
      simp only [h₁, ↓reduceIte]
      refine ⟨fun h => by split at h <;> simp at h, fun r hr => ?_⟩
      have hins := SortedAssoc.insert_append_cons_of_lt (v := v) (v' := v')
        (l₂ := c.toList ++ toListRest rest) (fun p hp => (hlt p hp).trans hk) hk
      cases hr' : insertRest t k v rest with
      | some r' =>
        -- the later triples took the key
        simp only [hr', Option.some.injEq] at hr
        subst hr
        have := ih.2 r' hr'
        simp only [List.append_assoc, List.cons_append] at this
        simpa only [toListRest_cons, List.cons_append, List.append_assoc] using this
      | none =>
        -- the key is below every later triple: descend into this triple's child
        simp only [hr', Option.some.injEq] at hr
        subst hr
        rw [hins, SortedAssoc.insert_append_of_forall_gt (ih.1 hr'), ← hcc,
          InsertResult.toList_withRest]
        simp

/-- Model equation of the bottom-up insertion on a subtree with sorted entries. -/
theorem toList_insertOrSplit_of_isSortedAssoc {tr : BTree α β} (h : tr.toList.IsSortedAssoc) :
    (insertOrSplit t k v tr).toList = SortedAssoc.insert k v tr.toList := by
  induction tr with
  | leaf => rfl
  | node first rest ihf ihr =>
    have spec := insertRest_spec (t := t) (k := k) (v := v) ihr first.toList h
    rw [toList_node, List.isSortedAssoc_append_iff] at h
    rw [insertOrSplit_node]
    cases hr : insertRest t k v rest with
    | some r =>
      simp only [InsertResult.toList_ofNode, toList_node]
      exact spec.2 r hr
    | none =>
      simp only [InsertResult.toList_ofNode, toList_node]
      rw [← InsertResult.toList_withRest, ihf h.1,
        SortedAssoc.insert_append_of_forall_gt (spec.1 hr)]

/-- Model equation of insertion on a tree with sorted entries. -/
theorem toList_insert_of_isSortedAssoc {tr : BTree α β} (h : tr.toList.IsSortedAssoc) :
    (insert t k v tr).toList = SortedAssoc.insert k v tr.toList := by
  rw [insert_eq_toTree, InsertResult.toList_toTree, toList_insertOrSplit_of_isSortedAssoc h]

/-- The search among the triples of a node keeps every child good, and adds at most one
key. -/
theorem fits_insertRest {rest : List (Triple α β)} {h : ℕ}
    (hc : ∀ e ∈ rest, Good t h e.child ∧ (insertOrSplit t k v e.child).Fits t e.child)
    {r : List (Triple α β)} (hr : insertRest t k v rest = some r) :
    (∀ e ∈ r, Good t h e.child) ∧ rest.length ≤ r.length ∧ r.length ≤ rest.length + 1 := by
  induction rest generalizing r with
  | nil => simp at hr
  | cons e rest ih =>
    obtain ⟨k', v', c⟩ := e
    have hcc : Good t h c ∧ (insertOrSplit t k v c).Fits t c := hc _ List.mem_cons_self
    have hrest : ∀ e ∈ rest, Good t h e.child := fun e he => (hc e (List.mem_cons_of_mem _ he)).1
    have ih := fun r (hr : insertRest t k v rest = some r) =>
      ih (fun e he => hc e (List.mem_cons_of_mem _ he)) hr
    rw [insertRest_cons] at hr
    by_cases h₁ : k ≤ k'
    · by_cases h₂ : k' ≤ k
      · simp only [h₁, h₂, ↓reduceIte, Option.some.injEq] at hr
        subst hr
        refine ⟨fun e he => ?_, by simp, by simp⟩
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        exacts [hcc.1, hrest e he]
      · simp [h₁, h₂] at hr
    · simp only [h₁, ↓reduceIte] at hr
      cases hr' : insertRest t k v rest with
      | some r' =>
        simp only [hr', Option.some.injEq] at hr
        subst hr
        obtain ⟨h₁, h₂, h₃⟩ := ih r' hr'
        refine ⟨fun e he => ?_, by simpa using h₂, by simpa using h₃⟩
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        exacts [hcc.1, h₁ e he]
      | none =>
        simp only [hr', Option.some.injEq] at hr
        subst hr
        obtain ⟨hp₁, hp₂, hl₁, hl₂⟩ :=
          InsertResult.fits_withRest hcc.2 hcc.1.occupied hcc.1.height_eq hrest
        refine ⟨fun e he => ?_, by simpa using hl₁, by simpa using hl₂⟩
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        exacts [hp₁, hp₂ e he]

/-- Shape invariant of the bottom-up insertion. -/
theorem fits_insertOrSplit {tr : BTree α β} (hb : Balanced tr)
    (ho : ∀ c ∈ tr.children, Occupied t c) (hk : tr.rootKeys ≤ 2 * t - 1) :
    (insertOrSplit t k v tr).Fits t tr := by
  induction tr with
  | leaf => exact ⟨⟨.leaf, rfl, .leaf⟩, ⟨.leaf, rfl, .leaf⟩⟩
  | node first rest ihf ihr =>
    obtain ⟨hf, hr⟩ := good_of_balanced_node hb ho
    -- the hypotheses of the induction, for an occupied child
    have hchild : ∀ c : BTree α β, Occupied t c →
        (∀ c' ∈ c.children, Occupied t c') ∧ c.rootKeys ≤ 2 * t - 1 :=
      fun _ hc => ⟨fun _ hc' => hc.of_mem_children hc', hc.rootKeys_le⟩
    have hrest : ∀ e ∈ rest, Good t first.height e.child ∧
        (insertOrSplit t k v e.child).Fits t e.child := fun e he => by
      obtain ⟨h₁, h₂⟩ := hchild _ (hr e he).occupied
      exact ⟨hr e he, ihr e he (hr e he).balanced h₁ h₂⟩
    have hh := hb.height_node
    simp only [rootKeys_node] at hk
    rw [insertOrSplit_node]
    cases hrs : insertRest t k v rest with
    | some r =>
      obtain ⟨h₁, h₂, h₃⟩ := fits_insertRest hrest hrs
      exact InsertResult.fits_ofNode hf h₁ (by omega) (by simp) hh (by simpa using h₂)
    | none =>
      obtain ⟨h₁, h₂⟩ := hchild first hf.occupied
      obtain ⟨hp₁, hp₂, hl₁, hl₂⟩ :=
        InsertResult.fits_withRest (ihf hb.first h₁ h₂) hf.occupied rfl hr
      exact InsertResult.fits_ofNode hp₁ hp₂ (by omega) (by simp) hh (by simpa using hl₁)

variable {tr : BTree α β}

/-- Model equation of insertion on well-formed trees. -/
theorem toList_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).toList = SortedAssoc.insert k v tr.toList :=
  toList_insert_of_isSortedAssoc h.sorted

/-- Insertion preserves well-formedness. -/
theorem IsWF.insert (h : IsWF t tr) (k : α) (v : β) : IsWF t (insert t k v tr) := by
  have hf := fits_insertOrSplit (k := k) (v := v) h.balanced h.occupied_of_mem_children
    h.rootKeys_le
  have hs : (BTree.insert t k v tr).toList.IsSortedAssoc := by
    rw [toList_insert h]
    exact SortedAssoc.isSortedAssoc_insert h.sorted
  rw [insert_eq_toTree] at hs ⊢
  cases hx : insertOrSplit t k v tr with
  | tree c =>
    rw [hx] at hf hs
    obtain ⟨hne, hb, -, hco, hk₁, hk₂⟩ := hf
    exact ⟨h.two_le, hk₂, fun _ => (h.rootKeys_pos hne).trans hk₁, hco, hb, hs⟩
  | split l k' v' r =>
    rw [hx] at hf hs
    obtain ⟨hl, hr⟩ := hf
    have := h.two_le
    refine ⟨h.two_le, by simp [InsertResult.toTree]; omega, fun _ => by simp [InsertResult.toTree],
      fun c hc => ?_, (InsertResult.balanced_toTree_split k' v' hl.balanced hr.balanced
        (hr.height_eq.trans hl.height_eq.symm)).1, hs⟩
    simp only [InsertResult.toTree, children_node, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    exacts [hl.occupied, hr.occupied]

/-- On a well-formed tree, insertion either keeps the height or raises it by one. -/
theorem height_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).height = tr.height ∨ (insert t k v tr).height = tr.height + 1 := by
  have hf := fits_insertOrSplit (k := k) (v := v) h.balanced h.occupied_of_mem_children
    h.rootKeys_le
  rw [insert_eq_toTree]
  cases hx : insertOrSplit t k v tr with
  | tree c =>
    rw [hx] at hf
    exact Or.inl hf.2.2.1
  | split l k' v' r =>
    rw [hx] at hf
    obtain ⟨hl, hr⟩ := hf
    rw [(InsertResult.balanced_toTree_split k' v' hl.balanced hr.balanced
      (hr.height_eq.trans hl.height_eq.symm)).2, hl.height_eq]
    exact Or.inr rfl

/-- Insertion raises the height by at most one. -/
theorem height_insert_le (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).height ≤ tr.height + 1 := by
  rcases height_insert h k v with h | h <;> omega

/-- Insertion never lowers the height. -/
theorem height_le_height_insert (h : IsWF t tr) (k : α) (v : β) :
    tr.height ≤ (insert t k v tr).height := by
  rcases height_insert h k v with h | h <;> omega

/-- On a tree with sorted entries, insertion keeps the size when the key is present and adds
one otherwise. -/
theorem size_insert_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) (v : β) :
    (insert t k v tr).size = if (lookup k tr).isSome then tr.size else tr.size + 1 := by
  rw [← length_toList (tr := insert t k v tr), toList_insert_of_isSortedAssoc h,
    SortedAssoc.length_insert h, lookup_eq_of_isSortedAssoc h, length_toList]

/-- Insertion keeps the size when the key is present and adds one otherwise. -/
theorem size_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).size = if (lookup k tr).isSome then tr.size else tr.size + 1 :=
  size_insert_of_isSortedAssoc h.sorted k v

/-- On a tree with sorted entries, lookup after insertion finds the new value at its key and is
unchanged elsewhere. -/
@[simp] theorem lookup_insert_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k k' : α) (v : β) :
    lookup k' (insert t k v tr) = if k' = k then some v else lookup k' tr := by
  have hs : (insert t k v tr).toList.IsSortedAssoc := by
    rw [toList_insert_of_isSortedAssoc h]
    exact SortedAssoc.isSortedAssoc_insert h
  rw [lookup_eq_of_isSortedAssoc hs, toList_insert_of_isSortedAssoc h,
    lookup_eq_of_isSortedAssoc h]
  split_ifs with hk
  · subst hk
    exact SortedAssoc.lookup_insert_self
  · exact SortedAssoc.lookup_insert_of_ne hk

/-- Lookup after insertion finds the new value at its key and is unchanged elsewhere. -/
@[simp] theorem lookup_insert (h : IsWF t tr) (k k' : α) (v : β) :
    lookup k' (insert t k v tr) = if k' = k then some v else lookup k' tr :=
  lookup_insert_of_isSortedAssoc h.sorted k k' v

end Pure

end Cslib.DataStructure.BTree
