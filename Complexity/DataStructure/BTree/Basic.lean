/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.List.SortedAssoc
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Classic B-trees

The B-trees of [BayerMcCreight1972], in the minimum-degree form of [CLRS2009], Chapter 18. A node
is a first child followed by a list of `(key, value, child)` triples (`BTree.Triple`), so a node
with `m` keys has `m + 1` children by construction; `leaf` is the empty tree. The tree is a map
from keys to values, specified by `toList` against the sorted association list model
`List.IsSortedAssoc`. `toList` traverses any tree in structural in-order (the first child, then
each key-value pair followed by its child); under `IsWF` (its `sorted` field) the keys are
strictly increasing, which gives map semantics.

`height` counts the nodes on a root-to-leaf path: the leaf has height `0` and a node has height
one more than its tallest child. Well-formedness at minimum degree `t` is the hypothesis
`IsWF t tr`, never part of the type: `t ≥ 2`, every non-root node has between `t - 1` and
`2 * t - 1` keys (`Occupied`), a non-leaf root has between `1` and `2 * t - 1` keys, all leaves
are at the same depth (`Balanced`), and `toList` is key-sorted. Taking `t = 2` gives 2-3-4 trees.

`induction` is the induction principle for the nested type; proofs use it rather than the raw
nested recursor. The Boolean checkers `occupied`, `balanced` and `isWF` decide the predicates, so
that well-formedness of concrete trees is checked by `decide`. The operations and checkers are
`@[expose]`d so that `decide` and `rfl` evaluate them from other modules.

## Main definitions

* `Cslib.DataStructure.BTree`: classic B-trees with keys in `α` and values in `β`.
* `BTree.Triple`, `BTree.Triple.val`, `BTree.Triple.child`: a node's `(key, value, child)`
  triples and their named components.
* `BTree.toList`, `BTree.size`, `BTree.height`, `BTree.keys`, `BTree.map`, `BTree.foldl`: entries
  in order and the basic API.
* `BTree.Occupied`, `BTree.Balanced`, `BTree.IsWF`: non-root occupancy, equal leaf depth and
  well-formedness at a minimum degree.
* `BTree.occupied`, `BTree.balanced`, `BTree.isWF`: Boolean checkers deciding them.

## Main results

* `BTree.induction`: induction over the nested type.
* `BTree.toList_map`, `BTree.isWF_map`: mapping values maps the entries and keeps
  well-formedness.
* `BTree.IsWF.of_mem_children`: every subtree of a well-formed tree is well-formed.
* `BTree.isWF_iff`: `isWF` decides `IsWF`.

## References

* [R. Bayer and E. McCreight, *Organization and Maintenance of Large Ordered
  Indexes*][BayerMcCreight1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

Ported from `cslib-community/EpsilonEridani` at commit `1966ab476`:
[EpsilonEridani/Algorithms/Lean/BTree/Basic.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Basic.lean).
-/

public section

universe u v w

namespace Cslib.DataStructure

/-- A classic B-tree. A node is a first child followed by `(key, value, child)` triples, so a
node with `m` keys has `m + 1` children by construction. `leaf` is the empty tree. -/
inductive BTree (α : Type u) (β : Type v) : Type (max u v) where
  /-- The empty tree. -/
  | leaf : BTree α β
  /-- A node: its first child, then the keys, values and remaining children in order. -/
  | node (first : BTree α β) (rest : List (α × β × BTree α β)) : BTree α β

namespace BTree

/-- A `(key, value, child)` triple of a node: a key, its value, and the child holding the keys
between this key and the next. The key is the first component `e.1`; `Triple.val` and
`Triple.child` name the other two. -/
abbrev Triple (α : Type u) (β : Type v) : Type (max u v) := α × β × BTree α β

/-- The value of a triple. -/
abbrev Triple.val {α : Type u} {β : Type v} (e : Triple α β) : β := e.2.1

/-- The child of a triple, which follows its key. -/
abbrev Triple.child {α : Type u} {β : Type v} (e : Triple α β) : BTree α β := e.2.2

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The value of a triple built from its components. -/
@[simp] theorem Triple.val_mk (k : α) (v : β) (c : BTree α β) : Triple.val (k, v, c) = v := rfl

/-- The child of a triple built from its components. -/
@[simp] theorem Triple.child_mk (k : α) (v : β) (c : BTree α β) : Triple.child (k, v, c) = c :=
  rfl

mutual
/-- Entries in structural in-order: the first child's, then each key-value pair followed by its
child's. The keys are strictly increasing under `IsWF` (its `sorted` field). -/
@[expose] def toList : BTree α β → List (α × β)
  | leaf => []
  | node first rest => first.toList ++ toListRest rest
/-- Entries of the triples following a first child, each key before its child's entries. -/
@[expose] def toListRest : List (Triple α β) → List (α × β)
  | [] => []
  | (k, v, c) :: rest => (k, v) :: c.toList ++ toListRest rest
end

mutual
/-- Nodes on a root-to-leaf path: the leaf has height `0`. -/
@[expose] def height : BTree α β → ℕ
  | leaf => 0
  | node first rest => max (first.height + 1) (heightRest rest)
/-- Height contribution of the children in a list of triples. -/
@[expose] def heightRest : List (Triple α β) → ℕ
  | [] => 0
  | (_, _, c) :: rest => max (c.height + 1) (heightRest rest)
end

mutual
/-- Map over values, keeping keys and shape. -/
@[expose] def map (f : β → γ) : BTree α β → BTree α γ
  | leaf => leaf
  | node first rest => node (first.map f) (mapRest f rest)
/-- Map over the values of a list of triples. -/
@[expose] def mapRest (f : β → γ) : List (Triple α β) → List (Triple α γ)
  | [] => []
  | (k, v, c) :: rest => (k, f v, c.map f) :: mapRest f rest
end

/-- Number of entries. -/
@[expose] def size (tr : BTree α β) : ℕ := tr.toList.length

/-- Keys in structural in-order, as in `toList`; strictly increasing under `IsWF`. -/
@[expose] def keys (tr : BTree α β) : List α := tr.toList.map Prod.fst

/-- Fold over entries in structural in-order, as in `toList`, which is key order under `IsWF`;
the specification of any direct recursive fold. -/
@[expose] def foldl (f : γ → α × β → γ) (init : γ) (tr : BTree α β) : γ :=
  tr.toList.foldl f init

/-- An entry belongs to a tree when it belongs to its `toList`. -/
instance : Membership (α × β) (BTree α β) := ⟨fun tr p => p ∈ tr.toList⟩

/-- Number of keys at the root node. -/
@[expose] def rootKeys : BTree α β → ℕ
  | leaf => 0
  | node _ rest => rest.length

/-- Children of the root node. -/
@[expose] def children : BTree α β → List (BTree α β)
  | leaf => []
  | node first rest => first :: rest.map Triple.child

/-- Every node satisfies the occupancy bounds of a non-root node of minimum degree `t`: between
`t - 1` and `2 * t - 1` keys. -/
inductive Occupied (t : ℕ) : BTree α β → Prop
  /-- The empty tree is occupied. -/
  | leaf : Occupied t .leaf
  /-- A node is occupied when its key count is in bounds and all its children are occupied. -/
  | node {first : BTree α β} {rest : List (Triple α β)} :
      t - 1 ≤ rest.length → rest.length ≤ 2 * t - 1 →
      Occupied t first → (∀ e ∈ rest, Occupied t e.child) → Occupied t (.node first rest)

/-- All leaves at the same depth: every child of a node has the height of the first child. -/
inductive Balanced : BTree α β → Prop
  /-- The empty tree is balanced. -/
  | leaf : Balanced .leaf
  /-- A node is balanced when its children are balanced and of equal height. -/
  | node {first : BTree α β} {rest : List (Triple α β)} :
      Balanced first → (∀ e ∈ rest, Balanced e.child) →
      (∀ e ∈ rest, e.child.height = first.height) → Balanced (.node first rest)

/-- Well-formed B-tree of minimum degree `t`: root occupancy, non-root occupancy, equal leaf
depth, and key-sortedness of `toList`. -/
structure IsWF [LinearOrder α] (t : ℕ) (tr : BTree α β) : Prop where
  /-- The minimum degree is at least `2`. -/
  two_le : 2 ≤ t
  /-- The root has at most `2 * t - 1` keys. -/
  rootKeys_le : tr.rootKeys ≤ 2 * t - 1
  /-- A non-empty root has at least one key. -/
  rootKeys_pos : tr ≠ .leaf → 1 ≤ tr.rootKeys
  /-- Every child of the root is occupied. -/
  occupied_of_mem_children : ∀ c ∈ tr.children, Occupied t c
  /-- All leaves are at the same depth. -/
  balanced : Balanced tr
  /-- The entries are sorted by strictly increasing key. -/
  sorted : tr.toList.IsSortedAssoc

mutual
/-- Boolean check of `Occupied t`. -/
@[expose] def occupied (t : ℕ) : BTree α β → Bool
  | leaf => true
  | node first rest =>
    decide (t - 1 ≤ rest.length) && decide (rest.length ≤ 2 * t - 1) && occupied t first &&
      occupiedRest t rest
/-- Boolean check that every child in a list of triples is occupied. -/
@[expose] def occupiedRest (t : ℕ) : List (Triple α β) → Bool
  | [] => true
  | (_, _, c) :: rest => occupied t c && occupiedRest t rest
end

mutual
/-- Boolean check of `Balanced`. -/
@[expose] def balanced : BTree α β → Bool
  | leaf => true
  | node first rest => balanced first && balancedRest first.height rest
/-- Boolean check that every child in a list of triples is balanced and of height `h`. -/
@[expose] def balancedRest (h : ℕ) : List (Triple α β) → Bool
  | [] => true
  | (_, _, c) :: rest => balanced c && c.height == h && balancedRest h rest
end

/-- Boolean check of `IsWF t`. -/
@[expose] def isWF [LinearOrder α] (t : ℕ) (tr : BTree α β) : Bool :=
  decide (2 ≤ t) && decide (tr.rootKeys ≤ 2 * t - 1) &&
    (tr matches .leaf || decide (1 ≤ tr.rootKeys)) && tr.children.all (occupied t) &&
    balanced tr && decide tr.toList.IsSortedAssoc

/-! ### Equation lemmas -/

section Equations

variable {first : BTree α β} {rest : List (Triple α β)} {k : α} {v : β} {c : BTree α β}

/-- The empty tree has no entries. -/
@[simp] theorem toList_leaf : (leaf : BTree α β).toList = [] := rfl

/-- The entries of a node: those of its first child, then those of the triples. -/
@[simp] theorem toList_node : (node first rest).toList = first.toList ++ toListRest rest := rfl

/-- An empty list of triples has no entries. -/
theorem toListRest_nil : toListRest ([] : List (Triple α β)) = [] := rfl

/-- The entries of a list of triples: the key, its child's entries, then the rest. -/
theorem toListRest_cons :
    toListRest ((k, v, c) :: rest) = (k, v) :: c.toList ++ toListRest rest := rfl

/-- The entries of a list of triples: each key-value pair followed by its child's entries. -/
@[simp] theorem toListRest_eq_flatMap :
    toListRest rest = rest.flatMap fun e => (e.1, e.val) :: e.child.toList := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp [toListRest_cons, ih]

/-- A list of entries, each over an empty child, has those entries. Not `@[simp]`: the simp
normal form of `toListRest` is the `flatMap` of `toListRest_eq_flatMap`. -/
theorem toListRest_map_leaf (l : List (α × β)) :
    toListRest (l.map fun p => (p.1, p.2, (leaf : BTree α β))) = l := by
  induction l with
  | nil => rfl
  | cons p l ih => simpa using ih

/-- The empty tree has size `0`. -/
@[simp] theorem size_leaf : (leaf : BTree α β).size = 0 := rfl

/-- The empty tree has height `0`. -/
@[simp] theorem height_leaf : (leaf : BTree α β).height = 0 := rfl

/-- The height of a node is one more than that of its tallest child. -/
@[simp] theorem height_node :
    (node first rest).height = max (first.height + 1) (heightRest rest) := rfl

/-- An empty list of triples contributes height `0`. -/
theorem heightRest_nil : heightRest ([] : List (Triple α β)) = 0 := rfl

/-- The height contribution of a list of triples is that of its tallest child. -/
theorem heightRest_cons :
    heightRest ((k, v, c) :: rest) = max (c.height + 1) (heightRest rest) := rfl

/-- The height contribution of a list of triples is the maximum of its children's heights plus
one, or `0` for the empty list. -/
@[simp] theorem heightRest_eq_foldr :
    heightRest rest = (rest.map fun e => e.child.height + 1).foldr max 0 := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp [heightRest_cons, ih]

/-- The children among a list of triples are all shorter than `n` exactly when the list's height
contribution is at most `n`. -/
theorem heightRest_le_iff {n : ℕ} : heightRest rest ≤ n ↔ ∀ e ∈ rest, e.child.height + 1 ≤ n := by
  induction rest with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp only [heightRest_cons, max_le_iff, ih, List.forall_mem_cons]

/-- Mapping the empty tree gives the empty tree. -/
@[simp] theorem map_leaf (f : β → γ) : (leaf : BTree α β).map f = leaf := rfl

/-- Mapping a node maps its first child and its triples. -/
@[simp] theorem map_node (f : β → γ) :
    (node first rest).map f = node (first.map f) (mapRest f rest) := rfl

/-- Mapping an empty list of triples gives the empty list. -/
theorem mapRest_nil (f : β → γ) : mapRest f ([] : List (Triple α β)) = [] := rfl

/-- Mapping a list of triples maps the value and the child of its head, then the rest. -/
theorem mapRest_cons (f : β → γ) :
    mapRest f ((k, v, c) :: rest) = (k, f v, c.map f) :: mapRest f rest := rfl

/-- Mapping a list of triples maps the value and the child of each triple, keeping its key. -/
@[simp] theorem mapRest_eq_map (f : β → γ) :
    mapRest f rest = rest.map fun e => (e.1, f e.val, e.child.map f) := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp [mapRest_cons, ih]

/-- The empty tree has no children. -/
@[simp] theorem children_leaf : (leaf : BTree α β).children = [] := rfl

/-- The children of a node: its first child, then the children of its triples. -/
@[simp] theorem children_node : (node first rest).children = first :: rest.map Triple.child := rfl

/-- The empty tree has no keys at its root. -/
@[simp] theorem rootKeys_leaf : (leaf : BTree α β).rootKeys = 0 := rfl

/-- A node has one root key per triple. -/
@[simp] theorem rootKeys_node : (node first rest).rootKeys = rest.length := rfl

/-- The first separator splits a node's entries into those of its first child, the separator, and
those of the node without its first child and separator. -/
theorem mem_toList_node_cons {p : α × β} :
    p ∈ (node first ((k, v, c) :: rest)).toList ↔
      p ∈ first.toList ∨ p = (k, v) ∨ p ∈ (node c rest).toList := by
  simp only [toList_node, toListRest_cons, List.cons_append, List.mem_append, List.mem_cons]

/-- Dropping a node's first child and first separator keeps the remaining children. -/
theorem children_node_subset_children_node_cons :
    (node c rest).children ⊆ (node first ((k, v, c) :: rest)).children := by
  intro c' h
  simp only [children_node, List.map_cons, List.mem_cons] at h ⊢
  tauto

end Equations

variable {tr : BTree α β}

/-! ### Induction -/

/-- Induction on B-trees, with a hypothesis for the first child and for every child among the
triples. This replaces the raw nested recursor in proofs. -/
theorem induction {motive : BTree α β → Prop} (leaf : motive .leaf)
    (node : ∀ (first : BTree α β) (rest : List (Triple α β)), motive first →
      (∀ e ∈ rest, motive e.child) → motive (.node first rest)) :
    ∀ tr, motive tr
  | .leaf => leaf
  | .node first rest =>
    node first rest (induction leaf node first) fun e _ => induction leaf node e.child
termination_by tr => sizeOf tr
decreasing_by
  · simp_wf
    omega
  · have := List.sizeOf_lt_of_mem ‹e ∈ rest›
    obtain ⟨a, b, c⟩ := e
    simp only [Prod.mk.sizeOf_spec] at this
    simp_wf
    omega

attribute [induction_eliminator] induction

/-! ### Basic API -/

/-- Membership in a tree is membership in its entries. -/
@[simp] theorem mem_def {p : α × β} : p ∈ tr ↔ p ∈ tr.toList := Iff.rfl

/-- The length of the entries is the size. -/
@[simp] theorem length_toList : tr.toList.length = tr.size := rfl

/-- The entries of a list of triples: one per key, plus those of the children. -/
theorem length_toListRest {rest : List (Triple α β)} :
    (toListRest rest).length = rest.length + (rest.map fun e => e.child.size).sum := by
  simp [List.length_flatMap, List.sum_map_add, Nat.add_comm]

/-- The size of a node: its first child's, one per key, and its other children's. -/
theorem size_node {first : BTree α β} {rest : List (Triple α β)} :
    (node first rest).size = first.size + rest.length + (rest.map fun e => e.child.size).sum := by
  rw [← length_toList, toList_node, List.length_append, length_toListRest, length_toList,
    Nat.add_assoc]

/-- `foldl` is the fold over `toList`. -/
theorem foldl_def (f : γ → α × β → γ) (init : γ) : tr.foldl f init = tr.toList.foldl f init :=
  rfl

/-- `keys` is the list of first components of `toList`. -/
theorem keys_def : tr.keys = tr.toList.map Prod.fst := rfl

/-- A key belongs to a tree's keys when some entry of the tree carries it. -/
@[simp] theorem mem_keys {k : α} : k ∈ tr.keys ↔ ∃ v, (k, v) ∈ tr := by
  simp only [keys_def, List.mem_map, mem_def]
  constructor
  · rintro ⟨⟨k, v⟩, hp, rfl⟩
    exact ⟨v, hp⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, hv, rfl⟩

/-- Only the empty tree has height `0`. -/
@[simp] theorem height_eq_zero_iff : tr.height = 0 ↔ tr = .leaf := by
  cases tr with
  | leaf => simp
  | node first rest => simp

/-- Mapping over values maps the entries, keeping keys. -/
@[simp] theorem toList_map (f : β → γ) :
    (tr.map f).toList = tr.toList.map fun p => (p.1, f p.2) := by
  induction tr with
  | leaf => rfl
  | node first rest ih₁ ih₂ =>
    simp only [map_node, toList_node, toListRest_eq_flatMap, mapRest_eq_map, List.map_append, ih₁,
      List.flatMap_map, List.map_flatMap, List.map_cons]
    exact congrArg _ (List.flatMap_congr fun e he => by rw [ih₂ e he])

/-- Mapping over values keeps the height. -/
@[simp] theorem height_map (f : β → γ) : (tr.map f).height = tr.height := by
  induction tr with
  | leaf => rfl
  | node first rest ih₁ ih₂ =>
    simp only [map_node, height_node, heightRest_eq_foldr, mapRest_eq_map, ih₁, List.map_map]
    exact congrArg _ (congrArg _ (List.map_congr_left fun e he => by simp [ih₂ e he]))

/-- Mapping over values keeps the size. -/
@[simp] theorem size_map (f : β → γ) : (tr.map f).size = tr.size := by
  simp [← length_toList]

/-- Mapping over values keeps the keys. -/
@[simp] theorem keys_map (f : β → γ) : (tr.map f).keys = tr.keys := by
  simp [keys, Function.comp_def]

/-- Mapping over values gives the empty tree exactly when the tree is empty. -/
@[simp] theorem map_eq_leaf_iff (f : β → γ) : tr.map f = leaf ↔ tr = leaf := by
  cases tr <;> simp

/-- Mapping over values keeps the number of root keys. -/
@[simp] theorem rootKeys_map (f : β → γ) : (tr.map f).rootKeys = tr.rootKeys := by
  cases tr <;> simp

/-- The children of a mapped tree are the mapped children. -/
@[simp] theorem children_map (f : β → γ) : (tr.map f).children = tr.children.map (·.map f) := by
  cases tr with
  | leaf => rfl
  | node first rest =>
    simp [Function.comp_def]

/-- Mapping the identity leaves the tree unchanged. -/
@[simp] theorem map_id : tr.map id = tr := by
  induction tr with
  | leaf => rfl
  | node first rest ih₁ ih₂ =>
    rw [map_node, ih₁, mapRest_eq_map]
    exact congrArg _ ((List.map_congr_left (g := fun e => e) fun e he => by simp [ih₂ e he]).trans
      (List.map_id' rest))

/-- Mapping twice is mapping the composition. -/
@[simp] theorem map_map {δ : Type*} (g : γ → δ) (f : β → γ) :
    (tr.map f).map g = tr.map (g ∘ f) := by
  induction tr with
  | leaf => rfl
  | node first rest ih₁ ih₂ =>
    simp only [map_node, ih₁, mapRest_eq_map, List.map_map]
    exact congrArg _ (List.map_congr_left fun e he => by simp [ih₂ e he])

/-- The entries of a concatenation of triple lists are the concatenated entries. -/
theorem toListRest_append {l₁ l₂ : List (Triple α β)} :
    toListRest (l₁ ++ l₂) = toListRest l₁ ++ toListRest l₂ := by
  simp [List.flatMap_append]

/-- The entries of a child among the triples form a sublist of the triples' entries. -/
theorem toList_sublist_toListRest_of_mem {rest : List (Triple α β)}
    {e : Triple α β} (he : e ∈ rest) : e.child.toList.Sublist (toListRest rest) := by
  rw [toListRest_eq_flatMap]
  exact (List.sublist_cons_self _ _).trans (List.sublist_flatten_of_mem (List.mem_map_of_mem he))

/-- The entries of a child of the root form a sublist of the tree's entries. -/
theorem toList_sublist_of_mem_children {c : BTree α β} (hc : c ∈ tr.children) :
    c.toList.Sublist tr.toList := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rw [toList_node]
    rcases hc with rfl | ⟨e, he, rfl⟩
    · exact List.sublist_append_left _ _
    · exact (toList_sublist_toListRest_of_mem he).trans (List.sublist_append_right _ _)

/-- Every child among the triples of a node is shorter than the node. -/
theorem height_succ_le_of_mem_rest {first : BTree α β} {rest : List (Triple α β)}
    {e : Triple α β} (he : e ∈ rest) : e.child.height + 1 ≤ (node first rest).height := by
  have := heightRest_le_iff.1 le_rfl e he
  rw [height_node]
  omega

/-- The first child of a node is shorter than the node. -/
theorem height_first_succ_le {first : BTree α β} {rest : List (Triple α β)} :
    first.height + 1 ≤ (node first rest).height := by
  rw [height_node]
  omega

/-- Dropping a node's first child and first key leaves a tree no taller than the node. -/
theorem height_node_le_height_node_cons {first c : BTree α β} {k : α} {v : β}
    {rest : List (Triple α β)} :
    (node c rest).height ≤ (node first ((k, v, c) :: rest)).height := by
  simp only [height_node, heightRest_cons]
  omega

/-- Every child of a tree is shorter than the tree. -/
theorem height_succ_le_of_mem_children {c : BTree α β} (hc : c ∈ tr.children) :
    c.height + 1 ≤ tr.height := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    · rw [height_node]
      omega
    · exact height_succ_le_of_mem_rest he

/-! ### Inversion lemmas -/

section Inversion

variable {fst : BTree α β} {rest : List (Triple α β)} {t : ℕ}

/-- Every child among the triples of a balanced node has the height of the first child. -/
theorem Balanced.height_of_mem_rest (h : Balanced (.node fst rest)) {e : Triple α β}
    (he : e ∈ rest) : e.child.height = fst.height := by
  cases h with
  | node _ _ h => exact h e he

/-- A balanced node is one taller than its first child. -/
theorem Balanced.height_node (h : Balanced (.node fst rest)) :
    (BTree.node fst rest).height = fst.height + 1 := by
  have := heightRest_le_iff.2 fun e he => Nat.succ_le_succ (h.height_of_mem_rest he).le
  rw [BTree.height_node]
  omega

/-- The first child of a balanced node is balanced. -/
theorem Balanced.first (h : Balanced (.node fst rest)) : Balanced fst := by
  cases h
  assumption

/-- Every child among the triples of a balanced node is balanced. -/
theorem Balanced.of_mem_rest (h : Balanced (.node fst rest)) {e : Triple α β}
    (he : e ∈ rest) : Balanced e.child := by
  cases h with
  | node _ h _ => exact h e he

/-- A node whose children are balanced and as tall as its first child is balanced, and one
taller than its first child. -/
theorem balanced_node_of_forall {first : BTree α β} {rest : List (Triple α β)}
    (hf : Balanced first) (hr : ∀ e ∈ rest, Balanced e.child ∧ e.child.height = first.height) :
    Balanced (.node first rest) ∧ (BTree.node first rest).height = first.height + 1 :=
  have hb : Balanced (.node first rest) :=
    .node hf (fun e he => (hr e he).1) fun e he => (hr e he).2
  ⟨hb, hb.height_node⟩

/-- Children of a balanced tree are one level shorter. -/
theorem Balanced.height_of_mem_children {c : BTree α β} (h : Balanced tr) (hc : c ∈ tr.children) :
    c.height + 1 = tr.height := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    rw [h.height_node]
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    · rfl
    · rw [h.height_of_mem_rest he]

/-- Children of a balanced tree are balanced. -/
theorem Balanced.of_mem_children {c : BTree α β} (h : Balanced tr) (hc : c ∈ tr.children) :
    Balanced c := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    · exact h.first
    · exact h.of_mem_rest he

/-- The first child of an occupied node is occupied. -/
theorem Occupied.first (h : Occupied t (.node fst rest)) : Occupied t fst := by
  cases h
  assumption

/-- Every child among the triples of an occupied node is occupied. -/
theorem Occupied.of_mem_rest (h : Occupied t (.node fst rest)) {e : Triple α β}
    (he : e ∈ rest) : Occupied t e.child := by
  cases h with
  | node _ _ _ h => exact h e he

/-- An occupied node has at most `2 * t - 1` keys. -/
theorem Occupied.length_le (h : Occupied t (.node fst rest)) : rest.length ≤ 2 * t - 1 := by
  cases h
  assumption

/-- An occupied node has at least `t - 1` keys. -/
theorem Occupied.le_length (h : Occupied t (.node fst rest)) : t - 1 ≤ rest.length := by
  cases h
  assumption

/-- An occupied tree has at most `2 * t - 1` root keys. -/
theorem Occupied.rootKeys_le {c : BTree α β} (h : Occupied t c) : c.rootKeys ≤ 2 * t - 1 := by
  cases c with
  | leaf => simp
  | node _ _ => exact h.length_le

/-- An occupied node has at least `t - 1` root keys. -/
theorem Occupied.le_rootKeys {c : BTree α β} (h : Occupied t c) (hne : c ≠ .leaf) :
    t - 1 ≤ c.rootKeys := by
  cases c with
  | leaf => exact absurd rfl hne
  | node _ _ => exact h.le_length

/-- An occupied node has at least one key when `2 ≤ t`. -/
theorem Occupied.one_le_rootKeys {c : BTree α β} (ht : 2 ≤ t) (h : Occupied t c)
    (hne : c ≠ .leaf) : 1 ≤ c.rootKeys := by
  have := h.le_rootKeys hne
  omega

/-- Children of an occupied tree are occupied. -/
theorem Occupied.of_mem_children {c : BTree α β} (h : Occupied t tr) (hc : c ∈ tr.children) :
    Occupied t c := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    · exact h.first
    · exact h.of_mem_rest he

/-- Mapping over values preserves occupancy. -/
@[simp] theorem occupied_map (f : β → γ) : Occupied t (tr.map f) ↔ Occupied t tr := by
  induction tr with
  | leaf => exact ⟨fun _ => .leaf, fun _ => .leaf⟩
  | node first rest ih₁ ih₂ =>
    rw [map_node, mapRest_eq_map]
    constructor
    · intro h
      have h₁ := h.le_length
      have h₂ := h.length_le
      rw [List.length_map] at h₁ h₂
      exact .node h₁ h₂ (ih₁.1 h.first) fun e he =>
        (ih₂ e he).1 (h.of_mem_rest (List.mem_map_of_mem he))
    · intro h
      refine .node ?_ ?_ (ih₁.2 h.first) fun e he => ?_
      · rw [List.length_map]
        exact h.le_length
      · rw [List.length_map]
        exact h.length_le
      · obtain ⟨e, he', rfl⟩ := List.mem_map.1 he
        exact (ih₂ e he').2 (h.of_mem_rest he')

/-- Mapping over values preserves balance. -/
@[simp] theorem balanced_map (f : β → γ) : Balanced (tr.map f) ↔ Balanced tr := by
  induction tr with
  | leaf => exact ⟨fun _ => .leaf, fun _ => .leaf⟩
  | node first rest ih₁ ih₂ =>
    rw [map_node, mapRest_eq_map]
    constructor
    · intro h
      refine .node (ih₁.1 h.first) (fun e he => ?_) fun e he => ?_
      · exact (ih₂ e he).1 (h.of_mem_rest (List.mem_map_of_mem he))
      · simpa using h.height_of_mem_rest (List.mem_map_of_mem he)
    · intro h
      refine .node (ih₁.2 h.first) (fun e he => ?_) fun e he => ?_
      · obtain ⟨e, he', rfl⟩ := List.mem_map.1 he
        exact (ih₂ e he').2 (h.of_mem_rest he')
      · obtain ⟨e, he', rfl⟩ := List.mem_map.1 he
        simpa using h.height_of_mem_rest he'

/-- Splitting a node with occupied children at its first separator: the first child is occupied,
and so are the children of the first child and of the node without its first child and
separator. -/
theorem occupied_children_node_cons {first c : BTree α β} {k : α} {v : β}
    {rest : List (Triple α β)}
    (hc : ∀ c' ∈ (node first ((k, v, c) :: rest)).children, Occupied t c') :
    Occupied t first ∧ (∀ c' ∈ first.children, Occupied t c') ∧
      ∀ c' ∈ (node c rest).children, Occupied t c' := by
  have hfirst : Occupied t first := hc first (by simp)
  exact ⟨hfirst, fun _ h => hfirst.of_mem_children h,
    fun c' h => hc c' (children_node_subset_children_node_cons h)⟩

end Inversion

section LinearOrder

variable [LinearOrder α] {t : ℕ} {c : BTree α β}

/-- The first child of a well-formed node is occupied. -/
theorem IsWF.occupied_first {first : BTree α β} {rest : List (Triple α β)}
    (h : IsWF t (node first rest)) : Occupied t first :=
  h.occupied_of_mem_children first List.mem_cons_self

/-- Every child among the triples of a well-formed node is occupied. -/
theorem IsWF.occupied_of_mem_rest {first : BTree α β} {rest : List (Triple α β)}
    {e : Triple α β} (h : IsWF t (node first rest)) (he : e ∈ rest) :
    Occupied t e.child :=
  h.occupied_of_mem_children _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))

/-- Every child of a well-formed tree has sorted entries. -/
theorem IsWF.sorted_of_mem_children (h : IsWF t tr) (hc : c ∈ tr.children) :
    c.toList.IsSortedAssoc :=
  h.sorted.sublist (toList_sublist_of_mem_children hc)

/-- An occupied, balanced tree with sorted entries is well-formed when `2 ≤ t`: the occupancy of a
non-root node implies the root rule. -/
theorem Occupied.isWF (ht : 2 ≤ t) (ho : Occupied t c) (hb : Balanced c)
    (hs : c.toList.IsSortedAssoc) : IsWF t c where
  two_le := ht
  rootKeys_le := ho.rootKeys_le
  rootKeys_pos := ho.one_le_rootKeys ht
  occupied_of_mem_children _ hc := ho.of_mem_children hc
  balanced := hb
  sorted := hs

/-- Every subtree of a well-formed tree is well-formed: non-root occupancy implies the root rule
when `2 ≤ t`. -/
theorem IsWF.of_mem_children (h : IsWF t tr) (hc : c ∈ tr.children) : IsWF t c :=
  (h.occupied_of_mem_children c hc).isWF h.two_le (h.balanced.of_mem_children hc)
    (h.sorted_of_mem_children hc)

/-- Mapping over values preserves well-formedness. -/
@[simp] theorem isWF_map (f : β → γ) : IsWF t (tr.map f) ↔ IsWF t tr := by
  have hs : (tr.map f).toList.IsSortedAssoc ↔ tr.toList.IsSortedAssoc := by
    rw [List.isSortedAssoc_iff_pairwise, List.isSortedAssoc_iff_pairwise, ← keys_def, ← keys_def,
      keys_map]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨h₁, by simpa using h₂, fun hne => by simpa using h₃ (by simpa using hne), ?_,
      by simpa using h₅, hs.1 h₆⟩
    simpa using h₄
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨h₁, by simpa using h₂, fun hne => by simpa using h₃ (by simpa using hne), ?_,
      by simpa using h₅, hs.2 h₆⟩
    simpa using h₄

/-- A node's entries are sorted exactly when those of its first child and of the node without its
first child and separator are, with the first separator strictly between them. -/
theorem isSortedAssoc_toList_node_cons_iff {first : BTree α β} {k : α} {v : β}
    {rest : List (Triple α β)} :
    (node first ((k, v, c) :: rest)).toList.IsSortedAssoc ↔
      first.toList.IsSortedAssoc ∧ (node c rest).toList.IsSortedAssoc ∧
        (∀ p ∈ first.toList, p.1 < k) ∧ ∀ p ∈ (node c rest).toList, k < p.1 := by
  rw [toList_node, toListRest_cons, List.cons_append, List.isSortedAssoc_append_cons_iff,
    toList_node]

end LinearOrder

/-! ### Decidability -/

section Decidability

variable {rest : List (Triple α β)} {t n : ℕ}

/-- `occupiedRest` checks every child among the triples with `occupied`. -/
@[simp] theorem occupiedRest_eq_all :
    occupiedRest t rest = rest.all fun e => occupied t e.child := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp [occupiedRest, ih]

/-- `balancedRest n` checks that every child among the triples is balanced and of height `n`. -/
@[simp] theorem balancedRest_eq_all :
    balancedRest n rest = rest.all fun e => balanced e.child && e.child.height == n := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp [balancedRest, ih, Bool.and_assoc]

/-- `occupied` decides `Occupied`. -/
@[simp] theorem occupied_iff : occupied t tr = true ↔ Occupied t tr := by
  induction tr with
  | leaf => exact ⟨fun _ => .leaf, fun _ => rfl⟩
  | node first rest ih₁ ih₂ =>
    rw [occupied, occupiedRest_eq_all]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, ih₁]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
      exact .node h₁ h₂ h₃ fun e he => (ih₂ e he).1 (h₄ e he)
    · intro h
      cases h with
      | node h₁ h₂ h₃ h₄ => exact ⟨⟨⟨h₁, h₂⟩, h₃⟩, fun e he => (ih₂ e he).2 (h₄ e he)⟩

/-- `balanced` decides `Balanced`. -/
@[simp] theorem balanced_iff : balanced tr = true ↔ Balanced tr := by
  induction tr with
  | leaf => exact ⟨fun _ => .leaf, fun _ => rfl⟩
  | node first rest ih₁ ih₂ =>
    rw [balanced, balancedRest_eq_all]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, ih₁]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact .node h₁ (fun e he => (ih₂ e he).1 (h₂ e he).1) fun e he => (h₂ e he).2
    · intro h
      cases h with
      | node h₁ h₂ h₃ => exact ⟨h₁, fun e he => ⟨(ih₂ e he).2 (h₂ e he), h₃ e he⟩⟩

/-- `isWF` decides `IsWF`. -/
@[simp] theorem isWF_iff [LinearOrder α] : isWF t tr = true ↔ IsWF t tr := by
  simp only [isWF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    occupied_iff, balanced_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩
    refine ⟨h₁, h₂, fun hne => ?_, h₄, h₅, h₆⟩
    cases tr with
    | leaf => exact absurd rfl hne
    | node => simpa using h₃
  · intro h
    refine ⟨⟨⟨⟨⟨h.two_le, h.rootKeys_le⟩, ?_⟩, h.occupied_of_mem_children⟩, h.balanced⟩, h.sorted⟩
    cases tr with
    | leaf => simp
    | node => exact Or.inr (h.rootKeys_pos nofun)

end Decidability

instance (t : ℕ) (tr : BTree α β) : Decidable (Occupied t tr) := decidable_of_iff _ occupied_iff

instance (tr : BTree α β) : Decidable (Balanced tr) := decidable_of_iff _ balanced_iff

instance [LinearOrder α] (t : ℕ) (tr : BTree α β) : Decidable (IsWF t tr) :=
  decidable_of_iff _ isWF_iff

end BTree

end Cslib.DataStructure
