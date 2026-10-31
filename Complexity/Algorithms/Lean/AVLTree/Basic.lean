/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.SearchTree.Cost
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Log

/-!
# Height-balanced AVL binary search trees

This module defines executable height-cached AVL binary search trees over any `LinearOrder α`,
proves preservation of strict key ordering, cached heights, and the AVL balance invariant across
rotations and insertion, and derives the logarithmic height bound
`t.cachedHeight ≤ 2 * Nat.log 2 ((elements t).card + 1)`.

Each tree projects to `BinaryTree α` via `toBinaryTree`, reusing key-set semantics, strict ordering,
and query contracts from `Cslib.Algorithms.Lean.SearchTree`. Following
[Cormen et al., Problem 13-3][CLRS2009], every node caches its subtree height so `balance` checks
height differences in `O(1)` without rescanning subtrees. Heights use `BinaryTree.height`'s
node-count convention (`0` for `.nil`, `1` for a singleton leaf, i.e., `h_CLRS + 1` on nonempty
trees), under which the minimum node count of a balanced tree of cached height `h` satisfies the
exact Fibonacci lower bound `Nat.fib (h + 2) ≤ t.numNodes + 1`.

## Main definitions

* `Cslib.Algorithms.Lean.AVLTree`: binary search tree caching subtree heights at internal nodes.
* `toBinaryTree`, `cachedHeight`, `numNodes`, `elements`: structural projection, O(1) height read,
  node count, and represented `Finset α`.
* `Ordered`, `HeightConsistent`, `Balanced`, `Valid`: strict BST ordering, cached-height accuracy,
  `±1` sibling-height balance, and combined AVL validity.
* `mkNode`, `rotateRight`, `rotateLeft`, `balance`: height-maintaining constructor, single
  rotations, and single/double rebalancing for sibling heights differing by at most `2`.
* `contains`, `minimum`, `successor`, `insert`: executable search queries and rebalancing insertion.
* `searchVisits`, `minimumVisits`, `successorVisits`: downward search-path internal-node visit
  counts matching `Cslib.Algorithms.Lean.SearchTree`.

## Main results

* `cachedHeight_eq_height`: under `HeightConsistent`, `cachedHeight` equals `toBinaryTree.height`.
* `fib_height_le_numNodes_add_one`: Fibonacci node-count lower bound
  `Nat.fib (t.cachedHeight + 2) ≤ t.numNodes + 1`.
* `Valid.cachedHeight_le_two_mul_log`: logarithmic height bound
  `t.cachedHeight ≤ 2 * Nat.log 2 ((elements t).card + 1)`.
* `contains_eq_true`, `minimum_spec`, `successor_spec`: query correctness under `Ordered`.
* `elements_balance`, `ordered_balance`, `heightConsistent_balance`, `balanced_and_height_balance`:
  semantic and structural contracts for `balance`, shared with deletion in `AVLTree.Erase`.
* `elements_insert`, `valid_insert`, `cachedHeight_insert_le`, `insert_eq_self`: set semantics,
  AVL validity preservation, height-growth bound, and duplicate idempotence for `insert`.
* `searchVisits_le_cachedHeight`, `minimumVisits_le_cachedHeight`,
  `successorVisits_le_cachedHeight`: path-visit upper bounds by `t.cachedHeight`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Problem 13-3][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean

/-- A binary search tree storing cached subtree heights at internal nodes. -/
inductive AVLTree (α : Type*) where
  /-- Empty tree of height `0`. -/
  | nil : AVLTree α
  /-- Internal node storing `key`, cached subtree height `cachedHeight`, and children. -/
  | node (key : α) (cachedHeight : ℕ) (left : AVLTree α) (right : AVLTree α) : AVLTree α
  deriving DecidableEq, Repr

namespace AVLTree

open Cslib.OrderedSet

section Structure

variable {α : Type*}

/-- Read the cached subtree height in `O(1)` without traversing children. -/
@[expose] def cachedHeight : AVLTree α → ℕ
  | .nil => 0
  | .node _ h _ _ => h

/-- Forget cached heights to obtain the underlying `BinaryTree α`. -/
@[expose] def toBinaryTree : AVLTree α → BinaryTree α
  | .nil => .nil
  | .node a _ l r => .node a l.toBinaryTree r.toBinaryTree

/-- Number of internal nodes in `t`. -/
@[expose] def numNodes (t : AVLTree α) : ℕ :=
  t.toBinaryTree.numNodes

/-- The empty tree has cached height `0`. -/
@[simp]
theorem cachedHeight_nil : cachedHeight (.nil : AVLTree α) = 0 := rfl

/-- An internal node's `cachedHeight` returns its stored height field. -/
@[simp]
theorem cachedHeight_node (a : α) (h : ℕ) (l r : AVLTree α) :
    cachedHeight (.node a h l r) = h := rfl

/-- Forgetting heights maps `.nil` to `BinaryTree.nil`. -/
@[simp]
theorem toBinaryTree_nil : toBinaryTree (.nil : AVLTree α) = .nil := rfl

/-- Forgetting heights maps `.node` to `BinaryTree.node` recursively. -/
@[simp]
theorem toBinaryTree_node (a : α) (h : ℕ) (l r : AVLTree α) :
    toBinaryTree (.node a h l r) = .node a l.toBinaryTree r.toBinaryTree := rfl

/-- The empty tree has `0` internal nodes. -/
@[simp]
theorem numNodes_nil : numNodes (.nil : AVLTree α) = 0 := rfl

/-- An internal node has `1 + l.numNodes + r.numNodes` nodes. -/
@[simp]
theorem numNodes_node (a : α) (h : ℕ) (l r : AVLTree α) :
    numNodes (.node a h l r) = 1 + l.numNodes + r.numNodes := by
  simp only [numNodes, toBinaryTree_node, BinaryTree.numNodes]
  omega

/-- Every internal node's `cachedHeight` equals `1 + max l.cachedHeight r.cachedHeight`. -/
@[expose] def HeightConsistent : AVLTree α → Prop
  | .nil => True
  | .node _ h l r =>
      h = 1 + max l.cachedHeight r.cachedHeight ∧ HeightConsistent l ∧ HeightConsistent r

/-- Every internal node's children have cached heights differing by at most `1`. -/
@[expose] def Balanced : AVLTree α → Prop
  | .nil => True
  | .node _ _ l r =>
      l.cachedHeight ≤ r.cachedHeight + 1 ∧
        r.cachedHeight ≤ l.cachedHeight + 1 ∧
        Balanced l ∧ Balanced r

/-- Under `HeightConsistent`, `cachedHeight` agrees with `BinaryTree.height` of `toBinaryTree`. -/
theorem cachedHeight_eq_height {t : AVLTree α} (hc : HeightConsistent t) :
    t.cachedHeight = t.toBinaryTree.height := by
  induction t with
  | nil => rfl
  | node a h l r ihl ihr =>
    obtain ⟨hh, hcl, hcr⟩ := hc
    simp only [cachedHeight_node, toBinaryTree_node, BinaryTree.height, hh, ihl hcl, ihr hcr]
    omega

/-- Fibonacci node-count lower bound ([Cormen et al., Problem 13-3(a)][CLRS2009]): any
height-consistent, AVL-balanced tree `t` satisfies
`Nat.fib (t.cachedHeight + 2) ≤ t.numNodes + 1`. -/
theorem fib_height_le_numNodes_add_one {t : AVLTree α}
    (hc : HeightConsistent t) (hb : Balanced t) :
    Nat.fib (t.cachedHeight + 2) ≤ t.numNodes + 1 := by
  induction t with
  | nil => simp
  | node a h l r ihl ihr =>
    obtain ⟨hh, hcl, hcr⟩ := hc
    obtain ⟨hlr, hrl, hbl, hbr⟩ := hb
    have il := ihl hcl hbl
    have ir := ihr hcr hbr
    rw [numNodes_node]
    by_cases hle : r.cachedHeight ≤ l.cachedHeight
    · have hmax : h = l.cachedHeight + 1 := by omega
      have hfib : Nat.fib (h + 2) =
          Nat.fib (l.cachedHeight + 1) + Nat.fib (l.cachedHeight + 2) := by
        rw [hmax]
        exact Nat.fib_add_two
      have hmono : Nat.fib (l.cachedHeight + 1) ≤ Nat.fib (r.cachedHeight + 2) :=
        Nat.fib_mono (by omega)
      simp only [cachedHeight_node]
      omega
    · have hmax : h = r.cachedHeight + 1 := by omega
      have hfib : Nat.fib (h + 2) =
          Nat.fib (r.cachedHeight + 1) + Nat.fib (r.cachedHeight + 2) := by
        rw [hmax]
        exact Nat.fib_add_two
      have hmono : Nat.fib (r.cachedHeight + 1) ≤ Nat.fib (l.cachedHeight + 2) :=
        Nat.fib_mono (by omega)
      simp only [cachedHeight_node]
      omega

private theorem two_pow_half_succ_le_fib : ∀ h : ℕ, 2 ^ ((h + 1) / 2) ≤ Nat.fib (h + 2)
  | 0 => by decide
  | 1 => by decide
  | h + 2 => by
    have ih := two_pow_half_succ_le_fib h
    have hdiv : (h + 2 + 1) / 2 = (h + 1) / 2 + 1 := by omega
    have hfib : Nat.fib (h + 2 + 2) = Nat.fib (h + 2) + Nat.fib (h + 2 + 1) := Nat.fib_add_two
    have hmono : Nat.fib (h + 2) ≤ Nat.fib (h + 2 + 1) := Nat.fib_le_fib_succ
    rw [hdiv, pow_succ]
    omega

/-- Construct a node computing its cached height in `O(1)` from its children's cached heights. -/
@[expose] def mkNode (a : α) (l r : AVLTree α) : AVLTree α :=
  .node a (1 + max l.cachedHeight r.cachedHeight) l r

/-- `mkNode` sets `cachedHeight` to `1 + max l.cachedHeight r.cachedHeight`. -/
@[simp]
theorem cachedHeight_mkNode (a : α) (l r : AVLTree α) :
    (mkNode a l r).cachedHeight = 1 + max l.cachedHeight r.cachedHeight := rfl

/-- `mkNode` projects to `BinaryTree.node` under `toBinaryTree`. -/
@[simp]
theorem toBinaryTree_mkNode (a : α) (l r : AVLTree α) :
    (mkNode a l r).toBinaryTree = .node a l.toBinaryTree r.toBinaryTree := rfl

/-- `mkNode` preserves `HeightConsistent` whenever both children are height-consistent. -/
theorem heightConsistent_mkNode {a : α} {l r : AVLTree α}
    (hl : HeightConsistent l) (hr : HeightConsistent r) :
    HeightConsistent (mkNode a l r) :=
  ⟨rfl, hl, hr⟩

/-- Single right rotation around `a` and a nonempty left child. -/
@[expose] def rotateRight (a : α) : AVLTree α → AVLTree α → AVLTree α
  | .node la _ ll lr, r => mkNode la ll (mkNode a lr r)
  | .nil, r => mkNode a .nil r

/-- Single left rotation around `a` and a nonempty right child. -/
@[expose] def rotateLeft (a : α) (l : AVLTree α) : AVLTree α → AVLTree α
  | .node ra _ rl rr => mkNode ra (mkNode a l rl) rr
  | .nil => mkNode a l .nil

/-- Rebalance a node whose children are height-balanced and differ in height by at most `2`
([Cormen et al., Problem 13-3(b)][CLRS2009]). Inspects only `O(1)` cached child/grandchild
heights. -/
@[expose] def balance (a : α) (l r : AVLTree α) : AVLTree α :=
  if r.cachedHeight + 1 < l.cachedHeight then
    match l with
    | .nil => mkNode a l r
    | .node la _ ll lr =>
      if lr.cachedHeight ≤ ll.cachedHeight then
        rotateRight a l r
      else
        rotateRight a (rotateLeft la ll lr) r
  else if l.cachedHeight + 1 < r.cachedHeight then
    match r with
    | .nil => mkNode a l r
    | .node ra _ rl rr =>
      if rl.cachedHeight ≤ rr.cachedHeight then
        rotateLeft a l r
      else
        rotateLeft a l (rotateRight ra rl rr)
  else
    mkNode a l r

/-- Single right rotation preserves `HeightConsistent`. -/
theorem heightConsistent_rotateRight {a : α} {l r : AVLTree α}
    (hl : HeightConsistent l) (hr : HeightConsistent r) :
    HeightConsistent (rotateRight a l r) := by
  cases l with
  | nil => exact ⟨rfl, trivial, hr⟩
  | node la lh ll lr =>
    exact ⟨rfl, hl.2.1, ⟨rfl, hl.2.2, hr⟩⟩

/-- Single left rotation preserves `HeightConsistent`. -/
theorem heightConsistent_rotateLeft {a : α} {l r : AVLTree α}
    (hl : HeightConsistent l) (hr : HeightConsistent r) :
    HeightConsistent (rotateLeft a l r) := by
  cases r with
  | nil => exact ⟨rfl, hl, trivial⟩
  | node ra rh rl rr =>
    exact ⟨rfl, ⟨rfl, hl, hr.2.1⟩, hr.2.2⟩

/-- `balance` preserves `HeightConsistent`. -/
theorem heightConsistent_balance {a : α} {l r : AVLTree α}
    (hl : HeightConsistent l) (hr : HeightConsistent r) :
    HeightConsistent (balance a l r) := by
  unfold balance
  split
  · cases l with
    | nil => exact ⟨rfl, trivial, hr⟩
    | node la lh ll lr =>
      dsimp only
      split
      · exact heightConsistent_rotateRight hl hr
      · exact heightConsistent_rotateRight (heightConsistent_rotateLeft hl.2.1 hl.2.2) hr
  · split
    · cases r with
      | nil => exact ⟨rfl, hl, trivial⟩
      | node ra rh rl rr =>
        dsimp only
        split
        · exact heightConsistent_rotateLeft hl hr
        · exact heightConsistent_rotateLeft hl (heightConsistent_rotateRight hr.2.1 hr.2.2)
    · exact ⟨rfl, hl, hr⟩

/-- Main structural contract of `balance`: when `l` and `r` are height-consistent, balanced, and
differ in height by at most `2`, `balance a l r` is balanced and its height lies in
`[max l.cachedHeight r.cachedHeight, 1 + max l.cachedHeight r.cachedHeight]` (equaling
`1 + max l.cachedHeight r.cachedHeight` whenever `l` and `r` already differ by at most `1`). -/
theorem balanced_and_height_balance (a : α) {l r : AVLTree α}
    (hcl : HeightConsistent l) (hcr : HeightConsistent r)
    (hbl : Balanced l) (hbr : Balanced r)
    (hlr : l.cachedHeight ≤ r.cachedHeight + 2)
    (hrl : r.cachedHeight ≤ l.cachedHeight + 2) :
    Balanced (balance a l r) ∧
      max l.cachedHeight r.cachedHeight ≤ (balance a l r).cachedHeight ∧
      (balance a l r).cachedHeight ≤ 1 + max l.cachedHeight r.cachedHeight ∧
      (l.cachedHeight ≤ r.cachedHeight + 1 → r.cachedHeight ≤ l.cachedHeight + 1 →
        (balance a l r).cachedHeight = 1 + max l.cachedHeight r.cachedHeight) := by
  unfold balance
  split
  · next hleft =>
    cases l with
    | nil =>
      simp only [cachedHeight_nil] at hleft
      omega
    | node la lh ll lr =>
      dsimp only
      obtain ⟨hlh, hcll, hclr⟩ := hcl
      obtain ⟨hll_lr, hlr_ll, hbll, hblr⟩ := hbl
      simp only [cachedHeight_node] at hleft hlr hrl
      split
      · next hsingle =>
        dsimp only [rotateRight, mkNode, Balanced, cachedHeight_node]
        refine ⟨⟨by omega, by omega, hbll, ⟨by omega, by omega, hblr, hbr⟩⟩,
          by omega, by omega, fun h₁ _ => by omega⟩
      · next hdouble =>
        cases lr with
        | nil =>
          simp only [cachedHeight_nil] at hdouble
          omega
        | node lra lrh lrl lrr =>
          obtain ⟨hlrh, _, _⟩ := hclr
          obtain ⟨hlrl_lrr, hlrr_lrl, hblrl, hblrr⟩ := hblr
          simp only [cachedHeight_node] at hlh hll_lr hlr_ll hdouble
          dsimp only [rotateLeft, rotateRight, mkNode, Balanced, cachedHeight_node]
          refine ⟨⟨by omega, by omega,
            ⟨by omega, by omega, hbll, hblrl⟩,
            ⟨by omega, by omega, hblrr, hbr⟩⟩,
            by omega, by omega, fun h₁ _ => by omega⟩
  · next hnotleft =>
    split
    · next hright =>
      cases r with
      | nil =>
        simp only [cachedHeight_nil] at hright
        omega
      | node ra rh rl rr =>
        dsimp only
        obtain ⟨hrh, hcrl, hcrr⟩ := hcr
        obtain ⟨hrl_rr, hrr_rl, hbrl, hbrr⟩ := hbr
        simp only [cachedHeight_node] at hnotleft hright hlr hrl
        split
        · next hsingle =>
          dsimp only [rotateLeft, mkNode, Balanced, cachedHeight_node]
          refine ⟨⟨by omega, by omega, ⟨by omega, by omega, hbl, hbrl⟩, hbrr⟩,
            by omega, by omega, fun _ h₂ => by omega⟩
        · next hdouble =>
          cases rl with
          | nil =>
            simp only [cachedHeight_nil] at hdouble
            omega
          | node rla rlh rll rlr =>
            obtain ⟨hrlh, _, _⟩ := hcrl
            obtain ⟨hrll_rlr, hrlr_rll, hbrll, hbrlr⟩ := hbrl
            simp only [cachedHeight_node] at hrh hrl_rr hrr_rl hdouble
            dsimp only [rotateRight, rotateLeft, mkNode, Balanced, cachedHeight_node]
            refine ⟨⟨by omega, by omega,
              ⟨by omega, by omega, hbl, hbrll⟩,
              ⟨by omega, by omega, hbrlr, hbrr⟩⟩,
              by omega, by omega, fun _ h₂ => by omega⟩
    · next hnotright =>
      dsimp only [mkNode, Balanced, cachedHeight_node]
      exact ⟨⟨by omega, by omega, hbl, hbr⟩, by omega, by omega, fun _ _ => rfl⟩

end Structure

section Ordered

variable {α : Type*} [LinearOrder α]

/-- The finite set of keys stored in `t`. -/
@[expose] def elements (t : AVLTree α) : Finset α :=
  SearchTree.elements t.toBinaryTree

/-- Strict binary-search-tree ordering on `t`. -/
@[expose] def Ordered (t : AVLTree α) : Prop :=
  SearchTree.Ordered t.toBinaryTree

/-- Complete AVL validity invariant: strict key ordering, accurate cached heights, and `±1`
sibling-height balance. -/
@[expose] def Valid (t : AVLTree α) : Prop :=
  Ordered t ∧ HeightConsistent t ∧ Balanced t

/-- Extract strict BST ordering from `Valid`. -/
theorem Valid.ordered {t : AVLTree α} (ht : Valid t) : Ordered t := ht.1

/-- Extract cached-height accuracy from `Valid`. -/
theorem Valid.heightConsistent {t : AVLTree α} (ht : Valid t) : HeightConsistent t := ht.2.1

/-- Extract `±1` sibling-height balance from `Valid`. -/
theorem Valid.balanced {t : AVLTree α} (ht : Valid t) : Balanced t := ht.2.2

/-- The empty tree is a valid AVL tree. -/
theorem valid_nil : Valid (.nil : AVLTree α) :=
  ⟨trivial, trivial, trivial⟩

/-- The empty tree stores no keys. -/
@[simp]
theorem elements_nil : elements (.nil : AVLTree α) = ∅ := rfl

/-- An internal node's key set is its root key together with both subtrees' key sets. -/
@[simp]
theorem elements_node (a : α) (h : ℕ) (l r : AVLTree α) :
    elements (.node a h l r) = Insert.insert a (elements l ∪ elements r) := rfl

/-- Membership in an internal node's key set splits across the root key and its two subtrees. -/
theorem mem_elements_node {x a : α} {h : ℕ} {l r : AVLTree α} :
    x ∈ elements (.node a h l r) ↔ x = a ∨ x ∈ elements l ∨ x ∈ elements r := by
  simp [elements]

/-- A strict AVL tree stores each represented key in exactly one node. -/
theorem card_elements {t : AVLTree α} (ht : Ordered t) :
    (elements t).card = t.numNodes :=
  SearchTree.card_elements ht

/-- Logarithmic height bound ([Cormen et al., Problem 13-3(a)][CLRS2009]): every valid AVL tree `t`
has height at most `2 * Nat.log 2 ((elements t).card + 1)` (in particular `0` when empty). -/
theorem Valid.cachedHeight_le_two_mul_log {t : AVLTree α} (ht : Valid t) :
    t.cachedHeight ≤ 2 * Nat.log 2 ((elements t).card + 1) := by
  have hcard : (elements t).card = t.numNodes := card_elements ht.ordered
  have hpow : 2 ^ ((t.cachedHeight + 1) / 2) ≤ (elements t).card + 1 :=
    (two_pow_half_succ_le_fib t.cachedHeight).trans
      (hcard ▸ fib_height_le_numNodes_add_one ht.heightConsistent ht.balanced)
  have hlog : (t.cachedHeight + 1) / 2 ≤ Nat.log 2 ((elements t).card + 1) :=
    Nat.le_log_of_pow_le (by decide) hpow
  omega

/-- Executable membership search on `AVLTree α` without allocating `toBinaryTree`. -/
@[expose] def contains (x : α) : AVLTree α → Bool
  | .nil => false
  | .node a _ l r => if x < a then contains x l else if a < x then contains x r else true

/-- Executable minimum query on `AVLTree α` without allocating `toBinaryTree`. -/
@[expose] def minimum : AVLTree α → Option α
  | .nil => none
  | .node a _ l _ => (minimum l).or (some a)

/-- Executable strict-successor query on `AVLTree α` without allocating `toBinaryTree`. -/
@[expose] def successor (x : α) : AVLTree α → Option α
  | .nil => none
  | .node a _ l r => if x < a then (successor x l).or (some a) else successor x r

/-- `AVLTree.contains` agrees with `SearchTree.contains` on `toBinaryTree`. -/
theorem contains_eq_searchTree (x : α) (t : AVLTree α) :
    contains x t = SearchTree.contains x t.toBinaryTree := by
  induction t with
  | nil => rfl
  | node a h l r ihl ihr => simp only [contains, toBinaryTree, SearchTree.contains, ihl, ihr]

omit [LinearOrder α] in
/-- `AVLTree.minimum` agrees with `SearchTree.minimum` on `toBinaryTree`. -/
theorem minimum_eq_searchTree (t : AVLTree α) :
    minimum t = SearchTree.minimum t.toBinaryTree := by
  induction t with
  | nil => rfl
  | node a h l r ihl _ => simp only [minimum, toBinaryTree, SearchTree.minimum, ihl]

/-- `AVLTree.successor` agrees with `SearchTree.successor` on `toBinaryTree`. -/
theorem successor_eq_searchTree (x : α) (t : AVLTree α) :
    successor x t = SearchTree.successor x t.toBinaryTree := by
  induction t with
  | nil => rfl
  | node a h l r ihl ihr => simp only [successor, toBinaryTree, SearchTree.successor, ihl, ihr]

/-- Membership search agrees with finite-set membership on any ordered tree. -/
theorem contains_eq_true {t : AVLTree α} (ht : Ordered t) (x : α) :
    contains x t = true ↔ x ∈ elements t := by
  rw [contains_eq_searchTree]
  exact SearchTree.contains_eq_true ht x

/-- Leftmost descent returns the least stored key, or `none` when empty. -/
theorem minimum_spec {t : AVLTree α} (ht : Ordered t) :
    LeastResult (elements t) (minimum t) := by
  rw [minimum_eq_searchTree]
  exact SearchTree.minimum_spec ht

/-- `successor x t` returns the least stored key strictly greater than `x`, or `none`. -/
theorem successor_spec {t : AVLTree α} (ht : Ordered t) (x : α) :
    LeastResult ((elements t).filter (x < ·)) (successor x t) := by
  rw [successor_eq_searchTree]
  exact SearchTree.successor_spec ht x

/-- `mkNode` stores `a` together with the keys of `l` and `r`. -/
@[simp]
theorem elements_mkNode (a : α) (l r : AVLTree α) :
    elements (mkNode a l r) = Insert.insert a (elements l ∪ elements r) := rfl

/-- Single right rotation preserves the represented key set. -/
theorem elements_rotateRight (a : α) (l r : AVLTree α) :
    elements (rotateRight a l r) = Insert.insert a (elements l ∪ elements r) := by
  cases l with
  | nil => rfl
  | node la lh ll lr =>
    ext x
    simp only [rotateRight, elements_mkNode, elements_node, Finset.mem_insert, Finset.mem_union]
    tauto

/-- Single left rotation preserves the represented key set. -/
theorem elements_rotateLeft (a : α) (l r : AVLTree α) :
    elements (rotateLeft a l r) = Insert.insert a (elements l ∪ elements r) := by
  cases r with
  | nil => rfl
  | node ra rh rl rr =>
    ext x
    simp only [rotateLeft, elements_mkNode, elements_node, Finset.mem_insert, Finset.mem_union]
    tauto

/-- `balance` preserves the represented key set unconditionally. -/
@[simp]
theorem elements_balance (a : α) (l r : AVLTree α) :
    elements (balance a l r) = Insert.insert a (elements l ∪ elements r) := by
  unfold balance
  split
  · cases l with
    | nil => rfl
    | node la lh ll lr =>
      dsimp only
      split
      · exact elements_rotateRight a _ r
      · rw [elements_rotateRight, elements_rotateLeft]
        rfl
  · split
    · cases r with
      | nil => rfl
      | node ra rh rl rr =>
        dsimp only
        split
        · exact elements_rotateLeft a l _
        · rw [elements_rotateLeft, elements_rotateRight]
          rfl
    · rfl

/-- Single right rotation preserves strict BST ordering. -/
theorem ordered_rotateRight {a : α} {h : ℕ} {l r : AVLTree α}
    (ho : Ordered (.node a h l r)) : Ordered (rotateRight a l r) := by
  cases l with
  | nil => exact ho
  | node la lh ll lr =>
    obtain ⟨⟨holl, holr, hll_la, hla_lr⟩, hor, hl_a, ha_r⟩ := ho
    have hla_a : la < a := hl_a la (by simp)
    refine ⟨holl, ⟨holr, hor, ?_, ha_r⟩, hll_la, ?_⟩
    · intro x hx
      exact hl_a x (by simp [hx])
    · intro x hx
      simp only [mkNode, toBinaryTree_node, SearchTree.mem_elements_node] at hx
      rcases hx with rfl | hx | hx
      · exact hla_a
      · exact hla_lr x hx
      · exact lt_trans hla_a (ha_r x hx)

/-- Single left rotation preserves strict BST ordering. -/
theorem ordered_rotateLeft {a : α} {h : ℕ} {l r : AVLTree α}
    (ho : Ordered (.node a h l r)) : Ordered (rotateLeft a l r) := by
  cases r with
  | nil => exact ho
  | node ra rh rl rr =>
    obtain ⟨hol, ⟨horl, horr, hrl_ra, hra_rr⟩, hl_a, ha_r⟩ := ho
    have ha_ra : a < ra := ha_r ra (by simp)
    refine ⟨⟨hol, horl, hl_a, ?_⟩, horr, ?_, hra_rr⟩
    · intro x hx
      exact ha_r x (by simp [hx])
    · intro x hx
      simp only [mkNode, toBinaryTree_node, SearchTree.mem_elements_node] at hx
      rcases hx with rfl | hx | hx
      · exact ha_ra
      · exact lt_trans (hl_a x hx) ha_ra
      · exact hrl_ra x hx

/-- `balance` preserves strict key ordering. -/
theorem ordered_balance {a : α} {h : ℕ} {l r : AVLTree α}
    (ho : Ordered (.node a h l r)) : Ordered (balance a l r) := by
  unfold balance
  split
  · cases l with
    | nil => exact ho
    | node la lh ll lr =>
      dsimp only
      split
      · exact ordered_rotateRight ho
      · obtain ⟨hl, hr, hl_a, ha_r⟩ := ho
        refine ordered_rotateRight (h := 0) ⟨ordered_rotateLeft hl, hr, ?_, ha_r⟩
        intro x hx
        have hx' : x ∈ elements (rotateLeft la ll lr) := hx
        rw [elements_rotateLeft] at hx'
        exact hl_a x hx'
  · split
    · cases r with
      | nil => exact ho
      | node ra rh rl rr =>
        dsimp only
        split
        · exact ordered_rotateLeft ho
        · obtain ⟨hl, hr, hl_a, ha_r⟩ := ho
          refine ordered_rotateLeft (h := 0) ⟨hl, ordered_rotateRight hr, hl_a, ?_⟩
          intro x hx
          have hx' : x ∈ elements (rotateRight ra rl rr) := hx
          rw [elements_rotateRight] at hx'
          exact ha_r x hx'
    · exact ho

/-- Insert `x` into an AVL tree, rebalancing ancestors along the search path
([Cormen et al., Problem 13-3(c)][CLRS2009]). Duplicate insertion leaves the node unchanged. -/
@[expose] def insert (x : α) : AVLTree α → AVLTree α
  | .nil => mkNode x .nil .nil
  | .node a h l r =>
      if x < a then balance a (insert x l) r
      else if a < x then balance a l (insert x r)
      else .node a h l r

/-- Insertion adds `x` to the represented `Finset α`. -/
@[simp]
theorem elements_insert (x : α) (t : AVLTree α) :
    elements (insert x t) = Insert.insert x (elements t) := by
  induction t with
  | nil => simp [insert, mkNode]
  | node a h l r ihl ihr =>
    simp only [insert]
    split <;> rename_i hxa
    · ext y
      simp [elements_balance, ihl, or_left_comm]
    · split <;> rename_i hax
      · ext y
        simp [elements_balance, ihr, or_left_comm]
      · have heq : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        simp [heq]

private theorem valid_and_height_insert {t : AVLTree α} (ht : Valid t) (x : α) :
    Valid (insert x t) ∧
      t.cachedHeight ≤ (insert x t).cachedHeight ∧
      (insert x t).cachedHeight ≤ t.cachedHeight + 1 := by
  induction t with
  | nil =>
    refine ⟨⟨?_, ⟨rfl, trivial, trivial⟩, ⟨Nat.zero_le _, Nat.zero_le _, trivial, trivial⟩⟩,
      Nat.zero_le _, Nat.le_refl 1⟩
    simp [insert, mkNode, Ordered, SearchTree.Ordered, SearchTree.elements]
  | node a h l r ihl ihr =>
    obtain ⟨⟨hol, hor, hl_a, ha_r⟩, ⟨hh, hcl, hcr⟩, ⟨hlr, hrl, hbl, hbr⟩⟩ := ht
    simp only [insert]
    split <;> rename_i hxa
    · obtain ⟨⟨hol', hcl', hbl'⟩, hlo, hhi⟩ := ihl ⟨hol, hcl, hbl⟩
      have ho' : Ordered (.node a 0 (insert x l) r) := by
        refine ⟨hol', hor, ?_, ha_r⟩
        intro y hy
        have hy' : y ∈ elements (insert x l) := hy
        rw [elements_insert, Finset.mem_insert] at hy'
        rcases hy' with rfl | hy'
        · exact hxa
        · exact hl_a y hy'
      obtain ⟨hb_bal, hb_lo, hb_hi, hb_eq⟩ :=
        balanced_and_height_balance a hcl' hcr hbl' hbr (by omega) (by omega)
      refine ⟨⟨ordered_balance ho', heightConsistent_balance hcl' hcr, hb_bal⟩, ?_, ?_⟩
      · simp only [cachedHeight_node]
        by_cases hbal1 : (insert x l).cachedHeight ≤ r.cachedHeight + 1
        · have heq := hb_eq hbal1 (by omega)
          omega
        · omega
      · simp only [cachedHeight_node]
        omega
    · split <;> rename_i hax
      · obtain ⟨⟨hor', hcr', hbr'⟩, hlo, hhi⟩ := ihr ⟨hor, hcr, hbr⟩
        have ho' : Ordered (.node a 0 l (insert x r)) := by
          refine ⟨hol, hor', hl_a, ?_⟩
          intro y hy
          have hy' : y ∈ elements (insert x r) := hy
          rw [elements_insert, Finset.mem_insert] at hy'
          rcases hy' with rfl | hy'
          · exact hax
          · exact ha_r y hy'
        obtain ⟨hb_bal, hb_lo, hb_hi, hb_eq⟩ :=
          balanced_and_height_balance a hcl hcr' hbl hbr' (by omega) (by omega)
        refine ⟨⟨ordered_balance ho', heightConsistent_balance hcl hcr', hb_bal⟩, ?_, ?_⟩
        · simp only [cachedHeight_node]
          by_cases hbal1 : (insert x r).cachedHeight ≤ l.cachedHeight + 1
          · have heq := hb_eq (by omega) hbal1
            omega
          · omega
        · simp only [cachedHeight_node]
          omega
      · exact ⟨⟨⟨hol, hor, hl_a, ha_r⟩, ⟨hh, hcl, hcr⟩, ⟨hlr, hrl, hbl, hbr⟩⟩,
          Nat.le_refl _, Nat.le_succ _⟩

/-- `insert` preserves full AVL validity (`Ordered`, `HeightConsistent`, and `Balanced`). -/
theorem valid_insert {t : AVLTree α} (ht : Valid t) (x : α) : Valid (insert x t) :=
  (valid_and_height_insert ht x).1

/-- `insert` increases the cached height by at most `1` (and never decreases it). -/
theorem cachedHeight_insert_le {t : AVLTree α} (ht : Valid t) (x : α) :
    t.cachedHeight ≤ (insert x t).cachedHeight ∧
      (insert x t).cachedHeight ≤ t.cachedHeight + 1 :=
  (valid_and_height_insert ht x).2

/-- When `l` and `r` already differ in height by at most `1`, `balance` performs no rotation. -/
theorem balance_eq_node {a : α} {h : ℕ} {l r : AVLTree α}
    (hh : h = 1 + max l.cachedHeight r.cachedHeight)
    (hlr : l.cachedHeight ≤ r.cachedHeight + 1)
    (hrl : r.cachedHeight ≤ l.cachedHeight + 1) :
    balance a l r = .node a h l r := by
  unfold balance mkNode
  split
  · omega
  · split
    · omega
    · rw [hh]

/-- Re-inserting an already-present key into a valid AVL tree leaves the entire tree unchanged. -/
theorem insert_eq_self {t : AVLTree α} (ht : Valid t) {x : α} (hx : x ∈ elements t) :
    insert x t = t := by
  induction t with
  | nil => simp at hx
  | node a h l r ihl ihr =>
    obtain ⟨⟨hol, hor, hl_a, ha_r⟩, ⟨hh, hcl, hcr⟩, ⟨hlr, hrl, hbl, hbr⟩⟩ := ht
    simp only [insert]
    split <;> rename_i hxa
    · have hxl : x ∈ elements l := by
        rcases mem_elements_node.mp hx with rfl | hxl | hxr
        · exact absurd rfl (ne_of_lt hxa)
        · exact hxl
        · exact absurd (ha_r x hxr) (not_lt_of_gt hxa)
      rw [ihl ⟨hol, hcl, hbl⟩ hxl]
      exact balance_eq_node hh hlr hrl
    · split <;> rename_i hax
      · have hxr : x ∈ elements r := by
          rcases mem_elements_node.mp hx with rfl | hxl | hxr
          · exact absurd rfl (ne_of_gt hax)
          · exact absurd (hl_a x hxl) (not_lt_of_gt hax)
          · exact hxr
        rw [ihr ⟨hor, hcr, hbr⟩ hxr]
        exact balance_eq_node hh hlr hrl
      · rfl

/-- Internal-node visits of `contains` and `insert` along the downward search path. -/
@[expose] def searchVisits (x : α) (t : AVLTree α) : ℕ :=
  SearchTree.searchVisits x t.toBinaryTree

/-- Internal-node visits of `minimum` along the left spine. -/
@[expose] def minimumVisits (t : AVLTree α) : ℕ :=
  SearchTree.minimumVisits t.toBinaryTree

/-- Internal-node visits of `successor`. -/
@[expose] def successorVisits (x : α) (t : AVLTree α) : ℕ :=
  SearchTree.successorVisits x t.toBinaryTree

/-- Search and insertion visit at most `t.cachedHeight` downward-path internal nodes. -/
theorem searchVisits_le_cachedHeight {t : AVLTree α} (hc : HeightConsistent t) (x : α) :
    searchVisits x t ≤ t.cachedHeight := by
  rw [cachedHeight_eq_height hc]
  exact SearchTree.searchVisits_le_height x t.toBinaryTree

omit [LinearOrder α] in
/-- Leftmost minimum descent visits at most `t.cachedHeight` internal nodes. -/
theorem minimumVisits_le_cachedHeight {t : AVLTree α} (hc : HeightConsistent t) :
    minimumVisits t ≤ t.cachedHeight := by
  rw [cachedHeight_eq_height hc]
  exact SearchTree.minimumVisits_le_height t.toBinaryTree

/-- Strict-successor search visits at most `t.cachedHeight` internal nodes. -/
theorem successorVisits_le_cachedHeight {t : AVLTree α} (hc : HeightConsistent t) (x : α) :
    successorVisits x t ≤ t.cachedHeight := by
  rw [cachedHeight_eq_height hc]
  exact SearchTree.successorVisits_le_height x t.toBinaryTree

end Ordered

end AVLTree

end Cslib.Algorithms.Lean
