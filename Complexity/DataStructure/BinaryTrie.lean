/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic

/-!
# Sparse binary dictionaries with exact traversal bounds

Keys are lists of bits. `BinaryTrie.find` follows one branch per key bit;
`BinaryTrie.insert` replaces only the specified key. Empty keys and keys of
different lengths are supported. The resource API counts actual node inspections
and retained nodes, including terminal-value nodes. List/key construction and
allocation time are not included. This is a dictionary operation count, not a
machine-runtime certificate.

## Main definitions

* `BinaryTrie.find`, `BinaryTrie.insert`: lookup and replacement by a bit-list key.

## Main results

* `BinaryTrie.find_insert`: insertion changes precisely one key.
* `BinaryTrie.nodes_insert_le`: retained-node growth.
* `BinaryTrie.insertVisits_eq`, `BinaryTrie.findVisits_le`: exact/bounded traversals.
-/

public section

namespace Cslib.DataStructure

/-- A sparse binary trie; an internal value permits keys of different lengths. -/
inductive BinaryTrie (α : Type*) where
  | empty
  | node (value : Option α) (left right : BinaryTrie α)
  deriving Inhabited

namespace BinaryTrie

/-- Follow the bits of the key, returning the stored record if present. -/
@[expose] def find {α : Type*} : BinaryTrie α → List Bool → Option α
  | .empty, _ => none
  | .node v _ _, [] => v
  | .node _ l r, b :: bs => find (if b then r else l) bs

/-- Insert a record. An existing record with the same key is replaced. -/
@[expose] def insert {α : Type*} (key : List Bool) (a : α) : BinaryTrie α → BinaryTrie α
  | .empty => match key with
    | [] => .node (some a) .empty .empty
    | b :: bs => if b then .node none .empty (insert bs a .empty)
      else .node none (insert bs a .empty) .empty
  | .node v l r => match key with
    | [] => .node (some a) l r
    | b :: bs => if b then .node v l (insert bs a r) else .node v (insert bs a l) r

/-- Insertion changes precisely one key. -/
theorem find_insert {α : Type*} (key query : List Bool) (a : α) (t : BinaryTrie α) :
    (insert key a t).find query = if query = key then some a else t.find query := by
  induction key generalizing query t with
  | nil => cases t <;> cases query <;> simp [insert, find]
  | cons b bs ih =>
    cases t <;> cases query with
    | nil => cases b <;> simp [insert, find]
    | cons c cs => cases b <;> cases c <;> simp [insert, find, ih]

/-- Node inspections/builds performed by insertion, following exactly its recursion. -/
@[expose] def insertVisits {α : Type*} : List Bool → BinaryTrie α → ℕ
  | [], _ => 1
  | _ :: bs, .empty => 1 + insertVisits bs (.empty : BinaryTrie α)
  | b :: bs, .node _ l r => 1 + insertVisits bs (if b then r else l)

/-- Insertion traverses or builds one node per key depth, including the terminal value. -/
theorem insertVisits_eq {α : Type*} (key : List Bool) (t : BinaryTrie α) :
    insertVisits key t = key.length + 1 := by
  induction key generalizing t with
  | nil => rfl
  | cons b bs ih => cases t <;> simp [insertVisits, ih, Nat.add_comm]

/-- Number of retained nodes, including terminal values. -/
@[expose] def nodes {α : Type*} : BinaryTrie α → ℕ
  | .empty => 0
  | .node _ l r => 1 + l.nodes + r.nodes

/-- Each insertion adds at most one node per key bit and one terminal node. -/
theorem nodes_insert_le {α : Type*} (key : List Bool) (a : α) (t : BinaryTrie α) :
    (insert key a t).nodes ≤ t.nodes + key.length + 1 := by
  induction key generalizing t with
  | nil => cases t <;> simp [insert, nodes]
  | cons b bs ih =>
    cases t with
    | empty =>
      have h := ih (.empty : BinaryTrie α)
      cases b <;> simp only [insert, nodes, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      all_goals simp only [nodes] at h; omega
    | node v l r =>
      cases b <;> simp only [insert, Bool.false_eq_true, ↓reduceIte, nodes, List.length_cons]
      · have := ih l; omega
      · have := ih r; omega

/-- Actual lookup-node inspections. Empty-child tests count as one inspection. -/
@[expose] def findVisits {α : Type*} : BinaryTrie α → List Bool → ℕ
  | .empty, _ => 1
  | .node _ _ _, [] => 1
  | .node _ l r, b :: bs => 1 + findVisits (if b then r else l) bs

/-- Lookup reads at most one node at each key depth, including termination. -/
theorem findVisits_le {α : Type*} (t : BinaryTrie α) (key : List Bool) :
    t.findVisits key ≤ key.length + 1 := by
  induction key generalizing t with
  | nil => cases t <;> simp [findVisits]
  | cons b bs ih =>
    cases t with
    | empty => simp [findVisits]
    | node v l r =>
      have h := ih (if b then r else l)
      simp only [findVisits, List.length_cons]
      omega

end BinaryTrie

end Cslib.DataStructure
