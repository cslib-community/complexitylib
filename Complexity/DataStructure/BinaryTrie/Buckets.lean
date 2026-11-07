/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.DataStructure.BinaryTrie
import Mathlib.Data.List.Nodup

/-!
# Collision-preserving binary-trie buckets

`bucketIndex` retains every input record, in input order, at its key.
`bucket_bucketIndex` identifies each bucket with the corresponding list filter,
including duplicates. Node and traversal bounds count the actual trie recursion;
key construction, allocation and native runtime are separate obligations.
-/

public section

namespace Cslib.DataStructure.BinaryTrie

/-- Read a whole collision bucket. Missing keys represent empty buckets. -/
@[expose] def bucket {α : Type*} (t : BinaryTrie (List α)) (key : List Bool) : List α :=
  (t.find key).getD []

/-- Retain all records at each key, including duplicates in the input list. -/
@[expose] def bucketIndex {α : Type*} (key : α → List Bool) : List α → BinaryTrie (List α)
  | [] => .empty
  | r :: rs =>
    let t := bucketIndex key rs
    t.insert (key r) (r :: bucket t (key r))

/-- Bucket order and multiplicity agree exactly with filtering the input list. -/
theorem bucket_bucketIndex {α : Type*} (key : α → List Bool) (rs : List α) (query : List Bool) :
    bucket (bucketIndex key rs) query = rs.filter (fun r => key r == query) := by
  induction rs with
  | nil => simp [bucket, bucketIndex, BinaryTrie.find]
  | cons r rs ih =>
    simp only [bucketIndex, bucket, BinaryTrie.find_insert]
    by_cases h : query = key r
    · subst query
      simp only [↓reduceIte, Option.getD_some]
      change r :: bucket (bucketIndex key rs) (key r) = _
      rw [ih]
      simp
    · simp only [h, ↓reduceIte]
      change bucket (bucketIndex key rs) query = _
      rw [ih]
      simp [Ne.symm h]

/-- A bucket bucketIndex stores each record only once if its input has no duplicates. -/
theorem bucket_bucketIndex_nodup {α : Type*} (key : α → List Bool) (rs : List α)
    (h : rs.Nodup) (q : List Bool) : (bucket (bucketIndex key rs) q).Nodup := by
  rw [bucket_bucketIndex]
  exact h.filter _

/-- Each first-quarter record increases the retained dictionary by at most one
node per key bit plus a terminal node. Collision buckets share their tails. -/
theorem bucketIndex_nodes_le {α : Type*} (key : α → List Bool) (rs : List α)
    (p : ℕ) (hkey : ∀ r ∈ rs, (key r).length = p) :
    (bucketIndex key rs).nodes ≤ rs.length * (p + 1) := by
  induction rs with
  | nil => simp [bucketIndex, BinaryTrie.nodes]
  | cons r rs ih =>
    have hr := hkey r List.mem_cons_self
    have hi := ih (fun a ha => hkey a (List.mem_cons_of_mem r ha))
    have hn := BinaryTrie.nodes_insert_le (key r)
      (r :: bucket (bucketIndex key rs) (key r)) (bucketIndex key rs)
    simp only [bucketIndex, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Actual lookup and insertion inspections while building the bucket bucketIndex. -/
@[expose] def bucketIndexVisits {α : Type*} (key : α → List Bool) : List α → ℕ
  | [] => 1
  | r :: rs => bucketIndexVisits key rs + (bucketIndex key rs).findVisits (key r) +
    BinaryTrie.insertVisits (key r) (bucketIndex key rs) + 1

/-- Preprocessing inspects at most two trie paths per quarter record. -/
theorem bucketIndexVisits_le {α : Type*} (key : α → List Bool) (rs : List α)
    (p : ℕ) (hkey : ∀ r ∈ rs, (key r).length = p) :
    bucketIndexVisits key rs ≤ rs.length * (2 * p + 3) + 1 := by
  induction rs with
  | nil => simp [bucketIndexVisits]
  | cons r rs ih =>
    have hr := hkey r List.mem_cons_self
    have hi := ih (fun a ha => hkey a (List.mem_cons_of_mem r ha))
    have hf := BinaryTrie.findVisits_le (bucketIndex key rs) (key r)
    rw [hr] at hf
    simp only [bucketIndexVisits, BinaryTrie.insertVisits_eq, hr, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

end Cslib.DataStructure.BinaryTrie
