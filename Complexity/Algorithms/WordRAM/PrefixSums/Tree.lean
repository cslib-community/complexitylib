/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Log

/-!
# Balanced aggregation trees for dynamic prefix sums

An array of `2 ^ h` natural numbers is represented by a complete binary aggregation tree.
The logical operations are addition at one position and summation of a prefix. Nodes are
laid out in preorder in a contiguous region of `2 * 2 ^ h - 1` words. These definitions do
not assign unit cost to a Lean operation: the concrete Word-RAM client supplies the execution
and cost proofs.

## Main definitions

* `Tree`, `Tree.leaves`, `Tree.total`, `Tree.zero`: a complete binary tree with natural-number
  leaves, its leaf array, root aggregate, and all-zero tree.
* `increment`: point increment on a list of natural numbers.
* `Tree.words`, `Tree.Rep`: word count and contiguous memory representation, including every
  internal sum.
* `Tree.prefixSum`, `Tree.add`: prefix queries and point increments.

## Main results

* `Tree.prefixSum_eq_sum_take`: the query is the sum of the corresponding leaf prefix.
* `Tree.Rep.congr`: representation depends only on its owned region.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009] for balanced trees and aggregation invariants.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PrefixSums

/-- A complete binary tree with `2 ^ h` leaves. -/
inductive Tree : ℕ → Type where
  /-- A single array entry. -/
  | leaf (value : ℕ) : Tree 0
  /-- Two equally sized consecutive subarrays. -/
  | node {h : ℕ} (left right : Tree h) : Tree (h + 1)
  deriving DecidableEq, Repr

/-- Add an increment at a list position; out-of-range positions leave the list unchanged. -/
def increment : List ℕ → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | a :: as, 0, δ => (a + δ) :: as
  | a :: as, i + 1, δ => a :: increment as i δ

/-- Point increments split over concatenation at the left array's length. -/
private theorem increment_append (as bs : List ℕ) (i δ : ℕ) :
    increment (as ++ bs) i δ =
      if i < as.length then increment as i δ ++ bs
      else as ++ increment bs (i - as.length) δ := by
  induction as generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero => simp [increment]
    | succ i =>
      simp only [List.cons_append, increment, ih, List.length_cons, Nat.add_lt_add_iff_right,
        Nat.add_sub_add_right]
      split <;> rfl

namespace Tree

variable {h a b : ℕ} {mem mem' : ℕ → ℕ}

/-- The represented array, in its original order. -/
def leaves : {h : ℕ} → Tree h → List ℕ
  | _, .leaf v => [v]
  | _, .node l r => l.leaves ++ r.leaves

/-- The aggregate stored at the root. -/
def total : {h : ℕ} → Tree h → ℕ
  | _, .leaf v => v
  | _, .node l r => l.total + r.total

/-- The sum of the first `k` entries. Calls beyond the end are clamped. -/
def prefixSum : {h : ℕ} → Tree h → ℕ → ℕ
  | _, .leaf v, k => if k = 0 then 0 else v
  | _, .node (h := h) l r, k =>
    if k < 2 ^ h then l.prefixSum k else l.total + r.prefixSum (k - 2 ^ h)

/-- Add `δ` at zero-based position `i`. The machine interface requires `i < 2 ^ h`. -/
def add : {h : ℕ} → Tree h → ℕ → ℕ → Tree h
  | _, .leaf v, _, δ => .leaf (v + δ)
  | _, .node (h := h) l r, i, δ =>
    if i < 2 ^ h then .node (l.add i δ) r else .node l (r.add (i - 2 ^ h) δ)

/-- A complete binary tree of height `h` has `2 ^ h` leaves. -/
@[simp]
theorem length_leaves (t : Tree h) : t.leaves.length = 2 ^ h := by
  induction t with
  | leaf => simp [leaves]
  | node l r ihl ihr => simp [leaves, ihl, ihr, pow_succ, Nat.mul_two]

/-- The sum of the leaf array equals the root aggregate `t.total`. -/
@[simp]
theorem sum_leaves (t : Tree h) : t.leaves.sum = t.total := by
  induction t <;> simp_all [leaves, total]

/-- The prefix sum of length zero is zero. -/
@[simp]
theorem prefixSum_zero (t : Tree h) : t.prefixSum 0 = 0 := by
  induction t <;> simp_all [prefixSum]

/-- The prefix sum over all `2 ^ h` leaves equals `t.total`. -/
@[simp]
theorem prefixSum_length (t : Tree h) : t.prefixSum (2 ^ h) = t.total := by
  induction t with
  | leaf => simp [prefixSum, total]
  | @node h l r ihl ihr =>
    have hp := Nat.two_pow_pos h
    simp only [prefixSum, pow_succ, show ¬2 ^ h * 2 < 2 ^ h by omega, ↓reduceIte, total]
    rw [show 2 ^ h * 2 - 2 ^ h = 2 ^ h by omega, ihr]

/-- The tree query has the ordinary array-prefix meaning. -/
theorem prefixSum_eq_sum_take (t : Tree h) (k : ℕ) : t.prefixSum k = (t.leaves.take k).sum := by
  induction t generalizing k with
  | leaf v => cases k <;> simp [prefixSum, leaves]
  | @node h l r ihl ihr =>
    simp only [prefixSum, leaves, List.take_append, List.sum_append, length_leaves]
    split
    · next hk => simp [ihl, Nat.sub_eq_zero_of_le hk.le]
    · next hk =>
      rw [List.take_of_length_le (by simpa using Nat.le_of_not_gt hk), sum_leaves, ihr]

/-- Point increments raise the total by precisely the increment. -/
@[simp]
theorem total_add (t : Tree h) (i δ : ℕ) : (t.add i δ).total = t.total + δ := by
  induction t generalizing i with
  | leaf => rfl
  | node l r ihl ihr =>
    simp only [add]
    split <;> simp [total, ihl, ihr, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The tree update is the ordinary point increment on the represented array. -/
theorem leaves_add (t : Tree h) (i δ : ℕ) (hi : i < 2 ^ h) :
    (t.add i δ).leaves = increment t.leaves i δ := by
  induction t generalizing i with
  | leaf v =>
    have : i = 0 := by simpa using hi
    simp [add, leaves, increment, this]
  | @node h l r ihl ihr =>
    have hp := Nat.two_pow_pos h
    simp only [add, leaves, increment_append, length_leaves]
    split
    · next hl => simp [leaves, ihl i hl]
    · next hl =>
      have hi' : i - 2 ^ h < 2 ^ h := by rw [pow_succ] at hi; omega
      simp [leaves, ihr (i - 2 ^ h) hi']

/-- Number of words occupied by a complete aggregation tree. -/
def words (h : ℕ) : ℕ := 2 * 2 ^ h - 1

/-- A leaf tree of height zero occupies one word. -/
@[simp]
theorem words_zero : words 0 = 1 := rfl

private theorem words_succ (h : ℕ) : words (h + 1) = 1 + words h + words h := by
  have := Nat.two_pow_pos h
  simp only [words, pow_succ]
  omega

/-- The memory stores each subtree's aggregate at its root, followed by its left and right
subtrees. No assertion is made about memory outside the occupied interval. -/
def Rep : {h : ℕ} → Tree h → ℕ → (ℕ → ℕ) → Prop
  | _, .leaf v, b, mem => mem b = v
  | h + 1, .node l r, b, mem =>
    mem b = l.total + r.total ∧ l.Rep (b + 1) mem ∧ r.Rep (b + 2 * 2 ^ h) mem

/-- The root word at base address `b` stores `t.total`. -/
theorem Rep.root {t : Tree h} (ht : t.Rep b mem) : mem b = t.total := by
  cases t with
  | leaf => exact ht
  | node => exact ht.1

/-- A frame rule for the tree representation: only its contiguous footprint matters. -/
theorem Rep.congr {t : Tree h} (ht : t.Rep b mem)
    (he : ∀ a, b ≤ a → a < b + words h → mem' a = mem a) : t.Rep b mem' := by
  induction t generalizing b with
  | leaf v =>
    change mem' b = v
    rw [he b le_rfl (by simp [words]), ht]
  | @node h l r ihl ihr =>
    have hp := Nat.two_pow_pos h
    obtain ⟨hroot, hl, hr⟩ := ht
    refine ⟨(he b le_rfl (by rw [words_succ]; omega)).trans hroot, ihl hl ?_, ihr hr ?_⟩
    · intro a ha ha'
      apply he a (by omega)
      rw [words_succ]
      omega
    · intro a ha ha'
      apply he a (by omega)
      simp only [words, pow_succ] at ha' ⊢
      omega

/-- Writing outside the representation's region preserves it. -/
theorem Rep.update_of_outside {t : Tree h} (ht : t.Rep b mem)
    (ha : a < b ∨ b + words h ≤ a) (v : ℕ) : t.Rep b (Function.update mem a v) := by
  apply ht.congr
  intro j hj hj'
  exact Function.update_of_ne (by omega) _ _

/-- The all-zero array has a concrete, nonempty representation in zero memory. -/
def zero : (h : ℕ) → Tree h
  | 0 => .leaf 0
  | h + 1 => .node (zero h) (zero h)

/-- The root aggregate of the all-zero tree is zero. -/
@[simp]
theorem total_zero (h : ℕ) : (zero h).total = 0 := by
  induction h <;> simp_all [zero, total]

/-- All-zero memory represents the all-zero tree at any base address `b`. -/
theorem rep_zero (h b : ℕ) : (zero h).Rep b (fun _ => 0) := by
  induction h generalizing b <;> simp_all [zero, Rep]

end Tree
end Cslib.Algorithms.WordRAM.PrefixSums

end
