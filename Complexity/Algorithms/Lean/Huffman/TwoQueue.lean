/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Huffman.Optimality
public import Cslib.Algorithms.Lean.TimeM
public import Cslib.Algorithms.Lean.Sort.Merge
public import Mathlib.Data.Nat.Log

import Complexity.Algorithms.Lean.MergeSort.Comparator

/-!
# Linear-Time Two-Queue Huffman Construction

When input symbols are already sorted in nondecreasing order of nonnegative weight, van Leeuwen
([VanLeeuwen1976]) observed that Huffman's algorithm does not need a general priority queue:
maintaining a list `q₁` of unmerged leaves alongside a single FIFO queue `q₂` of merged internal
nodes keeps `q₂` automatically sorted, because consecutive merged pair sums `w(t₁) + w(t₂)` are
monotone nondecreasing under nonnegative weights.

This module implements:

1. **Two-list functional FIFO queue (`FifoQueue γ`)** ([CLRS2009], Exercise 10.1-6): `O(1)`
   worst-case `peek?`, `O(1)` amortized `enqueue` / `dequeue?` under the canonical invariant
   `front = [] → back = []`, plus explicit potential-method reversal cost bounds
   (`enqueue_revCost_bound`, `dequeue?_revCost_bound`). Unlike `Std.Queue` (`Init.Data.Queue`,
   which does not maintain `dList = [] → eList = []`, so inspecting the head without committing a
   dequeue would repeatedly reverse `eList`) and `Cslib.Algorithms.Lean.Queue` (an abstract
   `Cslib.Stateful` two-stack module without `peek?`), `FifoQueue` supports `O(1)` worst-case
   `peek?` needed when `popMinM` compares the heads of `q₁` and `q₂` and pops `q₁` while leaving
   `q₂` unchanged.
2. **Cached-weight trees (`WeightedTree α β`)**: each queue entry caches `wt = tree.weight w`, so
   each merge computes `a.wt + b.wt` in `O(1)` arithmetic operations without re-traversing subtrees.
3. **Timed and pure van Leeuwen construction (`huffmanFromSortedM`, `huffmanFromSorted`)**:
   - **Cost model** (matching `Cslib.Algorithms.Lean.TimeM.mergeSort`): each weight comparison `≤`
     between the heads of `q₁` and `q₂` costs `1` tick (`✓`); pattern matching, list/queue pointer
     updates, and cached weight addition `a.wt + b.wt` cost `0` ticks.
   - **Tight comparison bound**: `(huffmanFromSortedM w syms).time ≤ 2 * syms.length - 5` for all
     `syms : List α` (`0` comparisons for `n ≤ 2`, at most `2n - 5` for `n ≥ 3`, and at most
     `2 * (n - 1)` uniformly).
4. **End-to-end unsorted Huffman construction (`huffmanM`, `huffman`)**: sorts `syms` with
   `List.mergeSortM` (`≤ n * ⌈log₂ n⌉` weight comparisons) and runs `huffmanFromSortedM`, achieving
   `≤ n * Nat.clog 2 n + (2 * n - 5)` total weight comparisons while producing a tree certified by
   `IsHuffmanBuild` (hence optimal over all `CodeTree`s, all injective `IsPrefixFree` binary codes,
   and all injective `IsUniquelyDecodable` binary codes).

## Main definitions

* `Cslib.Algorithms.Lean.Huffman.FifoQueue`: two-list functional FIFO queue.
* `Cslib.Algorithms.Lean.Huffman.WeightedTree`: `CodeTree α` paired with its cached weight `β`.
* `Cslib.Algorithms.Lean.Huffman.huffmanFromSortedM`, `huffmanFromSorted`: timed and pure `O(n)`
  two-queue Huffman construction from sorted symbols.
* `Cslib.Algorithms.Lean.Huffman.huffmanM`, `huffman`: timed and pure `O(n log n)` Huffman
  construction from arbitrary symbols via `List.mergeSortM`.

## Main results

* `Cslib.Algorithms.Lean.Huffman.huffmanFromSorted_spec`: correctness (`IsHuffmanBuild` and leaf
  permutation) on any nonempty sorted symbol list with nonnegative weights.
* `Cslib.Algorithms.Lean.Huffman.huffmanFromSortedM_time_le`: tight comparison bound
  `(huffmanFromSortedM w syms).time ≤ 2 * syms.length - 5`.
* `Cslib.Algorithms.Lean.Huffman.huffman_spec`, `huffman_optimal`,
  `huffman_optimal_isPrefixFree`, `huffman_optimal_isUniquelyDecodable`: end-to-end correctness and
  optimality of `huffman`.
* `Cslib.Algorithms.Lean.Huffman.huffmanM_time_le`: end-to-end comparison bound
  `(huffmanM w syms).time ≤ syms.length * Nat.clog 2 syms.length + (2 * syms.length - 5)`.

## References

* [VanLeeuwen1976] Jan van Leeuwen, *On the Construction of Huffman Trees*, ICALP 1976, pp. 382–410.
* [Huffman1952] David A. Huffman, *A Method for the Construction of Minimum-Redundancy Codes*, 1952.
* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms* (3rd ed.), Exercise 10.1-6 and Section 16.3, 2009.
-/

public section

namespace Cslib.Algorithms.Lean.Huffman

open scoped Cslib.Algorithms.Lean.TimeM
open Cslib.Algorithms.Lean (TimeM)

/-! ## Two-list functional FIFO queue -/

/-- Two-list functional FIFO queue representing `front ++ back.reverse`. -/
structure FifoQueue (γ : Type*) where
  /-- Dequeue-ready prefix in FIFO order. -/
  front : List γ
  /-- Recently enqueued suffix in reverse FIFO order. -/
  back : List γ
  deriving DecidableEq, Repr

universe u

namespace FifoQueue

variable {γ : Type*}

/-- Empty FIFO queue. -/
@[expose] def empty : FifoQueue γ := ⟨[], []⟩

/-- Abstract FIFO sequence represented by `q`. -/
@[expose] def toList (q : FifoQueue γ) : List γ := q.front ++ q.back.reverse

/-- Number of elements stored in `q`. -/
@[expose] def size (q : FifoQueue γ) : ℕ := q.front.length + q.back.length

/-- Canonical two-list invariant: `front` is empty only when `back` is also empty. -/
def WF (q : FifoQueue γ) : Prop := q.front = [] → q.back = []

/-- Smart constructor restoring `WF` by reversing `back` when `front` becomes empty. -/
def checkf : List γ → List γ → FifoQueue γ
  | [], b => ⟨b.reverse, []⟩
  | f, b => ⟨f, b⟩

/-- Number of list-reversal steps performed by `checkf f b`. -/
def checkfRevCost : List γ → List γ → ℕ
  | [], b => b.length
  | _ :: _, _ => 0

/-- Enqueue `x` at the back of `q`. -/
def enqueue (q : FifoQueue γ) (x : γ) : FifoQueue γ :=
  checkf q.front (x :: q.back)

/-- Peek at the front element of `q` in `O(1)` time. -/
def peek? (q : FifoQueue γ) : Option γ :=
  q.front.head?

/-- Dequeue the front element of `q` if non-empty. -/
def dequeue? (q : FifoQueue γ) : Option (γ × FifoQueue γ) :=
  match q.front with
  | [] => none
  | x :: f => some (x, checkf f q.back)

@[simp] theorem toList_empty : (empty : FifoQueue γ).toList = [] := rfl

@[simp] theorem size_empty : (empty : FifoQueue γ).size = 0 := rfl

theorem wf_empty : (empty : FifoQueue γ).WF := fun _ => rfl

@[simp] theorem toList_checkf (f b : List γ) : (checkf f b).toList = f ++ b.reverse := by
  cases f <;> simp [checkf, toList]

@[simp] theorem size_checkf (f b : List γ) : (checkf f b).size = f.length + b.length := by
  cases f <;> simp [checkf, size]

theorem wf_checkf (f b : List γ) : (checkf f b).WF := by
  cases f with
  | nil => intro _; rfl
  | cons _ _ => intro h; cases h

@[simp] theorem length_toList (q : FifoQueue γ) : q.toList.length = q.size := by
  simp [toList, size]

@[simp] theorem toList_enqueue (q : FifoQueue γ) (x : γ) :
    (q.enqueue x).toList = q.toList ++ [x] := by
  rw [enqueue, toList_checkf, toList]
  simp [List.append_assoc]

@[simp] theorem size_enqueue (q : FifoQueue γ) (x : γ) :
    (q.enqueue x).size = q.size + 1 := by
  rw [enqueue, size_checkf, size]
  simp only [List.length_cons]
  omega

theorem wf_enqueue (q : FifoQueue γ) (x : γ) : (q.enqueue x).WF :=
  wf_checkf q.front (x :: q.back)

theorem toList_eq_nil_of_front_eq_nil {q : FifoQueue γ} (hwf : q.WF) (hf : q.front = []) :
    q.toList = [] := by
  simp [toList, hf, hwf hf]

theorem front_cons_spec {q : FifoQueue γ} {x : γ} {f : List γ} (hf : q.front = x :: f) :
    q.toList = x :: (checkf f q.back).toList ∧ (checkf f q.back).WF := by
  refine ⟨?_, wf_checkf f q.back⟩
  rw [toList, hf, toList_checkf, List.cons_append]

theorem peek?_eq_head? {q : FifoQueue γ} (hwf : q.WF) : q.peek? = q.toList.head? := by
  cases hf : q.front with
  | nil => simp [peek?, hf, toList_eq_nil_of_front_eq_nil hwf hf]
  | cons x f => simp [peek?, toList, hf]

theorem dequeue?_spec {q : FifoQueue γ} (hwf : q.WF) :
    match q.dequeue? with
    | none => q.toList = []
    | some (x, q') => q.toList = x :: q'.toList ∧ q'.WF := by
  unfold dequeue?
  cases hf : q.front with
  | nil => exact toList_eq_nil_of_front_eq_nil hwf hf
  | cons x f => exact front_cons_spec hf

/-- Amortized `O(1)` potential bound for `enqueue` with potential `Φ(q) = q.back.length`:
actual reversal work plus `ΔΦ` is at most `1`. -/
theorem enqueue_revCost_bound (q : FifoQueue γ) (x : γ) :
    checkfRevCost q.front (x :: q.back) + (q.enqueue x).back.length ≤ q.back.length + 1 := by
  rw [enqueue]
  cases q.front <;> simp [checkf, checkfRevCost]

/-- Amortized `O(1)` potential bound for `dequeue?` with potential `Φ(q) = q.back.length`:
actual reversal work plus `ΔΦ` is `0`. -/
theorem dequeue?_revCost_bound (f b : List γ) :
    checkfRevCost f b + (checkf f b).back.length ≤ b.length := by
  cases f <;> simp [checkf, checkfRevCost]

end FifoQueue

/-! ## Cached-weight trees and van Leeuwen's two-queue loop -/

/-- A `CodeTree α` paired with its cached total weight `wt : β`. -/
structure WeightedTree (α β : Type*) where
  /-- Underlying code tree. -/
  tree : CodeTree α
  /-- Cached subtree weight (`tree.weight w`). -/
  wt : β
  deriving DecidableEq, Repr

/-- Pop a minimum-weight entry from leaf list `q₁` and internal-node queue `q₂`, charging `1` tick
if and only if both `q₁` and `q₂` are non-empty (preferring `q₁` on ties, as in
[VanLeeuwen1976]). Matching directly on `q₂.front` ensures `FifoQueue.checkf` is evaluated under
strict evaluation only in branches that actually dequeue from `q₂`. -/
def popMinM {α β : Type u} [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) :
    TimeM ℕ (Option (WeightedTree α β × List (WeightedTree α β) × FifoQueue (WeightedTree α β))) :=
  match q₁, q₂.front with
  | [], [] => pure none
  | [], y :: f => pure (some (y, [], FifoQueue.checkf f q₂.back))
  | x :: q₁', [] => pure (some (x, q₁', q₂))
  | x :: q₁', y :: f => do
    ✓ if x.wt ≤ y.wt then
      return some (x, q₁', q₂)
    else
      return some (y, x :: q₁', FifoQueue.checkf f q₂.back)

private theorem popMinM_size_eq {α β : Type u} [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    {q₁ q₁' : List (WeightedTree α β)} {q₂ q₂' : FifoQueue (WeightedTree α β)}
    {u : WeightedTree α β}
    (h : ⟪popMinM q₁ q₂⟫ = some (u, q₁', q₂')) :
    q₁'.length + q₂'.size + 1 = q₁.length + q₂.size := by
  unfold popMinM at h
  cases h1 : q₁ <;> cases h2 : q₂.front
  · rw [h1, h2] at h
    simp at h
  · rename_i y f
    rw [h1, h2] at h
    simp only [TimeM.ret_pure, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl, rfl⟩
    rw [FifoQueue.size_checkf, FifoQueue.size, h2]
    simp only [List.length_nil, List.length_cons]
    omega
  · rename_i x xs
    rw [h1, h2] at h
    simp only [TimeM.ret_pure, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl, rfl⟩
    simp only [List.length_cons]
    omega
  · rename_i x xs y f
    rw [h1, h2] at h
    by_cases hle : x.wt ≤ y.wt
    · simp only [hle, ↓reduceIte, TimeM.ret_bind, TimeM.ret_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl, rfl⟩
      simp only [List.length_cons]
      omega
    · simp only [hle, ↓reduceIte, TimeM.ret_bind, TimeM.ret_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl, rfl⟩
      rw [FifoQueue.size_checkf, FifoQueue.size, h2]
      simp only [List.length_cons]
      omega

/-- Fuel-driven merge loop of van Leeuwen's two-queue Huffman algorithm ([VanLeeuwen1976]). -/
private def twoQueueStepsM {α β : Type u} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)] :
    ℕ → List (WeightedTree α β) → FifoQueue (WeightedTree α β) → TimeM ℕ (Option (CodeTree α))
  | 0, _, _ => pure none
  | fuel + 1, q₁, q₂ => do
    match ← popMinM q₁ q₂ with
    | none => return none
    | some (a, q₁', q₂') =>
      match ← popMinM q₁' q₂' with
      | none => return some a.tree
      | some (b, q₁'', q₂'') =>
        twoQueueStepsM fuel q₁'' (q₂''.enqueue ⟨.branch a.tree b.tree, a.wt + b.wt⟩)

/-- Main merge loop of van Leeuwen's two-queue Huffman algorithm ([VanLeeuwen1976]). -/
def twoQueueLoopM {α β : Type u} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) :
    TimeM ℕ (Option (CodeTree α)) :=
  twoQueueStepsM (q₁.length + q₂.size) q₁ q₂

/-- Timed `O(n)` two-queue Huffman construction from a symbol list `syms` sorted by `w`
([VanLeeuwen1976]). -/
def huffmanFromSortedM {α β : Type u} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)] (w : α → β) (syms : List α) :
    TimeM ℕ (Option (CodeTree α)) :=
  twoQueueLoopM (syms.map fun a => ⟨.leaf a, w a⟩) FifoQueue.empty

/-- Pure `O(n)` two-queue Huffman construction from a symbol list `syms` sorted by `w`
([VanLeeuwen1976]). -/
def huffmanFromSorted {α β : Type u} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)] (w : α → β) (syms : List α) : Option (CodeTree α) :=
  ⟪huffmanFromSortedM w syms⟫

/-- Timed `O(n log n)` Huffman construction from an arbitrary symbol list `syms`, sorting first via
`List.mergeSortM` and then running `huffmanFromSortedM`. -/
def huffmanM {α β : Type} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (w : α → β) (syms : List α) : TimeM ℕ (Option (CodeTree α)) := do
  let sorted ← List.mergeSortM syms fun a b => do ✓ return decide (w a ≤ w b)
  huffmanFromSortedM w sorted

/-- Pure `O(n log n)` Huffman construction from an arbitrary symbol list `syms`. -/
def huffman {α β : Type} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (w : α → β) (syms : List α) : Option (CodeTree α) :=
  ⟪huffmanM w syms⟫

@[simp] theorem ret_huffmanFromSortedM {α β : Type u} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)] (w : α → β) (syms : List α) :
    ⟪huffmanFromSortedM w syms⟫ = huffmanFromSorted w syms := by rfl

@[simp] theorem ret_huffmanM {α β : Type} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)] (w : α → β) (syms : List α) :
    ⟪huffmanM w syms⟫ = huffman w syms := by rfl

/-! ## Comparison-count complexity bounds -/

private theorem popMinM_time_le_one {α β : Type u} [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) :
    (popMinM q₁ q₂).time ≤ 1 := by
  unfold popMinM
  cases q₁ <;> cases q₂.front
  · simp
  · simp
  · simp
  · rename_i x xs y f
    by_cases h : x.wt ≤ y.wt <;> simp [h]

private theorem popMinM_time_eq_zero_of_front_nil {α β : Type u} [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) {q₂ : FifoQueue (WeightedTree α β)} (hf : q₂.front = []) :
    (popMinM q₁ q₂).time = 0 := by
  unfold popMinM
  cases q₁ <;> simp [hf]

private theorem popMinM_time_eq_zero_of_size_le_one {α β : Type u} [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β))
    (hsz : q₁.length + q₂.size ≤ 1) :
    (popMinM q₁ q₂).time = 0 := by
  unfold popMinM
  cases h1 : q₁ <;> cases h2 : q₂.front
  · simp
  · simp
  · simp
  · rw [h1, FifoQueue.size, h2] at hsz
    simp only [List.length_cons] at hsz
    omega

private theorem twoQueueStepsM_time_le {α β : Type u} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)]
    (fuel : ℕ) (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) :
    (twoQueueStepsM fuel q₁ q₂).time ≤ 2 * (q₁.length + q₂.size) - 3 := by
  induction fuel generalizing q₁ q₂ with
  | zero => simp [twoQueueStepsM]
  | succ fuel ih =>
    simp only [twoQueueStepsM, TimeM.time_bind]
    by_cases h1 : q₁.length + q₂.size ≤ 1
    · have ht₁ := popMinM_time_eq_zero_of_size_le_one q₁ q₂ h1
      rw [ht₁, zero_add]
      split
      · simp
      · next a q₁' q₂' hr₁ =>
        have hsz₁ := popMinM_size_eq hr₁
        have hq₁' : q₁' = [] := List.length_eq_zero_iff.mp (by omega)
        have hf₂' : q₂'.front = [] := by
          rw [FifoQueue.size] at hsz₁
          exact List.length_eq_zero_iff.mp (by omega)
        simp [popMinM, hq₁', hf₂']
    · have ht₁ := popMinM_time_le_one q₁ q₂
      split
      · simp only [TimeM.time_pure]
        omega
      · next a q₁' q₂' hr₁ =>
        have hsz₁ := popMinM_size_eq hr₁
        simp only [TimeM.time_bind]
        split
        · simp only [TimeM.time_pure]
          by_cases hN2 : q₁.length + q₂.size = 2
          · have ht₂0 := popMinM_time_eq_zero_of_size_le_one q₁' q₂' (by omega)
            omega
          · have ht₂ := popMinM_time_le_one q₁' q₂'
            omega
        · next b q₁'' q₂'' hr₂ =>
          have hsz₂ := popMinM_size_eq hr₂
          have hih := ih q₁'' (q₂''.enqueue ⟨.branch a.tree b.tree, a.wt + b.wt⟩)
          rw [FifoQueue.size_enqueue] at hih
          by_cases hN2 : q₁.length + q₂.size = 2
          · have ht₂0 := popMinM_time_eq_zero_of_size_le_one q₁' q₂' (by omega)
            omega
          · have ht₂ := popMinM_time_le_one q₁' q₂'
            omega

/-- Comparison bound for `twoQueueLoopM` from an arbitrary two-queue state: `0` comparisons when
total size `N ≤ 1`, and at most `2 * N - 3` comparisons when `N ≥ 2` (`2 * N - 3` in `ℕ` covers
both). -/
theorem twoQueueLoopM_time_le {α β : Type u} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) :
    (twoQueueLoopM q₁ q₂).time ≤ 2 * (q₁.length + q₂.size) - 3 :=
  twoQueueStepsM_time_le (q₁.length + q₂.size) q₁ q₂

/-- **Tight Comparison Bound for Two-Queue Huffman (`O(n)`)**: starting from a sorted symbol list
`syms` (`q₂ = empty`), the first two `popMinM` calls perform `0` comparisons, so the total number of
weight comparisons is at most `2 * syms.length - 5` (`0` for `n ≤ 2`, `2n - 5` for `n ≥ 3`). -/
theorem huffmanFromSortedM_time_le {α β : Type u} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)] (w : α → β) (syms : List α) :
    (huffmanFromSortedM w syms).time ≤ 2 * syms.length - 5 := by
  unfold huffmanFromSortedM twoQueueLoopM
  set q₁ := syms.map fun a => (⟨.leaf a, w a⟩ : WeightedTree α β)
  have hq₁_len : q₁.length = syms.length := List.length_map _
  cases hfuel : q₁.length + (FifoQueue.empty : FifoQueue (WeightedTree α β)).size with
  | zero => simp [twoQueueStepsM]
  | succ fuel =>
    simp only [twoQueueStepsM, TimeM.time_bind]
    have ht₁ : (popMinM q₁ FifoQueue.empty).time = 0 :=
      popMinM_time_eq_zero_of_front_nil q₁ rfl
    rw [ht₁, zero_add]
    split
    · simp
    · next a q₁' q₂' hr₁ =>
      have hq₂'_empty : q₂' = FifoQueue.empty := by
        unfold popMinM at hr₁
        cases hq1 : q₁
        · rw [hq1] at hr₁; simp [FifoQueue.empty] at hr₁
        · rw [hq1] at hr₁
          simp only [FifoQueue.empty, TimeM.ret_pure, Option.some.injEq, Prod.mk.injEq] at hr₁
          exact hr₁.2.2.symm
      have hsz₁ := popMinM_size_eq hr₁
      have ht₂ : (popMinM q₁' q₂').time = 0 := by
        rw [hq₂'_empty]
        exact popMinM_time_eq_zero_of_front_nil q₁' rfl
      simp only [TimeM.time_bind, ht₂, zero_add]
      split
      · simp
      · next b q₁'' q₂'' hr₂ =>
        have hsz₂ := popMinM_size_eq hr₂
        have hloop := twoQueueStepsM_time_le fuel q₁''
          (q₂''.enqueue ⟨.branch a.tree b.tree, a.wt + b.wt⟩)
        rw [FifoQueue.size_enqueue] at hloop
        simp only [FifoQueue.size_empty] at hsz₁ hfuel
        omega

theorem huffmanFromSortedM_time_le_two_mul_pred {α β : Type u} [Add β] [LE β]
    [DecidableRel (· ≤ · : β → β → Prop)] (w : α → β) (syms : List α) :
    (huffmanFromSortedM w syms).time ≤ 2 * (syms.length - 1) := by
  have h := huffmanFromSortedM_time_le w syms
  omega

/-- **End-to-End Comparison Bound for `huffmanM` (`O(n log n)`)**: merge-sorting `syms` followed by
the linear-time two-queue phase uses at most `n * Nat.clog 2 n + (2 * n - 5)` weight comparisons. -/
theorem huffmanM_time_le {α β : Type} [Add β] [LE β] [DecidableRel (· ≤ · : β → β → Prop)]
    (w : α → β) (syms : List α) :
    (huffmanM w syms).time ≤ syms.length * Nat.clog 2 syms.length + (2 * syms.length - 5) := by
  unfold huffmanM
  simp only [TimeM.time_bind]
  have hsort := TimeM.mergeSortM_time syms
    (fun a b => (do ✓ return decide (w a ≤ w b) : TimeM ℕ Bool)) fun _ _ => le_rfl
  have hlen :
      ⟪List.mergeSortM syms fun a b =>
        (do ✓ return decide (w a ≤ w b) : TimeM ℕ Bool)⟫.length = syms.length := by
    simp [Cslib.Algorithms.Lean.TimeM.ret_mergeSortM]
  have htwo := huffmanFromSortedM_time_le w
    ⟪List.mergeSortM syms fun a b => (do ✓ return decide (w a ≤ w b) : TimeM ℕ Bool)⟫
  rw [hlen] at htwo
  omega

/-! ## Correctness of van Leeuwen's two-queue invariant and optimality of `huffman` -/

/-- `IsHuffmanBuild` depends on the starting forest `F` only up to `List.Perm`. -/
theorem IsHuffmanBuild.of_perm {α β : Type*} [Add β] [LE β] {w : α → β}
    {F₁ F₂ : List (CodeTree α)} {T : CodeTree α}
    (hperm : F₁.Perm F₂) (hbuild : IsHuffmanBuild w F₂ T) :
    IsHuffmanBuild w F₁ T := by
  cases hbuild with
  | single =>
    rw [List.Perm.eq_singleton hperm]
    exact .single T
  | step hmin hsub =>
    exact .step ⟨hperm.trans hmin.perm, hmin.weight_le⟩ hsub

private structure TwoQueueInv {α β : Type u} [AddCommMonoid β] [LinearOrder β]
    (w : α → β) (q₁ : List (WeightedTree α β)) (q₂ : FifoQueue (WeightedTree α β)) : Prop where
  wf : q₂.WF
  wt_eq : ∀ e ∈ q₁ ++ q₂.toList, e.wt = e.tree.weight w ∧ 0 ≤ e.wt
  sorted₁ : q₁.Pairwise (fun u v => u.wt ≤ v.wt)
  sorted₂ : q₂.toList.Pairwise (fun u v => u.wt ≤ v.wt)
  q2_le_pair_sum : ∀ u v rest, (q₁ ++ q₂.toList).Perm (u :: v :: rest) →
    ∀ z ∈ q₂.toList, z.wt ≤ u.wt + v.wt

private theorem popMinM_correct {α β : Type u} [LinearOrder β]
    {q₁ : List (WeightedTree α β)} {q₂ : FifoQueue (WeightedTree α β)}
    (hwf : q₂.WF)
    (hs₁ : q₁.Pairwise (fun u v => u.wt ≤ v.wt))
    (hs₂ : q₂.toList.Pairwise (fun u v => u.wt ≤ v.wt))
    (hne : q₁ ++ q₂.toList ≠ []) :
    ∃ u q₁' q₂',
      ⟪popMinM q₁ q₂⟫ = some (u, q₁', q₂') ∧
      q₂'.WF ∧
      q₁'.Pairwise (fun a b => a.wt ≤ b.wt) ∧
      q₂'.toList.Pairwise (fun a b => a.wt ≤ b.wt) ∧
      (∀ z ∈ q₂'.toList, z ∈ q₂.toList) ∧
      (q₁ ++ q₂.toList).Perm (u :: (q₁' ++ q₂'.toList)) ∧
      (∀ z ∈ q₁' ++ q₂'.toList, u.wt ≤ z.wt) := by
  unfold popMinM
  cases h1 : q₁ <;> cases h2 : q₂.front
  · have hnil := FifoQueue.toList_eq_nil_of_front_eq_nil hwf h2
    rw [h1, hnil] at hne
    exact absurd rfl hne
  · rename_i y f
    rcases FifoQueue.front_cons_spec h2 with ⟨hto, hwf'⟩
    rw [hto, List.pairwise_cons] at hs₂
    refine ⟨y, [], FifoQueue.checkf f q₂.back, rfl, hwf', List.Pairwise.nil, hs₂.2, ?_, ?_, ?_⟩
    · intro z hz
      rw [hto]
      exact List.mem_cons_of_mem y hz
    · rw [hto]
      exact List.Perm.refl _
    · intro z hz
      simp only [List.nil_append] at hz
      exact hs₂.1 z hz
  · rename_i x xs
    have hnil := FifoQueue.toList_eq_nil_of_front_eq_nil hwf h2
    rw [h1, List.pairwise_cons] at hs₁
    refine ⟨x, xs, q₂, rfl, hwf, hs₁.2, hs₂, fun _ hz => hz, ?_, ?_⟩
    · rw [hnil]
      exact List.Perm.refl _
    · intro z hz
      rw [hnil, List.append_nil] at hz
      exact hs₁.1 z hz
  · rename_i x xs y f
    rcases FifoQueue.front_cons_spec h2 with ⟨hto, hwf'⟩
    rw [h1, List.pairwise_cons] at hs₁
    rw [hto, List.pairwise_cons] at hs₂
    by_cases hle : x.wt ≤ y.wt
    · refine ⟨x, xs, q₂, by simp [hle], hwf, hs₁.2, by rw [hto, List.pairwise_cons]; exact hs₂,
        fun _ hz => hz, List.Perm.refl _, ?_⟩
      intro z hz
      rcases List.mem_append.mp hz with hxs | hq2
      · exact hs₁.1 z hxs
      · rw [hto] at hq2
        rcases List.mem_cons.mp hq2 with rfl | htail
        · exact hle
        · exact le_trans hle (hs₂.1 z htail)
    · have hyx : y.wt ≤ x.wt := le_of_not_ge hle
      refine ⟨y, x :: xs, FifoQueue.checkf f q₂.back, by simp [hle], hwf',
        by rw [List.pairwise_cons]; exact hs₁, hs₂.2, ?_, ?_, ?_⟩
      · intro z hz
        rw [hto]
        exact List.mem_cons_of_mem y hz
      · rw [hto]
        exact List.perm_middle
          (l₁ := x :: xs) (a := y) (l₂ := (FifoQueue.checkf f q₂.back).toList)
      · intro z hz
        rcases List.mem_append.mp hz with hxs | hq2'
        · rcases List.mem_cons.mp hxs with rfl | hxs'
          · exact hyx
          · exact le_trans hyx (hs₁.1 z hxs')
        · exact hs₂.1 z hq2'

private theorem pairwise_snoc_of_le {γ : Type*} {R : γ → γ → Prop} {L : List γ} {m : γ}
    (hL : L.Pairwise R) (hm : ∀ z ∈ L, R z m) : (L ++ [m]).Pairwise R := by
  rw [List.pairwise_append]
  refine ⟨hL, List.pairwise_singleton R m, ?_⟩
  intro z hz w hw
  simp only [List.mem_singleton] at hw
  subst hw
  exact hm z hz

private theorem twoQueueLoopM_correct {α β : Type u}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {q₁ : List (WeightedTree α β)} {q₂ : FifoQueue (WeightedTree α β)}
    (hinv : TwoQueueInv w q₁ q₂)
    (hne : q₁ ++ q₂.toList ≠ []) :
    ∃ T, ⟪twoQueueLoopM q₁ q₂⟫ = some T ∧
      IsHuffmanBuild w ((q₁ ++ q₂.toList).map WeightedTree.tree) T := by
  suffices h : ∀ (n : ℕ) (l₁ : List (WeightedTree α β)) (l₂ : FifoQueue (WeightedTree α β)),
      l₁.length + l₂.size ≤ n →
      TwoQueueInv w l₁ l₂ →
      l₁ ++ l₂.toList ≠ [] →
      ∃ T, ⟪twoQueueStepsM n l₁ l₂⟫ = some T ∧
        IsHuffmanBuild w ((l₁ ++ l₂.toList).map WeightedTree.tree) T by
    exact h (q₁.length + q₂.size) q₁ q₂ le_rfl hinv hne
  intro n
  induction n with
  | zero =>
    intro l₁ l₂ h0 _ hne'
    have hlen : (l₁ ++ l₂.toList).length = 0 := by
      rw [List.length_append, FifoQueue.length_toList]
      omega
    exact absurd (List.length_eq_zero_iff.mp hlen) hne'
  | succ n ih =>
    intro l₁ l₂ hle hinv' hne'
    rcases popMinM_correct hinv'.wf hinv'.sorted₁ hinv'.sorted₂ hne' with
      ⟨a, l₁', l₂', hr₁, hwf₁, hs₁', hs₂', hsub₁, hperm₁, hmin_a⟩
    have hsz₁ := popMinM_size_eq hr₁
    simp only [twoQueueStepsM, TimeM.ret_bind]
    split
    · next hnone => rw [hr₁] at hnone; cases hnone
    · next a₀ q₁' q₂' hr₁_eq =>
      rw [hr₁] at hr₁_eq
      injection hr₁_eq with htuple
      rcases Prod.mk.inj htuple with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
      simp only [TimeM.ret_bind]
      by_cases hne₂ : l₁' ++ l₂'.toList = []
      · have h2_nil : l₂'.front = [] := by
          have hlen' : (l₁' ++ l₂'.toList).length = 0 := by simp [hne₂]
          rw [List.length_append, FifoQueue.length_toList, FifoQueue.size] at hlen'
          exact List.length_eq_zero_iff.mp (by omega)
        have hl₁'_nil : l₁' = [] := (List.append_eq_nil_iff.mp hne₂).1
        have hr₂_none : ⟪popMinM l₁' l₂'⟫ = none := by
          simp [popMinM, hl₁'_nil, h2_nil]
        split
        · refine ⟨a.tree, rfl, ?_⟩
          rw [hne₂] at hperm₁
          have hmap := hperm₁.map WeightedTree.tree
          simp only [List.map_cons, List.map_nil] at hmap
          exact IsHuffmanBuild.of_perm hmap (.single a.tree)
        · next _ _ _ hr₂_some => rw [hr₂_none] at hr₂_some; cases hr₂_some
      · rcases popMinM_correct hwf₁ hs₁' hs₂' hne₂ with
          ⟨b, l₁'', l₂'', hr₂, hwf₂, hs₁'', hs₂'', hsub₂, hperm₂, hmin_b⟩
        have hsz₂ := popMinM_size_eq hr₂
        split
        · next hr₂_none => rw [hr₂] at hr₂_none; cases hr₂_none
        · next b₀ q₁'' q₂'' hr₂_eq =>
          rw [hr₂] at hr₂_eq
          injection hr₂_eq with htuple₂
          rcases Prod.mk.inj htuple₂ with ⟨rfl, hrest₂⟩
          rcases Prod.mk.inj hrest₂ with ⟨rfl, rfl⟩
          have hperm_ab : (l₁ ++ l₂.toList).Perm (a :: b :: (l₁'' ++ l₂''.toList)) :=
            hperm₁.trans (hperm₂.cons a)
          have ha_in : a ∈ l₁ ++ l₂.toList := hperm_ab.symm.subset List.mem_cons_self
          have hb_in' : b ∈ l₁' ++ l₂'.toList := hperm₂.symm.subset List.mem_cons_self
          have hb_in : b ∈ l₁ ++ l₂.toList :=
            hperm_ab.symm.subset (List.mem_cons_of_mem a List.mem_cons_self)
          have hab : a.wt ≤ b.wt := hmin_a b hb_in'
          rcases hinv'.wt_eq a ha_in with ⟨ha_wt, ha_nonneg⟩
          rcases hinv'.wt_eq b hb_in with ⟨hb_wt, hb_nonneg⟩
          let m : WeightedTree α β := ⟨.branch a.tree b.tree, a.wt + b.wt⟩
          let q_next := l₂''.enqueue m
          have hq_next_to : q_next.toList = l₂''.toList ++ [m] := FifoQueue.toList_enqueue l₂'' m
          have hq2_le_m : ∀ z ∈ l₂''.toList, z.wt ≤ m.wt := fun z hz =>
            hinv'.q2_le_pair_sum a b _ hperm_ab z (hsub₁ z (hsub₂ z hz))
          have hbm : b.wt ≤ m.wt := by
            dsimp only [m]
            simpa using add_le_add ha_nonneg (le_refl b.wt)
          have hb_le_all_new : ∀ x ∈ l₁'' ++ q_next.toList, b.wt ≤ x.wt := by
            intro x hx
            rw [hq_next_to, ← List.append_assoc] at hx
            rcases List.mem_append.mp hx with hpool | hm_mem
            · exact hmin_b x hpool
            · simp only [List.mem_singleton] at hm_mem
              subst hm_mem
              exact hbm
          have hinv_next : TwoQueueInv w l₁'' q_next := by
            refine ⟨FifoQueue.wf_enqueue l₂'' m, ?_, hs₁'', ?_, ?_⟩
            · intro e he
              rw [hq_next_to, ← List.append_assoc] at he
              rcases List.mem_append.mp he with hpool | hm_mem
              · exact hinv'.wt_eq e
                  (hperm_ab.symm.subset (List.mem_cons_of_mem a (List.mem_cons_of_mem b hpool)))
              · simp only [List.mem_singleton] at hm_mem
                subst hm_mem
                exact ⟨by simp [m, ha_wt, hb_wt], add_nonneg ha_nonneg hb_nonneg⟩
            · rw [hq_next_to]
              exact pairwise_snoc_of_le hs₂'' hq2_le_m
            · intro u v rest huv z hz
              have hu_in : u ∈ l₁'' ++ q_next.toList := huv.symm.subset List.mem_cons_self
              have hv_in : v ∈ l₁'' ++ q_next.toList :=
                huv.symm.subset (List.mem_cons_of_mem u List.mem_cons_self)
              have hau : a.wt ≤ u.wt := le_trans hab (hb_le_all_new u hu_in)
              have hbv : b.wt ≤ v.wt := hb_le_all_new v hv_in
              have hm_uv : m.wt ≤ u.wt + v.wt := add_le_add hau hbv
              rw [hq_next_to] at hz
              rcases List.mem_append.mp hz with hz_old | hz_m
              · exact le_trans (hq2_le_m z hz_old) hm_uv
              · simp only [List.mem_singleton] at hz_m
                subst hz_m
                exact hm_uv
          have hne_next : l₁'' ++ q_next.toList ≠ [] := by
            rw [hq_next_to]
            intro hnil
            have := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp hnil).2).2
            cases this
          have hsz_next : l₁''.length + q_next.size ≤ n := by
            simp only [q_next, FifoQueue.size_enqueue]
            omega
          rcases ih l₁'' q_next hsz_next hinv_next hne_next with ⟨T, hT_ret, hT_build⟩
          refine ⟨T, hT_ret, ?_⟩
          let F_rest := (l₁'' ++ l₂''.toList).map WeightedTree.tree
          have hmin_pair : IsMinPair w ((l₁ ++ l₂.toList).map WeightedTree.tree)
              a.tree b.tree F_rest := by
            refine ⟨hperm_ab.map WeightedTree.tree, ?_⟩
            intro t ht
            rcases List.mem_map.mp ht with ⟨e, he, rfl⟩
            have he_in : e ∈ l₁ ++ l₂.toList :=
              hperm_ab.symm.subset (List.mem_cons_of_mem a (List.mem_cons_of_mem b he))
            have he_wt := (hinv'.wt_eq e he_in).1
            rw [← ha_wt, ← hb_wt, ← he_wt]
            exact ⟨le_trans hab (hmin_b e he), hmin_b e he⟩
          have hforest_perm : (CodeTree.branch a.tree b.tree :: F_rest).Perm
              ((l₁'' ++ q_next.toList).map WeightedTree.tree) := by
            rw [hq_next_to, ← List.append_assoc, List.map_append, List.map_singleton]
            exact List.perm_append_singleton m.tree F_rest |>.symm
          exact IsHuffmanBuild.step hmin_pair (IsHuffmanBuild.of_perm hforest_perm hT_build)

/-- **Correctness of Two-Queue Huffman Construction** ([VanLeeuwen1976]): on any nonempty symbol
list `syms` sorted in nondecreasing order of `w` with nonnegative weights,
`huffmanFromSorted w syms` returns `some T` satisfying `IsHuffmanBuild w (syms.map .leaf) T` and
`T.leaves.Perm syms`. -/
theorem huffmanFromSorted_spec {α β : Type u}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {syms : List α}
    (hne : syms ≠ [])
    (hsorted : syms.Pairwise (fun a b => w a ≤ w b))
    (hw : ∀ a ∈ syms, 0 ≤ w a) :
    ∃ T, huffmanFromSorted w syms = some T ∧
      IsHuffmanBuild w (syms.map .leaf) T ∧
      T.leaves.Perm syms := by
  let q₁ := syms.map fun a => (⟨.leaf a, w a⟩ : WeightedTree α β)
  have hinv : TwoQueueInv w q₁ FifoQueue.empty := by
    refine ⟨FifoQueue.wf_empty, ?_, ?_, by simp, ?_⟩
    · intro e he
      simp only [FifoQueue.toList_empty, List.append_nil, q₁, List.mem_map] at he
      rcases he with ⟨a, ha, rfl⟩
      exact ⟨rfl, hw a ha⟩
    · simp only [q₁, List.pairwise_map]
      exact hsorted
    · intro _ _ _ _ z hz
      simp at hz
  have hne_q : q₁ ++ (FifoQueue.empty : FifoQueue (WeightedTree α β)).toList ≠ [] := by
    simp only [FifoQueue.toList_empty, List.append_nil, q₁]
    intro hnil
    exact hne (List.map_eq_nil_iff.mp hnil)
  rcases twoQueueLoopM_correct hinv hne_q with ⟨T, hT_ret, hT_build⟩
  have hmap_trees : ((q₁ ++ (FifoQueue.empty : FifoQueue (WeightedTree α β)).toList).map
      WeightedTree.tree) = syms.map .leaf := by
    simp [q₁, List.map_map, Function.comp_def]
  rw [hmap_trees] at hT_build
  exact ⟨T, hT_ret, hT_build, hT_build.leaves_perm⟩

/-- **End-to-End Correctness of `huffman`**: on any nonempty symbol list `syms` with nonnegative
weights, `huffman w syms` returns `some T` satisfying `IsHuffmanBuild w (syms.map .leaf) T` and
`T.leaves.Perm syms`. -/
theorem huffman_spec {α β : Type}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {syms : List α}
    (hne : syms ≠ [])
    (hw : ∀ a ∈ syms, 0 ≤ w a) :
    ∃ T, huffman w syms = some T ∧
      IsHuffmanBuild w (syms.map .leaf) T ∧
      T.leaves.Perm syms := by
  let cmp : α → α → Bool := fun a b => decide (w a ≤ w b)
  let sorted := syms.mergeSort cmp
  have hperm : sorted.Perm syms := List.mergeSort_perm syms cmp
  have hsorted_ne : sorted ≠ [] := fun hnil =>
    hne (List.Perm.nil_eq (hnil ▸ hperm)).symm
  have hpw : sorted.Pairwise (fun a b => w a ≤ w b) := by
    have htot : ∀ a b, (cmp a b || cmp b a) = true := by
      intro a b
      simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (w a) (w b)
    have htr : ∀ a b c, cmp a b = true → cmp b c = true → cmp a c = true := by
      intro a b c hab hbc
      simp only [cmp, decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc
    simpa [cmp, decide_eq_true_eq] using List.pairwise_mergeSort htr htot syms
  have hw_sorted : ∀ a ∈ sorted, 0 ≤ w a := fun a ha => hw a (hperm.subset ha)
  rcases huffmanFromSorted_spec hsorted_ne hpw hw_sorted with ⟨T, hT_eq, hT_build, hT_perm⟩
  have hret : huffman w syms = huffmanFromSorted w sorted := by
    simp [huffman, huffmanM, Cslib.Algorithms.Lean.TimeM.ret_mergeSortM, sorted, cmp]
  rw [← hret] at hT_eq
  have hbuild_syms : IsHuffmanBuild w (syms.map .leaf) T :=
    IsHuffmanBuild.of_perm (hperm.symm.map CodeTree.leaf) hT_build
  exact ⟨T, hT_eq, hbuild_syms, hT_perm.trans hperm⟩

/-- **Optimality of `huffman` over Full Binary Code Trees**: the tree returned by `huffman w syms`
minimizes `weightedPathLength w` among all full binary `CodeTree α`s with leaf multiset `syms`. -/
theorem huffman_optimal {α β : Type}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {w : α → β} {syms : List α} {T : CodeTree α}
    (hw : ∀ a ∈ syms, 0 ≤ w a)
    (hT : huffman w syms = some T)
    (T' : CodeTree α) (hT' : T'.leaves.Perm syms) :
    T.weightedPathLength w ≤ T'.weightedPathLength w := by
  have hne : syms ≠ [] := fun hnil =>
    T'.leaves_ne_nil (List.Perm.eq_nil (hnil ▸ hT'))
  rcases huffman_spec hne hw with ⟨T₀, hT₀, hbuild, _⟩
  rw [hT] at hT₀
  injection hT₀ with hEq
  subst hEq
  exact hbuild.weightedPathLength_le T' hT'

/-- **Optimality of `huffman` over All Prefix-Free Binary Codes**: on distinct symbols `syms` with
nonnegative weights, `huffman w syms` achieves weighted path length at most that of *any* injective
`InformationTheory.IsPrefixFree` binary code. -/
theorem huffman_optimal_isPrefixFree {α β : Type}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {syms : List α} (hne : syms ≠ []) (hnodup : syms.Nodup)
    {w : α → β} (hw : ∀ a ∈ syms, 0 ≤ w a)
    {T : CodeTree α} (hT : huffman w syms = some T)
    {code : α → List Bool}
    (hinj : Set.InjOn code {a | a ∈ syms})
    (hpf : InformationTheory.IsPrefixFree (code '' {a | a ∈ syms})) :
    T.weightedPathLength w ≤ (syms.map fun a => (code a).length • w a).sum := by
  rcases huffman_spec hne hw with ⟨T₀, hT₀, hbuild, _⟩
  rw [hT] at hT₀
  injection hT₀ with hEq
  subst hEq
  exact hbuild.weightedPathLength_le_of_isPrefixFree hne hnodup hw hinj hpf

/-- **Optimality of `huffman` over All Uniquely Decodable Binary Codes**: on distinct symbols `syms`
with nonnegative weights, `huffman w syms` achieves weighted path length at most that of *any*
injective `InformationTheory.IsUniquelyDecodable` binary code. -/
theorem huffman_optimal_isUniquelyDecodable {α β : Type}
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {syms : List α} (hne : syms ≠ []) (hnodup : syms.Nodup)
    {w : α → β} (hw : ∀ a ∈ syms, 0 ≤ w a)
    {T : CodeTree α} (hT : huffman w syms = some T)
    {code : α → List Bool}
    (hinj : Set.InjOn code {a | a ∈ syms})
    (hud : InformationTheory.IsUniquelyDecodable (code '' {a | a ∈ syms})) :
    T.weightedPathLength w ≤ (syms.map fun a => (code a).length • w a).sum := by
  rcases huffman_spec hne hw with ⟨T₀, hT₀, hbuild, _⟩
  rw [hT] at hT₀
  injection hT₀ with hEq
  subst hEq
  exact hbuild.weightedPathLength_le_of_isUniquelyDecodable hne hnodup hw hinj hud

end Cslib.Algorithms.Lean.Huffman
