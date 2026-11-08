/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.ExtractMin

/-!
# The record Fibonacci heap's `extractMin` on concrete heaps

A heap on four handles has two roots: `0` (key `1`), whose children are the leaf `1` (key `5`)
and the marked leaf `2` (key `6`), and the leaf `3` (key `7`). It satisfies `Inv`, proved here
directly. Extracting the minimum returns `(0, 1)`; both children become unmarked roots, and the
second collides with the first in the table's slot of degree `0`, so `2` is linked below `1`;
then `3` takes the emptied slot. The tests check the answer, the keys, the marks, the links, the
cleared table and the exact cost by evaluation, and apply `wp_extractMin`, which gives
admissibility, the invariant of the result and the amortized bound `extractCharge 4 = 276`.

Two edge cases: extraction from the empty heap, and from a heap with one handle, built by
`insert` and so known valid through `wp_insert`.
-/

@[expose] public section

namespace ComplexityTests.FibonacciHeapExtractMin

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
  Cslib.DataStructure.PriorityQueue.FibonacciHeap
  Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- The record specification for heaps on four handles at word size `4`. -/
abbrev heap : StateTransitionSpec := Record.spec (Cell.ok 4) 4

/-- Roots `0` and `3`; the root `0` has the children `1` and `2`, linked in this order, and `2`
is marked. The root list and the child list are two-element circular lists. -/
def twoRoots : Cell → ℕ
  | .key 0 => 1 | .key 1 => 5 | .key 2 => 6 | .key 3 => 7
  | .par 1 => 0 + 1 | .par 2 => 0 + 1
  | .child 0 => 1 + 1
  | .left 0 => 3 | .right 0 => 3 | .left 3 => 0 | .right 3 => 0
  | .left 1 => 2 | .right 1 => 2 | .left 2 => 1 | .right 2 => 1
  | .deg 0 => 2
  | .mark 2 => 1
  | .inHeap 0 => 1 | .inHeap 1 => 1 | .inHeap 2 => 1 | .inHeap 3 => 1
  | .minRoot => 0 + 1 | .numRoots => 2 | .numMarked => 1 | .sz => 4
  | _ => 0

/-- The two trees. The second child `2` may have no children, as its mark makes up its rank. -/
def trees : List (FHTree 4) := [.node 0 [.node 1 [], .node 2 []], .node 3 []]

/-- **The invariant has an instance with a marked child of the minimum root.** -/
theorem inv_twoRoots : Inv 4 9 twoRoots := by
  have hleaf : ∀ v : Fin 4, (view 4 twoRoots).inHeap v ≠ 0 → (view 4 twoRoots).mark v ≤ 1 →
      (view 4 twoRoots).deg v = 0 → (view 4 twoRoots).child v = 0 →
      ValidSubtree (view 4 twoRoots) none (.node v []) := fun v h1 h2 h3 h4 =>
    .mk h1 h2 h3 (Or.inl ⟨rfl, h4⟩) (by simp) (by simp) (by simp) (by simp)
  refine ⟨trees, fun T hT => ?_, by decide, fun v => by revert v; decide,
    fun v => by revert v; decide, fun v k h => ?_, by decide, rfl, by decide, by decide,
    Or.inr ⟨0, [3], rfl, by simp only [IsCircList, ChainLinks]; decide, by decide, by decide⟩⟩
  · simp only [trees, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · refine ⟨.mk (by decide) (by decide) rfl
        (Or.inr ⟨1, [2], rfl, by simp only [IsCircList, ChainLinks]; decide, by decide⟩) (by decide)
        (by decide) (fun i hi => ?_) fun T hT => ?_, rfl, rfl⟩
      · match i with
        | 0 => exact Nat.zero_le _
        | 1 => simp [view, twoRoots]
        | _ + 2 => simp at hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
        rcases hT with rfl | rfl <;> exact hleaf _ (by decide) (by decide) rfl rfl
    · exact ⟨hleaf _ (by decide) (by decide) rfl rfl, rfl, rfl⟩
  · have hkeys : ∀ v : Fin 4, ∀ k ∈ abs 4 twoRoots v, (view 4 twoRoots).key v = k ∧ k ≤ 9 := by
      decide
    exact hkeys v k h

/-- The answer: handle `0` with key `1`. -/
example : heap.clientResult twoRoots (extractMin 4) = some (0, 1) := by decide

/-- The final record. -/
abbrev after : Cell → ℕ := heap.clientState twoRoots (extractMin 4)

/-- `0` is gone; the other keys are unchanged. -/
example : abs 4 after = ![none, some 5, some 6, some 7] := by decide

/-- The marked child `2` was made an unmarked root, collided with `1` in the slot of degree `0`,
and was linked below it: `1` is a root of degree `1` with the child `2`. -/
example : (view 4 after).par 2 = 1 + 1 ∧ (view 4 after).child 1 = 2 + 1 ∧
    (view 4 after).deg 1 = 1 ∧ (view 4 after).par 1 = 0 ∧ (view 4 after).par 3 = 0 := by decide

/-- No mark is left, two roots remain, the new minimum root is `1`, and the table is empty. -/
example : (∀ v : Fin 4, (view 4 after).mark v = 0) ∧ (view 4 after).numMarked = 0 ∧
    (view 4 after).numRoots = 2 ∧ (view 4 after).minRoot = 1 + 1 ∧
    (∀ d ≤ 4, (view 4 after).cons d = 0) := by decide

/-- The run's exact cost in record operations. -/
example : (heap.clientHistory twoRoots (extractMin 4)).length = 65 := by decide

/-- The potential before and after: two roots and one mark, then two roots. -/
example : potential 4 twoRoots = 96 ∧ potential 4 after = 48 := by decide

/-- **The specification applies**: `wp_extractMin` on this run. -/
theorem extract_spec : Record.wp (Cell.ok 4) 4 (extractMin 4) (fun a g' t =>
    IndexedMinPQ.step (abs 4 twoRoots) .extractMin = (abs 4 g', a) ∧ Inv 4 9 g' ∧
      t + potential 4 g' ≤ extractCharge (IndexedMinPQ.dom (abs 4 twoRoots)).card +
        potential 4 twoRoots) twoRoots :=
  wp_extractMin inv_twoRoots (by decide)

/-- So the run is admissible, the result is a valid heap, and the cost is within the bound
`extractCharge 4 = 92 * (log₂ 4 + 1) = 276`. -/
example : heap.ValidHistory twoRoots (heap.clientHistory twoRoots (extractMin 4)) ∧
    Inv 4 9 after ∧
    (heap.clientHistory twoRoots (extractMin 4)).length + potential 4 after ≤
      276 + potential 4 twoRoots := by
  obtain ⟨hv, -, hI, hc⟩ := (Record.wp_iff _ _ _).mp extract_spec
  refine ⟨hv, hI, ?_⟩
  have hcard : (IndexedMinPQ.dom (abs 4 twoRoots)).card = 4 := by decide
  rw [hcard] at hc
  exact hc

/-! ## Edge cases -/

/-- The empty heap: every cell zero. -/
def empty : Cell → ℕ := fun _ => 0

/-- The empty heap is valid. -/
theorem inv_empty : Inv 4 9 empty :=
  (inv_of_fibRawInv (FibRawInv.empty (fun _ => rfl) (fun _ _ => rfl) rfl rfl rfl rfl)).1

/-- Extraction from the empty heap answers `none` in one operation and changes nothing. -/
example : heap.clientResult empty (extractMin 4) = none ∧
    heap.clientState empty (extractMin 4) = empty ∧
    (heap.clientHistory empty (extractMin 4)).length = 1 := by
  refine ⟨by decide, rfl, by decide⟩

/-- One handle, `3` with key `2`, inserted into the empty heap. -/
abbrev single : Cell → ℕ := heap.clientState empty (insert 3 2)

/-- It is valid, by `wp_insert`. -/
theorem inv_single : Inv 4 9 single :=
  ((Record.wp_iff _ _ _).mp (wp_insert (v := 3) (k := 2) (w := 4) inv_empty (by decide)
    (by decide) (by decide) (by decide))).2.2.1

/-- Extracting its only handle answers `(3, 2)` and leaves an empty heap with an empty table. -/
example : heap.clientResult single (extractMin 4) = some (3, 2) ∧
    abs 4 (heap.clientState single (extractMin 4)) = IndexedMinPQ.empty 4 ∧
    (view 4 (heap.clientState single (extractMin 4))).minRoot = 0 ∧
    (view 4 (heap.clientState single (extractMin 4))).numRoots = 0 ∧
    (∀ d ≤ 4, (view 4 (heap.clientState single (extractMin 4))).cons d = 0) := by
  decide

/-- The result satisfies the invariant, by `wp_extractMin`. -/
example : Inv 4 9 (heap.clientState single (extractMin 4)) :=
  ((Record.wp_iff _ _ _).mp (wp_extractMin (w := 4) inv_single (by decide))).2.2.1

end ComplexityTests.FibonacciHeapExtractMin
