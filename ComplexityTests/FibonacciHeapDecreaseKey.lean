/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.DecreaseKey

/-!
# The record Fibonacci heap's `decreaseKey` on a concrete heap

A heap on three handles is one chain: root `0` with child `1` with child `2`, and `1` is marked.
It satisfies `Inv`, proved here directly, so the invariant and its `Cascading` form have a
concrete instance with a marked node. Decreasing the key of `2` below its parent's cuts `2`, and
the cascade cuts the marked `1` in turn. The tests check the result by evaluation (the keys, the
three unmarked roots, the minimum root, the exact cost) and apply `wp_decreaseKey`, which gives
admissibility, the invariant of the result and the amortized bound `104`.
-/

@[expose] public section

namespace ComplexityTests.FibonacciHeapDecreaseKey

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
  Cslib.DataStructure.PriorityQueue.FibonacciHeap
  Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- The record specification for heaps on three handles at word size `4`. -/
abbrev heap : StateTransitionSpec := Record.spec (Cell.ok 3) 4

/-- Root `0` (key `1`) with child `1` (key `5`, marked) with child `2` (key `7`). Each child list
and the root list is a one-element circular list. -/
def chain : Cell → ℕ
  | .key 0 => 1 | .key 1 => 5 | .key 2 => 7
  | .par 1 => 0 + 1 | .par 2 => 1 + 1
  | .child 0 => 1 + 1 | .child 1 => 2 + 1
  | .left 1 => 1 | .right 1 => 1 | .left 2 => 2 | .right 2 => 2
  | .deg 0 => 1 | .deg 1 => 1
  | .mark 1 => 1
  | .inHeap 0 => 1 | .inHeap 1 => 1 | .inHeap 2 => 1
  | .minRoot => 0 + 1 | .numRoots => 1 | .numMarked => 1 | .sz => 3
  | _ => 0

/-- The chain as a tree. -/
def tree : FHTree 3 := .node 0 [.node 1 [.node 2 []]]

/-- The chain is a valid root tree. -/
theorem valid_tree : ValidRoot (view 3 chain) none tree := by
  refine ⟨.mk (by decide) (by decide) rfl
      (Or.inr ⟨1, [], rfl, by unfold IsCircList ChainLinks; decide, by decide⟩)
      (by decide) (by decide) (fun i hi => by simp at hi; omega) fun T hT => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hT
  subst hT
  refine .mk (by decide) (by decide) rfl
    (Or.inr ⟨2, [], rfl, by unfold IsCircList ChainLinks; decide, by decide⟩)
    (by decide) (by decide) (fun i hi => by simp at hi; omega) fun T hT => ?_
  simp only [List.mem_singleton] at hT
  subst hT
  exact .mk (by decide) (by decide) rfl (Or.inl ⟨rfl, rfl⟩) (by simp) (by simp) (by simp) (by simp)

/-- **The invariant has an instance with a marked node**: the chain is a valid heap. -/
theorem inv_chain : Inv 3 9 chain := by
  refine ⟨[tree], by simpa using valid_tree, by decide, fun v => by revert v; decide,
    fun v => by revert v; decide, fun v k h => ?_, by decide, rfl, by decide, by decide,
    Or.inr ⟨0, [], rfl, by unfold IsCircList ChainLinks; decide, by decide, by decide⟩⟩
  fin_cases v <;> simp [FibonacciHeap.abs, absRaw, view, chain] at h ⊢ <;> omega

/-- So the forest is `Cascading` for `2`, with nothing pending. -/
example : ∃ m ts, Cascading 3 9 (abs 3 chain) (view 3 chain) 2 m none ts :=
  cascading_of_fibRawInv inv_chain (by decide)

/-- Decrease the key of `2` from `7` to `3`. -/
abbrev lower : Prog Unit := decreaseKey 3 2 3

/-- The keys after the run. -/
example : abs 3 (heap.clientState chain lower) = ![some 1, some 5, some 3] := by decide

/-- Both cuts happened: the three handles are unmarked roots, and `0` is still the minimum. -/
example : (view 3 (heap.clientState chain lower)).numRoots = 3 ∧
    (view 3 (heap.clientState chain lower)).numMarked = 0 ∧
    (∀ v : Fin 3, (view 3 (heap.clientState chain lower)).par v = 0 ∧
      (view 3 (heap.clientState chain lower)).mark v = 0) ∧
    (view 3 (heap.clientState chain lower)).minRoot = 0 + 1 := by decide

/-- The run's exact cost in record operations. -/
example : (heap.clientHistory chain lower).length = 40 := by decide

/-- The potential before and after: one root and one mark, then three roots. -/
example : potential 3 chain = 72 ∧ potential 3 (heap.clientState chain lower) = 72 := by decide

/-- **The specification applies**: `wp_decreaseKey` on this run. -/
theorem lower_spec : Record.wp (Cell.ok 3) 4 lower (fun _ g' t =>
    abs 3 g' = Function.update (abs 3 chain) 2 (some 3) ∧ Inv 3 9 g' ∧
      t + potential 3 g' ≤ 104 + potential 3 chain) chain :=
  wp_decreaseKey (v := 2) (k₀ := 7) (k := 3) (w := 4) inv_chain (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- So the run is admissible, the result is a valid heap, and the cost is within the bound. -/
example : heap.ValidHistory chain (heap.clientHistory chain lower) ∧
    Inv 3 9 (heap.clientState chain lower) ∧
    (heap.clientHistory chain lower).length + potential 3 (heap.clientState chain lower) ≤
      104 + potential 3 chain := by
  obtain ⟨hv, -, hI, hc⟩ := (Record.wp_iff _ _ _).mp lower_spec
  exact ⟨hv, hI, hc⟩

end ComplexityTests.FibonacciHeapDecreaseKey
