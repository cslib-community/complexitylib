/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Alloc
public import Complexity.DataStructure.Memory.Triple
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Memory

/-!
# Allocating an empty Fibonacci heap in already-zero memory

The word RAM's input convention is zero beyond the input. Under `Memory.ZeroAbove`, the
existing Fibonacci-heap layout therefore needs no clearing: one `Memory.allocDirty` query
reserves its `9 n + 5` cells and establishes the existing framed refinement at the empty queue.
Previously allocated cells are unchanged. This is an oracle-cost certificate; a native
realization must additionally charge address arithmetic, argument preparation and control.

## Main definitions

* `zeroAllocator`: the existing memory allocator interface, with `ZeroAbove` as precondition
  and one memory unit of allocation cost.

## Main results

* `framed_allocDirty`: already-zero fresh cells establish the existing empty-heap frame.

No new heap representation or execution interface is introduced. This specialized allocator
uses the existing frame and source methods; an allocator that accepts arbitrary fresh contents
must still establish the representation, for example by clearing its storage.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap

open Cslib.WordRAM

variable {n w K : ℕ}

/-- Reserving fresh storage without clearing it establishes the existing empty-heap frame
when memory is already zero above the old frontier. -/
theorem framed_allocDirty (hn : Fits w n) (hK : Fits w K) {s : Memory.State}
    (hz : Memory.ZeroAbove s) :
    (framed hn hK s.frontier).inv ⟨s.mem, s.frontier + (9 * n + 5)⟩ ∧
      (framed hn hK s.frontier).abs ⟨s.mem, s.frontier + (9 * n + 5)⟩ =
        IndexedMinPQ.empty n := by
  have hclear : clear s.mem s.frontier (9 * n + 5) = s.mem := by
    funext a
    simp only [clear, ite_eq_right_iff]
    exact fun ha => (hz a ha.1).symm
  simpa only [hclear] using framed_alloc hn hK s

/-- Allocate an empty indexed Fibonacci heap by reserving its already-zero storage. The
precondition is explicit, and neither the returned base nor the cell count is a native timing
claim. The existing memory methods and framed refinement are retained. -/
@[expose] def zeroAllocator (hn : Fits w n) (hK : Fits w K) :
    Memory.Allocator (indexedMinPQSpec n K) w where
  Handle := ℕ
  alloc := Memory.allocDirty (9 * n + 5)
  methods base := (framed hn hK base).methods
  init := IndexedMinPQ.empty n
  room := 9 * n + 5
  cost := 1
  Pre := Memory.ZeroAbove
  pre_fresh := by
    intro s s' hz _ hmem hfront _ a ha
    rw [hmem a ha]
    exact hz a (hfront.trans ha)
  framed s _ _ := framed hn hK s.frontier
  allocates s hz hroom := by
    obtain ⟨hinv, habs⟩ := framed_allocDirty hn hK hz
    refine ⟨?_, ?_, ?_, rfl, hinv, habs, ?_, ?_⟩
    · change Fits w (s.frontier + (9 * n + 5)) ∧ True
      exact ⟨hroom, trivial⟩
    · change 1 ≤ 1
      exact le_rfl
    · intro a _
      rfl
    · intro a ha
      right
      change a ∈ footprint n s.frontier at ha
      exact (Finset.mem_Ico.mp ha).1
    · change s.frontier + (9 * n + 5) + 0 ≤ s.frontier + (9 * n + 5)
      omega

end Cslib.DataStructure.PriorityQueue.FibonacciHeap
