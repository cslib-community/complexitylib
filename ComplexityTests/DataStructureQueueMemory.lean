/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Queue.Memory

/-!
# A queue over two array stacks, run on concrete memory

A client enqueues three words and dequeues four times; the third dequeue empties the rear stack
into the front. The run allocates both stacks in empty memory at word size `8` with capacity `3`.
The tests check its answers against the queue specification, its exact memory cost against the
proved bound `6 + 9 m`, the admissibility of every memory operation, and that the general
theorems apply: their room and admissibility hypotheses hold here.
-/

@[expose] public section

namespace ComplexityTests.DataStructureQueueMemory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Queue
  Cslib.DataStructure.Queue.Memory

/-- Enqueue `1, 2`, dequeue, enqueue `3`, then dequeue three times. -/
def client : (Queue.WordRAM.spec 8 3).Client (List (Option ℕ)) := do
  (Queue.WordRAM.spec 8 3).call (.enqueue 1)
  (Queue.WordRAM.spec 8 3).call (.enqueue 2)
  let a ← (Queue.WordRAM.spec 8 3).call .dequeue
  (Queue.WordRAM.spec 8 3).call (.enqueue 3)
  let b ← (Queue.WordRAM.spec 8 3).call .dequeue
  let c ← (Queue.WordRAM.spec 8 3).call .dequeue
  let d ← (Queue.WordRAM.spec 8 3).call .dequeue
  pure [a, b, c, d]

/-- Empty memory with nothing allocated. -/
def empty : State := ⟨fun _ => 0, 0⟩

/-- FIFO answers, and an empty queue at the end. -/
example : (Queue.WordRAM.spec 8 3).clientResult [] client = [some 1, some 2, some 3, none] := by
  decide

/-- The run over memory gives the same answers. -/
example : (spec 8).clientResult empty (run 8 3 client) = [some 1, some 2, some 3, none] := by
  decide

/-- Its exact memory cost: 6 for the allocations and 43 for the seven queue operations, against
the proved bound `6 + 9 · 7 = 69`. The dequeue that moves two elements costs 17 alone. -/
example : (spec 8).totalCost charge empty ((spec 8).clientHistory empty (run 8 3 client)) = 49 := by
  decide

/-- Every memory operation of the run is admissible. -/
example : (spec 8).ValidHistory empty ((spec 8).clientHistory empty (run 8 3 client)) := by
  decide

/-- The client is admissible for the bounded queue. -/
theorem client_valid :
    (Queue.WordRAM.spec 8 3).ValidHistory [] ((Queue.WordRAM.spec 8 3).clientHistory [] client) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, trivial, ⟨by decide, by decide⟩, trivial,
    trivial, trivial, trivial⟩

/-- The general theorems apply: empty memory has room for both stacks at this word size. -/
theorem room : Fits 8 (empty.frontier + 2 * (3 + 1)) := by decide

example : (spec 8).clientResult empty (run 8 3 client) =
    (Queue.WordRAM.spec 8 3).clientResult [] client :=
  (run_correct client room client_valid).2

example : (spec 8).totalCost charge empty ((spec 8).clientHistory empty (run 8 3 client)) ≤ 69 :=
  run_cost client room client_valid

/-- A memory with too little room: the second stack would end past the 4-bit word range. -/
example : ¬Fits 4 (empty.frontier + 2 * (7 + 1)) := by decide

end ComplexityTests.DataStructureQueueMemory
