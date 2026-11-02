/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.PriorityQueue.BinaryHeap.Memory

/-!
# An indexed binary heap over the memory oracle, run on concrete memory

A client inserts three handles, lowers one key, and extracts four times, the last time from an
empty queue. Two handles share a key, so the extractions also check the tie-break toward the
smaller handle. The run allocates a heap on four handles in empty memory at word size `8`. The
tests check its answers against the specification, its exact memory cost against the proved
bound `2 + 8 opCost 4`, the admissibility of every memory operation, and that the hypotheses of
the general theorems hold here.
-/

namespace ComplexityTests.DataStructureBinaryHeapMemory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
  Cslib.DataStructure.PriorityQueue.BinaryHeap.Memory
open Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap (space)

/-- The queue on four handles with keys at most `9`. -/
abbrev Q : StateTransitionSpec := indexedMinPQSpec 4 9

/-- Insert `2 ↦ 5`, `0 ↦ 3`, `3 ↦ 3`; lower the key of `2` to `1`; extract four times. -/
def client : Q.Client (List (Option (Fin 4 × ℕ))) := do
  Q.call (.insert 2 5)
  Q.call (.insert 0 3)
  Q.call (.insert 3 3)
  Q.call (.decreaseKey 2 1)
  let a ← Q.call .extractMin
  let b ← Q.call .extractMin
  let c ← Q.call .extractMin
  let d ← Q.call .extractMin
  pure [a, b, c, d]

/-- Allocate a heap on four handles, then run the client on it. -/
def run : Prog (List (Option (Fin 4 × ℕ))) := do
  let L ← allocLayout 4
  link (methods L 8 9) client

/-- Empty memory with nothing allocated. -/
def empty : State := ⟨fun _ => 0, 0⟩

-- The specification's answers: smallest key first, and handle `0` before handle `3` at key `3`.
#guard Q.clientResult (IndexedMinPQ.empty 4) client =
  [some (2, 1), some (0, 3), some (3, 3), none]

-- The run over memory gives the same answers.
#guard (spec 8).clientResult empty run = [some (2, 1), some (0, 3), some (3, 3), none]

-- Every memory operation of the run is admissible at word size `8`.
#guard decide ((spec 8).ValidHistory empty ((spec 8).clientHistory empty run))

-- Its exact memory cost, against the bound `2 + 8 · opCost 4 = 274` from allocation and
-- `amortized`.
#guard (spec 8).totalCost charge empty ((spec 8).clientHistory empty run) = 69

example : 2 + 8 * opCost 4 = 274 := by decide

/-- The hypotheses of the general theorems hold: the allocated layout is well formed, and empty
memory is zero above its frontier. -/
example : (allocated 4 empty.frontier).Valid 8 9 := valid_allocated (by decide) (by decide)

example : ZeroAbove empty := fun _ _ => rfl

example : Inv (allocated 4 empty.frontier) ⟨empty.mem, empty.frontier + 1 + space 4⟩ :=
  (inv_allocated (s := empty) fun _ _ => rfl).1

/-- A word size too small for the keys: `9` does not fit three bits. -/
example : ¬Fits 3 9 := by decide

end ComplexityTests.DataStructureBinaryHeapMemory
