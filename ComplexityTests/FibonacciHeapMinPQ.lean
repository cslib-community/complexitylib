/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.MinPQ

/-!
# The Fibonacci heap with handles and values, run over memory

A client of the handle-allocating queue on three handles inserts two entries, extracts the
minimum (freeing its handle), inserts again (reusing the freed handle), reads it back, lowers the
other key, and extracts twice. It runs over empty memory at word size `7`, through
`MinPQ.allocAllocator`, which allocates the heap's `9 · 3 + 5` cells and the slots'
`2 · 3 + 2` cells. The tests check the answers, the reused handle, the exact memory cost, and
that `run_correct` and `run_cost` apply.
-/

@[expose] public section

namespace ComplexityTests.FibonacciHeapMinPQ

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
  Cslib.DataStructure.PriorityQueue.FibonacciHeap.MinPQ

/-- The allocator on three handles, keys below `9`, values below `99`. -/
abbrev Q : StateTransitionSpec := allocSpec 3 9 99

/-- Insert `(5, 50)` and `(3, 30)`; extract; insert `(7, 70)`; get handle `1`; lower handle
`0`'s key to `2`; extract twice. -/
def client : Q.Client (List (Option (ℕ × ℕ × Fin 3)) × Option (ℕ × ℕ)) := do
  let _ ← Q.call (.insert 5 50)
  let _ ← Q.call (.insert 3 30)
  let x ← Q.call .extractMin
  let _ ← Q.call (.insert 7 70)
  let g ← Q.call (.get 1)
  Q.call (.decreaseKey 0 2)
  let y ← Q.call .extractMin
  let z ← Q.call .extractMin
  pure ([x, y, z], g)

theorem hn : Fits 7 3 := by decide

theorem hU : Fits 7 9 := by decide

theorem hV : Fits 7 99 := by decide

/-- The queue in memory. -/
abbrev pq : Memory.Allocator Q 7 := allocAllocator hn hU hV

/-- Empty memory. -/
def empty : Memory.State := ⟨fun _ => 0, 0⟩

/-- The specification's answers: `(3, 30)` at handle `1`; then handle `1` is reused for
`(7, 70)`; then `(2, 50)` at handle `0`, and `(7, 70)`. -/
example : Q.clientResult pq.init client =
    ([some (3, 30, 1), some (2, 50, 0), some (7, 70, 1)], some (7, 70)) := by
  decide

/-- The client is admissible. -/
theorem client_valid : Q.ValidHistory pq.init (Q.clientHistory pq.init client) :=
  ⟨by simp only [minPQSpec]; decide, by simp only [minPQSpec]; decide, trivial,
    by simp only [minPQSpec]; decide, trivial, ⟨5, 50, by decide, by decide⟩, trivial, trivial,
    trivial⟩

set_option maxRecDepth 20000 in
/-- The run over memory gives the same answers. -/
example : (Memory.spec 7).clientResult empty (pq.run client) =
    ([some (3, 30, 1), some (2, 50, 0), some (7, 70, 1)], some (7, 70)) := by
  decide

set_option maxRecDepth 20000 in
/-- Its exact cost: `182` memory units, `42` of them for zeroing the `40` cells. -/
example : (Memory.spec 7).totalCost Memory.charge empty
    ((Memory.spec 7).clientHistory empty (pq.run client)) = 182 := by
  decide

/-- The amortized bound: `720` for the eight operations, plus `42` for the allocation. -/
example : Q.totalCost (allocCharge 3) pq.init (Q.clientHistory pq.init client) = 720 ∧
    pq.cost = 42 ∧ pq.room = 40 := by
  decide

/-- The memory has room for the queue at word size `7`. -/
theorem room : Fits 7 (empty.frontier + pq.room) := by decide

set_option maxRecDepth 20000 in
/-- **The general theorems apply**: the run is admissible, answers as the allocator, and costs at
most `42 + 720`. -/
example : (Memory.spec 7).ValidHistory empty ((Memory.spec 7).clientHistory empty (pq.run client)) ∧
    (Memory.spec 7).clientResult empty (pq.run client) = Q.clientResult pq.init client ∧
    (Memory.spec 7).totalCost Memory.charge empty
      ((Memory.spec 7).clientHistory empty (pq.run client)) ≤ 42 + 720 := by
  obtain ⟨hv, hres⟩ := run_correct hn hU hV client room client_valid
  have hc := run_cost hn hU hV client room client_valid
  have h720 : Q.totalCost (allocCharge 3) pq.init (Q.clientHistory pq.init client) = 720 := by
    decide
  have h42 : pq.cost = 42 := by decide
  exact ⟨hv, hres, by rw [h720, h42] at hc; exact hc⟩

end ComplexityTests.FibonacciHeapMinPQ
