/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Memory

/-!
# The Fibonacci heap over memory, on a concrete client

A client of the indexed priority queue on four handles inserts four keys, extracts the minimum
(which consolidates the other three), decreases a key below its parent's (which cuts it), and
extracts the minimum twice more. It runs over memory through `memRefinement`, with the heap's
`9 · 4 + 5 = 41` cells zeroed at addresses `0, …, 40`, at word size `6`.

The tests check the answers against the specification, the exact memory cost of the run, the
amortized bound `4 · 43 + 104 + 276 + 2 · 184 = 920` of `charge`, and that the general theorems
apply: `simulates_client` gives the answers and admissibility, and `Amortized.client` with
`mem_amortized` gives the bound.
-/

@[expose] public section

namespace ComplexityTests.FibonacciHeapMemory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
  Cslib.DataStructure.PriorityQueue.FibonacciHeap

/-- The indexed priority queue on four handles with keys at most `9`. -/
abbrev pq : StateTransitionSpec := indexedMinPQSpec 4 9

/-- Insert keys `5, 3, 8, 6` at handles `0, 1, 2, 3`; extract the minimum; lower the key of `2`
to `1`; extract the minimum twice. -/
def client : pq.Client (List (Option (Fin 4 × ℕ))) := do
  pq.call (.insert 0 5)
  pq.call (.insert 1 3)
  pq.call (.insert 2 8)
  pq.call (.insert 3 6)
  let a ← pq.call .extractMin
  pq.call (.decreaseKey 2 1)
  let b ← pq.call .extractMin
  let c ← pq.call .extractMin
  pure [a, b, c]

/-- The specification's answers: `(1, 3)`, then the lowered `(2, 1)`, then `(0, 5)`. -/
example :
    pq.clientResult (IndexedMinPQ.empty 4) client = [some (1, 3), some (2, 1), some (0, 5)] := by
  decide

/-- The client is admissible: handles are fresh on insertion, and the key decrease lowers a
present key. -/
theorem client_valid : pq.ValidHistory (IndexedMinPQ.empty 4)
    (pq.clientHistory (IndexedMinPQ.empty 4) client) :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    trivial, ⟨⟨8, by decide, by decide⟩, by decide⟩, trivial, trivial, trivial⟩

/-- Word size `6` fits the handle count and the key bound. -/
theorem hn : Fits 6 4 := by decide

theorem hK : Fits 6 9 := by decide

/-- The heap over memory at base address `0`. -/
abbrev heap : Refinement pq (Memory.spec 6) := memRefinement hn hK 0

/-- Memory with the heap's 41 cells allocated and zeroed. -/
def mem : Memory.State := ⟨fun _ => 0, 41⟩

/-- The zeroed cells hold the empty heap. -/
theorem mem_inv : heap.inv mem := by
  refine ⟨fun i hi => ?_, ?_⟩
  · cases i <;> simp only [Cell.ok, layout, mem] at hi ⊢ <;> omega
  · have hzero : (layout 4 0).abs mem = fun _ => 0 := by
      funext i
      simp [Record.Layout.abs, mem]
    change Inv 4 9 ((layout 4 0).abs mem)
    rw [hzero]
    exact (inv_of_fibRawInv (WordRAM.FibonacciHeap.FibRawInv.empty (fun _ => rfl)
      (fun _ _ => rfl) rfl rfl rfl rfl)).1

theorem abs_mem : heap.abs mem = IndexedMinPQ.empty 4 := by
  funext v
  fin_cases v <;> decide

set_option maxRecDepth 20000 in
/-- The run over memory gives the same answers. -/
example : (Memory.spec 6).clientResult mem (link heap.methods client) =
    [some (1, 3), some (2, 1), some (0, 5)] := by
  decide

set_option maxRecDepth 20000 in
/-- Its exact cost: `213` memory units, one per record operation. -/
example : (Memory.spec 6).totalCost Memory.charge mem
    ((Memory.spec 6).clientHistory mem (link heap.methods client)) = 213 := by
  decide

/-- The amortized bound: `43` per insertion, `104` for the key decrease, and
`92 · (log₂ m + 1)` for an extraction from `m` handles: `276` from four, `184` from three and
from two. -/
example : pq.totalCost (charge 4) (IndexedMinPQ.empty 4)
    (pq.clientHistory (IndexedMinPQ.empty 4) client) = 920 := by
  decide

set_option maxRecDepth 20000 in
/-- **The refinement theorem applies**: the memory run is admissible and answers as the
specification. -/
example : (Memory.spec 6).ValidHistory mem
      ((Memory.spec 6).clientHistory mem (link heap.methods client)) ∧
    (Memory.spec 6).clientResult mem (link heap.methods client) =
      pq.clientResult (IndexedMinPQ.empty 4) client := by
  obtain ⟨hv, hres, -⟩ :=
    heap.simulates_client client mem_inv (by rw [abs_mem]; exact client_valid)
  rw [abs_mem] at hres
  exact ⟨hv, hres⟩

set_option maxRecDepth 20000 in
/-- **The amortized bound applies**: the memory cost and the final potential are at most `920`,
the empty heap's potential being `0`. -/
example : (Memory.spec 6).totalCost Memory.charge mem
      ((Memory.spec 6).clientHistory mem (link heap.methods client)) ≤ 920 := by
  have h := (mem_amortized hn hK 0).client client mem_inv (by rw [abs_mem]; exact client_valid)
  have hΦ : potential 4 ((layout 4 0).abs mem) + 0 = 0 := by decide
  have hcharge : pq.totalCost (charge 4) (heap.abs mem) (pq.clientHistory (heap.abs mem) client) =
      920 := by
    rw [abs_mem]
    decide
  rw [hcharge, hΦ] at h
  exact (Nat.le_add_right _ _).trans h

end ComplexityTests.FibonacciHeapMemory
