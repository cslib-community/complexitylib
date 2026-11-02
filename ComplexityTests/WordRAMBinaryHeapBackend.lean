/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Backend

/-! A concrete resident empty heap instantiates the complete generic backend at width one.
The operation executes its actual selected body from the documented prepared calling convention;
argument installation and initialization are not counted as native instructions here. -/

namespace ComplexityTests.WordRAMBinaryHeapBackend

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

private def layout : PriorityQueue.BinaryHeap.Memory.Layout 0 :=
  PriorityQueue.BinaryHeap.Memory.compactLayout 0 0
private def state : Memory.State := ⟨fun a => if a = 100 then 1 else 0, 1⟩
private theorem valid : layout.Valid 1 0 :=
  PriorityQueue.BinaryHeap.Memory.valid_compactLayout (by decide +kernel) (by decide +kernel)
private theorem inv : PriorityQueue.BinaryHeap.Memory.Inv layout state := by
  apply (PriorityQueue.BinaryHeap.Memory.inv_empty ?_ ?_ rfl ?_).1
  · change 0 + 1 ≤ 1; decide
  · change 0 + (3 * 0 + 1) ≤ 1; decide
  · intro v hv; omega
private theorem wellFormed : Memory.WellFormed 1 state := by
  refine ⟨by decide +kernel, fun a => ?_⟩
  change Fits 1 (if a = 100 then 1 else 0)
  split_ifs <;> decide

-- Read-only operation charges remain constant rather than being enlarged to O(log n).
example (n : ℕ) : memoryBound (IndexedMinPQ.Op.isEmpty (n := n)) = 1 := rfl
example {n : ℕ} (v : Fin n) : memoryBound (IndexedMinPQ.Op.getKey v) = 2 := rfl

noncomputable section

private abbrev data := Backend.data certificates state
private theorem represented :
    (implementation layout valid).rep (PriorityQueue.BinaryHeap.Memory.abs layout state) data :=
  Backend.rep_data (implements layout valid) wellFormed inv rfl

-- The common register bank/factor and tag-4 body do not depend on n, K, layout or width.
example : ∃ y steps, Exec 1 (Backend.code certificates 4)
      ((backend 0 0 layout).prepare .extractMin data) y steps ∧
    steps ≤ Backend.factor certificates * (PriorityQueue.BinaryHeap.Memory.opCost 0 + 1) ∧
    y.mem = state.mem ∧ y.mem 100 = 1 := by
  obtain ⟨a, y, steps, he⟩ := (implementation layout valid).total .extractMin represented trivial
  have hv : IndexedMinPQ.valid 0 (PriorityQueue.BinaryHeap.Memory.abs layout state)
      .extractMin := trivial
  have hc := bound layout valid represented hv he
  have hm := Backend.exec_memoryState (implements layout valid) represented hv he
  have hp := (Backend.exec_iff (backend 0 0 layout) 1 data y .extractMin a steps).mp he
  refine ⟨y, steps, hp.1, hc, ?_, ?_⟩
  · exact congrArg Memory.State.mem hm
  · have hmem := congrArg Memory.State.mem hm
    change y.mem = state.mem at hmem
    rw [hmem]
    rfl

-- An actual body execution also inherits the existing footprint frame.
example {y : Data (Backend.registers certificates)} {a : Option (Fin 0 × ℕ)} {steps : ℕ}
    (he : (backend 0 0 layout).exec 1 data .extractMin a y steps) : y.mem 100 = 1 := by
  have hv : IndexedMinPQ.valid 0 (PriorityQueue.BinaryHeap.Memory.abs layout state)
      .extractMin := trivial
  have h := modifies layout valid represented hv he
  exact h 100 (by decide +kernel)

end

end ComplexityTests.WordRAMBinaryHeapBackend
