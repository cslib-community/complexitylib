/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Read
import CslibFrontierTests.WordRAMRealizationPacking

/-! The same read-method witnesses handle present and absent handles, Boolean emptiness and a
maximum fitting key. The shared packing only supplies the kernel's static register ABI;
no algorithm-specific instruction execution or register-frame proof is used. -/

namespace ComplexityTests.WordRAMBinaryHeapRead

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open ComplexityTests.WordRAMRealizationPacking

noncomputable section

private def layout : PriorityQueue.BinaryHeap.Memory.Layout 1 :=
  PriorityQueue.BinaryHeap.Memory.compactLayout 1 0

private def mem (present : Bool) (a : ℕ) : ℕ :=
  if a = 0 then 15
  else if a = 1 ∨ a = 3 then present.toNat
  else if a = 100 then 7 else 0

private def state (present : Bool) : Memory.State := ⟨mem present, 4⟩

private theorem wellFormed (present : Bool) : Memory.WellFormed 4 (state present) := by
  refine ⟨by change Fits 4 4; decide, fun a => ?_⟩
  change Fits 4 (mem present a)
  unfold mem
  split_ifs <;> cases present <;> decide

/-- One selected getKey body returns both the maximum word and the absence tag without any
successor encoding; it preserves all memory, including an inaccessible dirty sentinel. -/
example (present : Bool) :
    ∃ y, ExecWithin 4 (realizes_getKey.code (frontier realizes_getKey)
        (src realizes_getKey) (tmp realizes_getKey))
        (packed realizes_getKey ⟨1, layout, 0⟩ (state present)) y
        (3 * realizes_getKey.factor) ∧
      y.mem = mem present ∧ y.regs (frontier realizes_getKey) = 4 ∧
      (∀ i : Fin 2, y.regs (tmp realizes_getKey
        (Fin.castAdd (realizes_getKey.scratchSize + 1) i)) =
        optionWords (if present then some 15 else none) i) := by
  have hw : ∀ i, Fits 4 (handleWords ⟨1, layout, 0⟩ i) := by
    intro i
    fin_cases i <;> decide +kernel
  have hs : layout.arrays.Allocated (state present) := by
    change 0 + (3 * 1 + 1) ≤ 4
    decide
  have hv : (Memory.spec 4).ValidHistory (state present)
      ((Memory.spec 4).clientHistory (state present)
        (PriorityQueue.BinaryHeap.Memory.getKey layout 0)) := by
    cases present <;> decide +kernel
  obtain ⟨y, hy, hm, ho⟩ := native realizes_getKey 4 ⟨1, layout, 0⟩ (state present)
    hw (wellFormed present) hs hv
  simp only [Fin.val_zero] at hy hm ho
  have hc : memoryCost (PriorityQueue.BinaryHeap.Memory.getKey layout 0) (state present) ≤ 2 :=
    by cases present <;> decide +kernel
  have hr : (Memory.spec 4).clientResult (state present)
      (PriorityQueue.BinaryHeap.Memory.getKey layout 0) = if present then some 15 else none :=
    by cases present <;> decide +kernel
  have ht : (Memory.spec 4).clientState (state present)
      (PriorityQueue.BinaryHeap.Memory.getKey layout 0) = state present := by
    cases present <;> rfl
  refine ⟨y, hy.mono ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_comm] using Nat.mul_le_mul_left realizes_getKey.factor (by omega :
      memoryCost (PriorityQueue.BinaryHeap.Memory.getKey layout 0) (state present) + 0 + 1 ≤ 3)
  · have hh := congrArg Memory.State.mem hm
    rw [ht] at hh
    exact hh
  · have hh := congrArg Memory.State.frontier hm
    rw [ht] at hh
    exact hh
  · simpa only [hr] using ho

/-- The same emptiness witness reads either size value and returns a true/false tag; its
instruction budget is constant rather than the logarithmic update-method allowance. -/
example (present : Bool) :
    ∃ y, ExecWithin 4 (realizes_isEmpty.code (frontier realizes_isEmpty)
        (src realizes_isEmpty) (tmp realizes_isEmpty))
        (packed realizes_isEmpty ⟨1, layout⟩ (state present)) y
        (2 * realizes_isEmpty.factor) ∧
      y.mem = mem present ∧
      (∀ i : Fin 2, y.regs (tmp realizes_isEmpty
        (Fin.castAdd (realizes_isEmpty.scratchSize + 1) i)) = boolWords (!present) i) := by
  have hw : ∀ i, Fits 4 (layoutWords ⟨1, layout⟩ i) := by
    intro i
    fin_cases i <;> decide +kernel
  have hs : layout.size.length = 1 ∧ layout.size.Allocated (state present) := by
    exact ⟨rfl, by change 1 + 1 ≤ 4; decide⟩
  have hv : (Memory.spec 4).ValidHistory (state present)
      ((Memory.spec 4).clientHistory (state present)
        (PriorityQueue.BinaryHeap.Memory.isEmpty layout)) := by
    cases present <;> decide +kernel
  obtain ⟨y, hy, hm, ho⟩ := native realizes_isEmpty 4 ⟨1, layout⟩ (state present)
    hw (wellFormed present) hs hv
  have hc : memoryCost (PriorityQueue.BinaryHeap.Memory.isEmpty layout) (state present) = 1 :=
    by cases present <;> rfl
  have hr : (Memory.spec 4).clientResult (state present)
      (PriorityQueue.BinaryHeap.Memory.isEmpty layout) = !present := by
    cases present <;> rfl
  have ht : (Memory.spec 4).clientState (state present)
      (PriorityQueue.BinaryHeap.Memory.isEmpty layout) = state present := rfl
  refine ⟨y, hy.mono ?_, ?_, ?_⟩
  · rw [hc]
    omega
  · have hh := congrArg Memory.State.mem hm
    rw [ht] at hh
    exact hh
  · simpa only [hr] using ho

end

end ComplexityTests.WordRAMBinaryHeapRead
