/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Program

/-! The actual shared register interface initializes the original compact local-zero domain.
These are raw native executions with paid reservation/metadata code. Inaccessible dirty cells
remain literal memory contents; no global-zero allocator premise or free prepare is used. -/

namespace CslibFrontierTests.WordRAMBinaryHeapProgram

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Program

noncomputable section

private def input (n base : ℕ) (mem : ℕ → ℕ) : Data registers where
  regs i := if i = code.frontierReg then base else if i = code.nReg then n else 0
  mem := mem

private theorem input_frontier (n base : ℕ) (mem : ℕ → ℕ) :
    (input n base mem).regs code.frontierReg = base := by simp [input]
private theorem input_n (n base : ℕ) (mem : ℕ → ℕ) :
    (input n base mem).regs code.nReg = n := by
  simp [input, code.nReg_ne_frontier]
private theorem input_bounded {w n base : ℕ} (mem : ℕ → ℕ)
    (hn : Fits w n) (hb : Fits w base) (hm : ∀ a, Fits w (mem a)) :
    (input n base mem).Bounded w := by
  refine ⟨fun i => ?_, hm⟩
  simp only [input]
  split_ifs
  · exact hb
  · exact hn
  · exact fits_zero w

private def minimumMemory (a : ℕ) := if a = 100 then 1 else 0
private def shiftedMemory (a : ℕ) := if a = 0 ∨ a = 100 then 7 else 0
private abbrev initBound :=
  2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor

-- The same compiled interface accepts n=0 at width1 without a gratuitous literal2/3 fit.
example : ∃ y, ExecWithin 1 code.initFresh (input 0 0 minimumMemory) y initBound ∧
    y.mem = minimumMemory ∧ y.mem 100 = 1 ∧ y.regs code.frontierReg = 1 ∧
    y.regs code.nReg = 0 ∧ y.regs code.baseReg = 0 ∧
    y.regs (argument 1) = 0 ∧ y.regs (argument 2) = 1 ∧
    PriorityQueue.BinaryHeap.Memory.Inv (PriorityQueue.BinaryHeap.Memory.compactLayout 0 0)
      (memoryState code.frontierReg y) := by
  have hx : (input 0 0 minimumMemory).Bounded 1 := by
    apply input_bounded _ (by decide) (by decide)
    intro a
    change Fits 1 (if a = 100 then 1 else 0)
    split_ifs <;> decide
  have hz : ∀ a, (Block.mk 0 (PriorityQueue.BinaryHeap.space 0)).Owns a →
      (input 0 0 minimumMemory).mem a = 0 := by
    intro a ha
    change 0 ≤ a ∧ a < 1 at ha
    have he : a = 0 := by omega
    subst a
    rfl
  obtain ⟨y, hy, _, hm, hf, hn, hb, hs, hl, hi, _⟩ :=
    initFresh_exec (input 0 0 minimumMemory) hx (input_frontier ..) (input_n ..)
      (by decide +kernel) hz
  exact ⟨y, hy, hm, congrFun hm 100, hf, hn, hb, hs, hl, hi⟩

-- The old end7 local-zero domain fits width3, while the original allocated3n+2 endpoint end8
-- does not. Both the dirty lower prefix and inaccessible high sentinel remain unchanged.
example : ∃ y, ExecWithin 3 code.initFresh (input 1 3 shiftedMemory) y initBound ∧
    y.mem = shiftedMemory ∧ y.mem 0 = 7 ∧ y.mem 100 = 7 ∧
    y.regs code.frontierReg = 7 ∧ y.regs code.nReg = 1 ∧ y.regs code.baseReg = 3 ∧
    y.regs (argument 1) = 4 ∧ y.regs (argument 2) = 1 ∧
    PriorityQueue.BinaryHeap.Memory.abs (PriorityQueue.BinaryHeap.Memory.compactLayout 1 3)
      (memoryState code.frontierReg y) = IndexedMinPQ.empty 1 := by
  have hx : (input 1 3 shiftedMemory).Bounded 3 := by
    apply input_bounded _ (by decide) (by decide)
    intro a
    change Fits 3 (if a = 0 ∨ a = 100 then 7 else 0)
    split_ifs <;> decide
  have hz : ∀ a, (Block.mk 3 (PriorityQueue.BinaryHeap.space 1)).Owns a →
      (input 1 3 shiftedMemory).mem a = 0 := by
    intro a ha
    change 3 ≤ a ∧ a < 7 at ha
    change (if a = 0 ∨ a = 100 then 7 else 0) = 0
    rw [ite_eq_right (by omega)]
  obtain ⟨y, hy, _, hm, hf, hn, hb, hs, hl, _, ha⟩ :=
    initFresh_exec (input 1 3 shiftedMemory) hx (input_frontier ..) (input_n ..)
      (by decide +kernel) hz
  exact ⟨y, hy, hm, congrFun hm 0, congrFun hm 100, hf, hn, hb, hs, hl, ha⟩

example : ¬Fits 3 8 := by decide
example : ¬∀ a, (Block.mk 3 (PriorityQueue.BinaryHeap.space 1)).Owns a →
    (if a = 6 then 7 else 0) = 0 := by
  intro h
  have hh := h 6 (by change 3 ≤ 6 ∧ 6 < 7; omega)
  contradiction

end

end CslibFrontierTests.WordRAMBinaryHeapProgram
