/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.SiftDown
import Mathlib.Tactic.IntervalCases

/-! One globally selected emitter handles a left-only swap, a real read-then-stop, a right
selection by the strict handle tie, and index zero. The fixtures retain an inaccessible cell. -/

namespace ComplexityTests.WordRAMBinaryHeapSiftDown

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.SiftDown

private def layout : BinaryHeap.Memory.Layout 4 := ⟨⟨0, 1⟩, 1⟩

/-- Left-only, early stop, key tie/right child, or empty. -/
private def size (mode : Fin 4) : ℕ := if mode = 0 then 2 else if mode = 3 then 0 else 3

private def mem (mode : Fin 4) (a : ℕ) : ℕ :=
  if a = 100 then 7
  else if a = 0 then size mode
  else if a = 1 then if mode = 0 then 15 else if mode = 1 then 0 else 5
  else if a = 2 then if mode = 2 then 5 else 1
  else if a = 3 then if mode = 2 then 5 else 2
  else if a = 6 then if mode = 2 then 2 else 0
  else if a = 7 then 1
  else if a = 8 then if mode = 2 then 0 else 2
  else if a = 10 then if mode = 3 then 0 else if mode = 2 then 3 else 1
  else if a = 11 then if mode = 3 then 0 else 2
  else if a = 12 then if mode = 0 ∨ mode = 3 then 0 else if mode = 2 then 1 else 3
  else 0

private def state (mode : Fin 4) : Memory.State := ⟨mem mode, 14⟩

private theorem shape (mode : Fin 4) : HeapShape 4 layout.base (size mode) (mem mode) := by
  have hS : size mode ≤ 3 := by unfold size; split_ifs <;> omega
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  all_goals
    intro i hi
    try intro hs
    have hi3 : i ≤ 3 := by omega
    interval_cases i <;> fin_cases mode <;> norm_num [layout, mem, size] at *

private theorem down_ordered (mode : Fin 4) :
    DownOrdered (heapEntry 4 layout.base (mem mode)) (size mode) 1 := by
  intro i hi hs
  have hm : size mode ≤ 3 := by unfold size; split_ifs <;> omega
  have hi3 : i ≤ 3 := hs.trans hm
  interval_cases i <;> simp

-- The left-only case omits both right reads; the early stop includes its six reads.
example : memoryCost (BinaryHeap.Memory.siftDown layout (size 0) 1) (state 0) = 8 := by
  decide +kernel
example : memoryCost (BinaryHeap.Memory.siftDown layout (size 1) 1) (state 1) = 6 := by
  decide +kernel
example : memoryCost (BinaryHeap.Memory.siftDown layout (size 2) 1) (state 2) = 10 := by
  decide +kernel
example : memoryCost (BinaryHeap.Memory.siftDown layout (size 3) 0) (state 3) = 0 := by
  decide +kernel

-- Positive active index, zero ghost cutoff: truncation is explicitly inadmissible.
example : ¬whileSafe guard step (fun _ _ _ => True) 4 ((⟨4, layout⟩, 3), 2) 0 1 (state 2) := by
  change ¬¬(1 < 2)
  omega

noncomputable section

private abbrev bankSize := 0 + realizes_siftDown.scratchSize + 1
private abbrev regs := 6 + bankSize + 1
private def frontier : Fin regs := Fin.last (6 + bankSize)
private def src (i : Fin 6) : Fin regs := (Fin.castAdd bankSize i).castSucc
private def tmp (i : Fin bankSize) : Fin regs := (Fin.natAdd 6 i).castSucc

private def packed (mode : Fin 4) (k : ℕ) : Data regs :=
  ⟨Fin.lastCases 14
    (Fin.append (inputWords ((⟨4, layout⟩, size mode), k)) (fun _ => 0)), mem mode⟩

private theorem tmp_injective : Function.Injective tmp := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [tmp] using this

private theorem src_tmp : ∀ i j, src i ≠ tmp j := by
  intro i j h
  have hh := congrArg Fin.val h
  dsimp only [src, tmp, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd] at hh
  omega

private theorem tmp_frontier : ∀ j, tmp j ≠ frontier := by
  intro j h
  have hh := congrArg Fin.val h
  dsimp only [tmp, frontier, Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hh
  omega

private theorem src_frontier : ∀ i, src i ≠ frontier := by
  intro i h
  have hh := congrArg Fin.val h
  dsimp only [src, frontier, Fin.val_castSucc, Fin.val_castAdd, Fin.val_last] at hh
  omega

private theorem packed_input (mode : Fin 4) (k : ℕ) :
    (packed mode k).regs ∘ src = inputWords ((⟨4, layout⟩, size mode), k) := by
  funext i
  simp [packed, src]

private theorem packed_state (mode : Fin 4) (k : ℕ) :
    memoryState frontier (packed mode k) = state mode := by
  simp [memoryState, packed, frontier, state]

private theorem mem_fits (mode : Fin 4) (a : ℕ) : Fits 4 (mem mode a) := by
  by_cases h100 : a = 100
  · subst a
    change Fits 4 7
    decide
  · by_cases ha : a ≤ 12
    · interval_cases a <;> fin_cases mode <;> decide +kernel
    · have hz : mem mode a = 0 := by
        simp [mem, h100, show a ≠ 0 by omega, show a ≠ 1 by omega,
          show a ≠ 2 by omega, show a ≠ 3 by omega, show a ≠ 6 by omega,
          show a ≠ 7 by omega, show a ≠ 8 by omega, show a ≠ 10 by omega,
          show a ≠ 11 by omega, show a ≠ 12 by omega]
      rw [hz]
      exact fits_zero 4

private theorem packed_bounded (mode : Fin 4) (k : ℕ) (hk : Fits 4 k) :
    (packed mode k).Bounded 4 := by
  refine ⟨?_, mem_fits mode⟩
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [packed, Fin.lastCases_last]
    decide
  · simp only [packed, Fin.lastCases_castSucc]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · fin_cases j
      · change Fits 4 4; decide
      · change Fits 4 0; decide
      · change Fits 4 1; decide
      · change Fits 4 1; decide
      · change Fits 4 (size mode)
        fin_cases mode <;> decide
      · exact hk
    · simp only [Fin.append_right]
      exact fits_zero 4

private theorem native_run (mode : Fin 4) (hm : mode ≠ 3) :
    ∃ y, ExecWithin 4 (realizes_siftDown.code frontier src tmp) (packed mode 1) y
        (10 * realizes_siftDown.factor * (Nat.log 2 4 + 1)) ∧
      memoryState frontier y =
        (Memory.spec 4).clientState (state mode)
          (BinaryHeap.Memory.siftDown layout (size mode) 1) := by
  have hA : layout.arrays.Allocated (memoryState frontier (packed mode 1)) := by
    rw [packed_state]
    change 1 + (3 * 4 + 1) ≤ 14
    decide
  have hsz : 1 ≤ size mode := by unfold size; split_ifs <;> omega
  obtain ⟨y, hy, hs, _, _, _⟩ := exec_siftDown frontier src tmp tmp_injective src_tmp
    tmp_frontier src_frontier layout (packed mode 1) (packed_bounded mode 1 (by decide))
    (packed_input mode 1) hA le_rfl hsz (shape mode) (down_ordered mode)
  exact ⟨y, hy, by simpa only [packed_state] using hs⟩

-- Same emitted body, only a left child: swap, exact inverse positions, dirty frame retained.
example : ∃ y, ExecWithin 4 (realizes_siftDown.code frontier src tmp) (packed 0 1) y
      (10 * realizes_siftDown.factor * (Nat.log 2 4 + 1)) ∧
    y.mem 6 = 1 ∧ y.mem 7 = 0 ∧ y.mem 10 = 2 ∧ y.mem 11 = 1 ∧ y.mem 100 = 7 := by
  obtain ⟨y, hy, hs⟩ := native_run 0 (by decide)
  refine ⟨y, hy, ?_⟩
  have hmem := congrArg Memory.State.mem hs
  change y.mem = _ at hmem
  rw [hmem]
  decide +kernel

-- Same body, actual reads followed by a no-swap early exit; root/children and dirty cell retained.
example : ∃ y, ExecWithin 4 (realizes_siftDown.code frontier src tmp) (packed 1 1) y
      (10 * realizes_siftDown.factor * (Nat.log 2 4 + 1)) ∧
    y.mem 6 = 0 ∧ y.mem 7 = 1 ∧ y.mem 8 = 2 ∧ y.mem 100 = 7 := by
  obtain ⟨y, hy, hs⟩ := native_run 1 (by decide)
  refine ⟨y, hy, ?_⟩
  have hmem := congrArg Memory.State.mem hs
  change y.mem = _ at hmem
  rw [hmem]
  decide +kernel

-- Equal keys: right handle0 outranks left handle1, and both outrank root handle2.
example : ∃ y, ExecWithin 4 (realizes_siftDown.code frontier src tmp) (packed 2 1) y
      (10 * realizes_siftDown.factor * (Nat.log 2 4 + 1)) ∧
    y.mem 6 = 0 ∧ y.mem 8 = 2 ∧ y.mem 10 = 1 ∧ y.mem 12 = 3 ∧ y.mem 100 = 7 := by
  obtain ⟨y, hy, hs⟩ := native_run 2 (by decide)
  refine ⟨y, hy, ?_⟩
  have hmem := congrArg Memory.State.mem hs
  change y.mem = _ at hmem
  rw [hmem]
  decide +kernel

/-- Empty index at width one: literal `2` does not fit, so actual exit before division matters. -/
private def smallArgument : Argument := ((⟨0, ⟨⟨0, 1⟩, 0⟩⟩, 0), 0)

private def smallData : Data regs :=
  ⟨Fin.lastCases 1 (Fin.append (inputWords smallArgument) (fun _ => 0)), fun _ => 1⟩

example : ∃ y, ExecWithin 1 (realizes_siftDown.code frontier src tmp) smallData y
    realizes_siftDown.factor ∧ y.mem = smallData.mem ∧ ¬Fits 1 2 := by
  have hin : smallData.regs ∘ src = inputWords smallArgument := by
    funext i
    simp only [Function.comp_apply, smallData, src, Fin.lastCases_castSucc, Fin.append_left]
  have hs : memoryState frontier smallData = ⟨fun _ => 1, 1⟩ := by
    apply Memory.State.ext
    · rfl
    · simp [memoryState, smallData, frontier]
  have hb : smallData.Bounded 1 := by
    refine ⟨?_, fun _ => by change Fits 1 1; decide⟩
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [smallData, Fin.lastCases_last]
      decide
    · simp only [smallData, Fin.lastCases_castSucc]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        fin_cases j <;> decide +kernel
      · simp only [Fin.append_right]
        exact fits_zero 1
  have hsafe : Safe 1 smallArgument (memoryState frontier smallData) := by
    rw [hs]
    refine ⟨by decide, ?_, ?_, by decide⟩
    · change 0 + (3 * 0 + 1) ≤ 1
      decide
    · change HeapShape 0 0 0 (fun _ => 1)
      refine ⟨le_rfl, ?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  have hp : BinaryHeap.Memory.siftDown smallArgument.1.1.2
      smallArgument.1.2 smallArgument.2 = pure () := by
    rw [BinaryHeap.Memory.siftDown]
    simp [smallArgument]
  have hv : (Memory.spec 1).ValidHistory (memoryState frontier smallData)
      ((Memory.spec 1).clientHistory (memoryState frontier smallData)
        (BinaryHeap.Memory.siftDown smallArgument.1.1.2 smallArgument.1.2 smallArgument.2)) := by
    rw [hp]
    trivial
  obtain ⟨y, hy, hm, _, _⟩ :=
    (realizes_siftDown.code_spec frontier src tmp tmp_injective src_tmp tmp_frontier
      src_frontier).2 1 smallArgument smallData hb hin hsafe hv
  refine ⟨y, ?_, ?_, by decide⟩
  · have hc : memoryCost (BinaryHeap.Memory.siftDown smallArgument.1.1.2
        smallArgument.1.2 smallArgument.2) (memoryState frontier smallData) = 0 := by
      rw [hp]
      rfl
    simpa only [hc, Nat.zero_add, Nat.mul_one] using hy
  · rw [hp] at hm
    exact congrArg Memory.State.mem hm

end

end ComplexityTests.WordRAMBinaryHeapSiftDown
