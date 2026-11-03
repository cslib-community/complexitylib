/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.SiftUp
import Mathlib.Tactic.IntervalCases

/-! A real two-level sift at maximum fitting key 15, a no-swap/root exit, and a key-tie swap.
The native emitter is selected globally before all these installed-argument memory fixtures.
No native instruction or algorithm-specific register-frame proof is supplied by the tests. -/

namespace ComplexityTests.WordRAMBinaryHeapSiftUp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.SiftUp
open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap

private def layout : BinaryHeap.Memory.Layout 4 := ⟨⟨0, 1⟩, 1⟩

-- The typed handle uses its actual word, without a successor sentinel or extra fit premise.
example : handleWords ⟨4, layout, 3⟩ = ![4, 0, 1, 1, 3] := by
  funext i
  fin_cases i <;> rfl

private def mem (low : Bool) (a : ℕ) : ℕ :=
  if a = 100 then 7
  else if a = 0 ∨ a = 13 then 4
  else if 1 ≤ a ∧ a ≤ 3 then 15
  else if a = 4 then if low then 0 else 15
  else if a = 7 ∨ a = 10 then 1
  else if a = 8 ∨ a = 11 then 2
  else if a = 9 ∨ a = 12 then 3
  else 0

private def state (low : Bool) : Memory.State := ⟨mem low, 14⟩

private theorem shape (low : Bool) : HeapShape 4 layout.base 4 (mem low) := by
  refine ⟨by decide +kernel, ?_, ?_, ?_, ?_⟩
  · intro i hi hs
    interval_cases i <;> norm_num [layout, mem]
  · intro i hi hs
    interval_cases i <;> norm_num [layout, mem]
  · intro v hv
    interval_cases v <;> norm_num [layout, mem]
  · intro v hv hp
    interval_cases v <;> norm_num [layout, mem]

private theorem ordered_up (low : Bool) : UpOrdered (heapEntry 4 layout.base (mem low)) 4 4 := by
  intro i hi hs
  interval_cases i <;> norm_num [heapEntry, layout, mem, IndexedMinPQ.RawPrioLE]

private theorem ordered_root : UpOrdered (heapEntry 4 layout.base (mem false)) 4 1 := by
  intro i hi hs
  interval_cases i <;> norm_num [heapEntry, layout, mem, IndexedMinPQ.RawPrioLE]

-- Exact source history/cost, including the two swaps and the initially-false guard.
example : memoryCost (BinaryHeap.Memory.siftUp layout 4) (state true) = 16 := by decide +kernel
example : localWork (⟨4, layout⟩, 4) (state true) = 4 := by decide +kernel
example : memoryCost (BinaryHeap.Memory.siftUp layout 1) (state false) = 0 := by decide +kernel
example : localWork (⟨4, layout⟩, 1) (state false) = 2 := by decide +kernel
example : memoryCost (BinaryHeap.Memory.siftUp layout 4) (state false) = 4 := by decide +kernel

-- A zero cutoff would truncate the genuinely active guard; it is excluded by the while domain.
example : ¬whileSafe guard step (fun _ _ _ => True) 4 (⟨4, layout⟩, ()) 0 4 (state true) := by
  simp only [whileSafe]
  change ¬¬(2 ≤ 4)
  omega

private def tieMem : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (mem true) 6 3) 9 0) 10 4)
    13 1

private theorem tie_shape : HeapShape 4 layout.base 4 tieMem := by
  refine ⟨by decide +kernel, ?_, ?_, ?_, ?_⟩
  · intro i hi hs
    interval_cases i <;> norm_num [layout, tieMem, mem]
  · intro i hi hs
    interval_cases i <;> norm_num [layout, tieMem, mem]
  · intro v hv
    interval_cases v <;> norm_num [layout, tieMem, mem]
  · intro v hv hp
    interval_cases v <;> norm_num [layout, tieMem, mem]

private theorem tie_ordered : UpOrdered (heapEntry 4 layout.base tieMem) 4 4 := by
  intro i hi hs
  interval_cases i <;> norm_num [heapEntry, layout, tieMem, mem, IndexedMinPQ.RawPrioLE]

-- Equal keys: handle 0 rises above handle 1, then stops below the strictly smaller root key.
example : memoryCost (BinaryHeap.Memory.siftUp layout 4) ⟨tieMem, 14⟩ = 12 := by decide +kernel
example : ((Memory.spec 4).clientState ⟨tieMem, 14⟩
    (BinaryHeap.Memory.siftUp layout 4)).mem 7 = 0 := by decide +kernel

noncomputable section

private abbrev bankSize := 0 + realizes_siftUp.scratchSize + 1
private abbrev regs := 5 + bankSize + 1
private def frontier : Fin regs := Fin.last (5 + bankSize)
private def src (i : Fin 5) : Fin regs := (Fin.castAdd bankSize i).castSucc
private def tmp (i : Fin bankSize) : Fin regs := (Fin.natAdd 5 i).castSucc

private def packed (s : Memory.State) (k : ℕ) : Data regs :=
  ⟨Fin.lastCases s.frontier (Fin.append (indexWords (⟨4, layout⟩, k)) (fun _ => 0)), s.mem⟩

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

private theorem packed_input (s : Memory.State) (k : ℕ) :
    (packed s k).regs ∘ src = indexWords (⟨4, layout⟩, k) := by
  funext i
  simp [packed, src]

private theorem packed_state (s : Memory.State) (k : ℕ) :
    memoryState frontier (packed s k) = s := by
  cases s
  simp [memoryState, packed, frontier]

private theorem packed_bounded (s : Memory.State) (k : ℕ)
    (hm : ∀ a, Fits 4 (s.mem a)) (hf : Fits 4 s.frontier) (hk : Fits 4 k) :
    (packed s k).Bounded 4 := by
  refine ⟨?_, hm⟩
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa [packed] using hf
  · simp only [packed, Fin.lastCases_castSucc]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      fin_cases j
      · change Fits 4 4; decide
      · change Fits 4 0; decide
      · change Fits 4 1; decide
      · change Fits 4 1; decide
      · exact hk
    · simp only [Fin.append_right]
      exact fits_zero 4

private theorem mem_fits (low : Bool) (a : ℕ) : Fits 4 (mem low a) := by
  unfold mem
  split_ifs <;> decide

private theorem native_run (s : Memory.State) (k : ℕ) (hf : s.frontier = 14)
    (hm : ∀ a, Fits 4 (s.mem a)) (hk : 1 ≤ k) (hk4 : k ≤ 4)
    (hshape : HeapShape 4 layout.base 4 s.mem)
    (hord : UpOrdered (heapEntry 4 layout.base s.mem) 4 k) :
    ∃ y, ExecWithin 4 (realizes_siftUp.code frontier src tmp) (packed s k) y
        (9 * realizes_siftUp.factor * (Nat.log 2 4 + 1)) ∧
      memoryState frontier y =
        (Memory.spec 4).clientState s (BinaryHeap.Memory.siftUp layout k) := by
  have hb := packed_bounded s k hm (hf ▸ by decide +kernel)
    ((show Fits 4 4 by decide +kernel).of_le hk4)
  have hA : layout.arrays.Allocated (memoryState frontier (packed s k)) := by
    rw [packed_state]
    change 1 + (3 * 4 + 1) ≤ s.frontier
    omega
  obtain ⟨y, hy, hstate, _, _, _⟩ := exec_siftUp frontier src tmp tmp_injective src_tmp
    tmp_frontier src_frontier layout (packed s k) hb (packed_input _ _) hA hk hk4 hshape hord
  exact ⟨y, hy, by simpa only [packed_state] using hstate⟩

/-- The same selected native body executes an actual two-swap sift and preserves a dirty cell
outside the heap, with the full source state and caller frame provided by the shared kernel. -/
example : ∃ y, ExecWithin 4 (realizes_siftUp.code frontier src tmp) (packed (state true) 4) y
      (9 * realizes_siftUp.factor * (Nat.log 2 4 + 1)) ∧
    y.mem 6 = 3 ∧ y.mem 7 = 0 ∧ y.mem 9 = 1 ∧ y.mem 100 = 7 ∧
    y.regs frontier = 14 := by
  have hb := packed_bounded (state true) 4 (mem_fits true) (by decide +kernel) (by decide +kernel)
  have hA : layout.arrays.Allocated (memoryState frontier (packed (state true) 4)) := by
    rw [packed_state]
    change 1 + (3 * 4 + 1) ≤ 14
    decide
  obtain ⟨y, hy, hm, _, _, _⟩ := exec_siftUp frontier src tmp tmp_injective src_tmp tmp_frontier
    src_frontier layout (packed (state true) 4) hb (packed_input _ _) hA (by decide +kernel)
    (by decide +kernel)
    (shape true) (ordered_up true)
  refine ⟨y, hy, ?_⟩
  have hm' := congrArg Memory.State.mem hm
  have hf' := congrArg Memory.State.frontier hm
  rw [packed_state] at hm' hf'
  change y.mem = _ at hm'
  change y.regs frontier = _ at hf'
  rw [hm', hf']
  decide +kernel

-- Same emitter, initially false guard: no read or swap and literal whole memory unchanged.
example : ∃ y, ExecWithin 4 (realizes_siftUp.code frontier src tmp) (packed (state false) 1) y
      (9 * realizes_siftUp.factor * (Nat.log 2 4 + 1)) ∧ y.mem = mem false := by
  obtain ⟨y, hy, hm⟩ := native_run (state false) 1 rfl (mem_fits false)
    (by decide +kernel) (by decide +kernel) (shape false) ordered_root
  refine ⟨y, hy, ?_⟩
  have hmem := congrArg Memory.State.mem hm
  change y.mem = ((Memory.spec 4).clientState (state false)
    (BinaryHeap.Memory.siftUp layout 1)).mem at hmem
  simpa [BinaryHeap.Memory.siftUp, StateTransitionSpec.clientState, state] using hmem

private theorem tie_fits (a : ℕ) : Fits 4 (tieMem a) := by
  simp only [tieMem, Function.update_apply]
  split_ifs <;> first | exact mem_fits true a | decide

-- Same emitter, a key-tie swap followed by a real no-swap early exit.
example : ∃ y, ExecWithin 4 (realizes_siftUp.code frontier src tmp) (packed ⟨tieMem, 14⟩ 4) y
      (9 * realizes_siftUp.factor * (Nat.log 2 4 + 1)) ∧
    y.mem 6 = 3 ∧ y.mem 7 = 0 ∧ y.mem 9 = 1 ∧ y.mem 100 = 7 := by
  obtain ⟨y, hy, hm⟩ := native_run ⟨tieMem, 14⟩ 4 rfl tie_fits
    (by decide +kernel) (by decide +kernel) tie_shape tie_ordered
  refine ⟨y, hy, ?_⟩
  have hmem := congrArg Memory.State.mem hm
  change y.mem = _ at hmem
  rw [hmem]
  decide +kernel

-- The caller's physical width is a real condition, not an invisible fit assumption.
example : ¬(packed (state true) 4).Bounded 3 := by
  intro h
  have hf := h.1 frontier
  norm_num [packed, frontier, Fits, state] at hf

end

end ComplexityTests.WordRAMBinaryHeapSiftUp
