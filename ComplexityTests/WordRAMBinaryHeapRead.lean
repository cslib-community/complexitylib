/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Read
import Complexity.Computability.WordRAM.Realization.Witness

/-! The same read-method witnesses handle present and absent handles, Boolean emptiness and a
maximum fitting key. The generic packing below only supplies the kernel's static register ABI;
no algorithm-specific instruction execution or register-frame proof is used. -/

namespace ComplexityTests.WordRAMBinaryHeapRead

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

noncomputable section

variable {δ α : Type} {k : ℕ} {p : δ → Memory.Prog α}
  {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin 2 → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

private abbrev bankSize (h : Realizes .exact p input output safe work) := 2 + h.scratchSize + 1
private abbrev regs (h : Realizes .exact p input output safe work) := k + bankSize h + 1
private def frontier (h : Realizes .exact p input output safe work) : Fin (regs h) :=
  Fin.last (k + bankSize h)
private def src (h : Realizes .exact p input output safe work) (i : Fin k) : Fin (regs h) :=
  (Fin.castAdd (bankSize h) i).castSucc
private def tmp (h : Realizes .exact p input output safe work) (i : Fin (bankSize h)) :
    Fin (regs h) := (Fin.natAdd k i).castSucc
private def packed (h : Realizes .exact p input output safe work) (d : δ) (s : Memory.State) :
    Data (regs h) :=
  ⟨Fin.lastCases s.frontier (Fin.append (input d) (fun _ => 0)), s.mem⟩

private theorem packed_state (h : Realizes .exact p input output safe work) (d : δ)
    (s : Memory.State) : memoryState (frontier h) (packed h d s) = s := by
  cases s
  simp [memoryState, frontier, packed]

private theorem native (h : Realizes .exact p input output safe work) (w : ℕ) (d : δ)
    (s : Memory.State) (hw : ∀ i, Fits w (input d i)) (hm : Memory.WellFormed w s)
    (hs : safe w d s)
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d))) :
    ∃ y, ExecWithin w (h.code (frontier h) (src h) (tmp h)) (packed h d s) y
        (h.factor * (memoryCost (p d) s + work d s + 1)) ∧
      memoryState (frontier h) y = (Memory.spec w).clientState s (p d) ∧
      ∀ i : Fin 2, y.regs (tmp h (Fin.castAdd (h.scratchSize + 1) i)) =
        output ((Memory.spec w).clientResult s (p d)) i := by
  have hi : Function.Injective (tmp h) := by
    intro i j he
    apply Fin.ext
    have hh := congrArg Fin.val he
    simpa [tmp] using hh
  have hd : ∀ i j, src h i ≠ tmp h j := by
    intro i j he
    have hh := congrArg Fin.val he
    dsimp only [src, tmp, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd] at hh
    omega
  have hf : ∀ j, tmp h j ≠ frontier h := by
    intro j he
    have hh := congrArg Fin.val he
    dsimp only [tmp, frontier, Fin.val_castSucc, Fin.val_natAdd, Fin.val_last] at hh
    omega
  have hsrc : ∀ i, src h i ≠ frontier h := by
    intro i he
    have hh := congrArg Fin.val he
    dsimp only [src, frontier, Fin.val_castSucc, Fin.val_castAdd, Fin.val_last] at hh
    omega
  have hx : (packed h d s).Bounded w := by
    refine ⟨?_, hm.mem_fits⟩
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa [packed] using hm.frontier_fits
    · simp only [packed, Fin.lastCases_castSucc]
      exact Fin.addCases (fun j => by simpa using hw j)
        (fun _ => by simp) i
  have hin : (packed h d s).regs ∘ src h = input d := by
    funext i
    simp [packed, src]
  obtain ⟨y, hy, hm, ho, _⟩ := (h.code_spec (frontier h) (src h) (tmp h) hi hd hf hsrc).2
    w d (packed h d s) hx hin (by simpa only [packed_state] using hs)
    (by simpa only [packed_state] using hv)
  exact ⟨y, by simpa only [packed_state] using hy,
    by simpa only [packed_state] using hm, by simpa only [packed_state] using ho⟩

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
