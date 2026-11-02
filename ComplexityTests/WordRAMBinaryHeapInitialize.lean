/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Initialize

/-! The same two global primitive witnesses work at both old-width boundaries. Reservation
actually preserves dirty outside memory; local zero then supplies the existing compact Inv.
The metadata primitive really computes its result and frames both original input words. -/

namespace ComplexityTests.WordRAMBinaryHeapInitialize

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.WordRAM.BinaryHeap (space)
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Initialize

noncomputable section

private abbrev reserveSlots := 1 + realizes_reserve.scratchSize + 1
private abbrev metadataSlots := 3 + realizes_metadata.scratchSize + 1
private abbrev bank := max reserveSlots metadataSlots
private abbrev regs := 2 + bank + 1

private def frontier : Fin regs := ⟨2 + bank, by unfold regs; omega⟩

private def inputs {k : ℕ} (hk : k ≤ 2) (i : Fin k) : Fin regs :=
  ⟨i.val, by have := i.isLt; unfold regs; omega⟩

private def scratch {k : ℕ} (hk : k ≤ bank) (i : Fin k) : Fin regs :=
  ⟨2 + i.val, by have := i.isLt; unfold regs; omega⟩

private abbrev srcR := inputs (show 1 ≤ 2 by decide)
private abbrev srcM := inputs (show 2 ≤ 2 from le_rfl)
private abbrev tmpR := scratch (Nat.le_max_left reserveSlots metadataSlots)
private abbrev tmpM := scratch (Nat.le_max_right reserveSlots metadataSlots)

private theorem scratch_injective {k : ℕ} (hk : k ≤ bank) :
    Function.Injective (scratch hk) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [scratch] at this
  omega

private theorem inputs_scratch {k l : ℕ} (hk : k ≤ 2) (hl : l ≤ bank) :
    ∀ i j, inputs hk i ≠ scratch hl j := by
  intro i j h
  have := congrArg Fin.val h
  simp only [inputs, scratch] at this
  have := i.isLt
  omega

private theorem scratch_frontier {k : ℕ} (hk : k ≤ bank) :
    ∀ j, scratch hk j ≠ frontier := by
  intro j h
  have := congrArg Fin.val h
  simp only [scratch, frontier] at this
  have := j.isLt
  omega

private theorem inputs_frontier {k : ℕ} (hk : k ≤ 2) : ∀ i, inputs hk i ≠ frontier := by
  intro i h
  have := congrArg Fin.val h
  simp only [inputs, frontier] at this
  have := i.isLt
  omega

private def packed (n base : ℕ) (mem : ℕ → ℕ) : Data regs where
  regs i := if i.val = 0 then n else if i.val = 1 then base
    else if i = frontier then base else 1
  mem := mem

private theorem packed_bounded {w n base : ℕ} (mem : ℕ → ℕ)
    (h1 : Fits w 1) (hn : Fits w n) (hb : Fits w base) (hm : ∀ a, Fits w (mem a)) :
    (packed n base mem).Bounded w := by
  refine ⟨fun i => ?_, hm⟩
  simp only [packed]
  split_ifs <;> assumption

private theorem packed_frontier (n base : ℕ) (mem : ℕ → ℕ) :
    (packed n base mem).regs frontier = base := by
  simp [packed, frontier]

private theorem packed_reserve_input (n base : ℕ) (mem : ℕ → ℕ) :
    (packed n base mem).regs ∘ srcR = WordEncoding.encode (α := ℕ) n := by
  funext i
  fin_cases i
  rfl

private theorem packed_metadata_input (n base : ℕ) (mem : ℕ → ℕ) :
    (packed n base mem).regs ∘ srcM = WordEncoding.encode (α := ℕ × ℕ) (n, base) := by
  funext i
  fin_cases i <;> rfl

/-- One fixed witness reserves the old span, then the same compact source invariant applies. -/
private theorem reservation {w n base : ℕ} (mem : ℕ → ℕ)
    (h1 : Fits w 1) (hn : Fits w n) (hb : Fits w base) (hm : ∀ a, Fits w (mem a))
    (hfit : Fits w (base + space n))
    (hz : ∀ a, (Block.mk base (space n)).Owns a → mem a = 0) :
    ∃ y, ExecWithin w (realizes_reserve.code frontier srcR tmpR) (packed n base mem) y
        (2 * realizes_reserve.factor) ∧ y.mem = mem ∧ y.regs frontier = base + space n ∧
      y.regs (tmpR (Fin.castAdd (realizes_reserve.scratchSize + 1) 0)) = base ∧
      BinaryHeap.Memory.Inv (BinaryHeap.Memory.compactLayout n base) (memoryState frontier y) ∧
      BinaryHeap.Memory.abs (BinaryHeap.Memory.compactLayout n base) (memoryState frontier y) =
        IndexedMinPQ.empty n := by
  have hfit' : Fits w ((packed n base mem).regs frontier + space n) := by
    simpa only [packed_frontier] using hfit
  obtain ⟨y, hy, _, hym, hyfr, hout, _⟩ := reserve_exec frontier srcR tmpR
    (scratch_injective _) (inputs_scratch _ _) (scratch_frontier _) (inputs_frontier _)
    (packed n base mem) (packed_bounded mem h1 hn hb hm) (packed_reserve_input n base mem) hfit'
  have hz' : ∀ a, (Block.mk ((packed n base mem).regs frontier) (space n)).Owns a →
      (packed n base mem).mem a = 0 := by
    intro a ha
    change mem a = 0
    exact hz a (by simpa only [packed_frontier] using ha)
  obtain ⟨hinv, habs⟩ := reserve_empty frontier hym hyfr hz'
  rw [packed_frontier] at hyfr hout hinv habs
  exact ⟨y, hy, hym, hyfr, hout, hinv, habs⟩

private theorem metadata {w n base : ℕ} (mem : ℕ → ℕ)
    (h1 : Fits w 1) (hn : Fits w n) (hb : Fits w base) (hm : ∀ a, Fits w (mem a))
    (hfit : Fits w (base + space n)) :
    ∃ y, ExecWithin w (realizes_metadata.code frontier srcM tmpM) (packed n base mem) y
        realizes_metadata.factor ∧ y.mem = mem ∧ y.regs frontier = base ∧
      (∀ i : Fin 3, y.regs (tmpM (Fin.castAdd (realizes_metadata.scratchSize + 1) i)) =
        ![n, base + n, 1] i) ∧ y.regs (srcM 0) = n ∧ y.regs (srcM 1) = base := by
  obtain ⟨y, hy, _, hstate, hout, hinput, _⟩ := metadata_exec frontier srcM tmpM
    (scratch_injective _) (inputs_scratch _ _) (scratch_frontier _) (inputs_frontier _)
    (n, base) (packed n base mem) (packed_bounded mem h1 hn hb hm)
    (packed_metadata_input n base mem) hfit
  have hmem := congrArg Memory.State.mem hstate
  have hfr := congrArg Memory.State.frontier hstate
  refine ⟨y, hy, hmem, ?_, hout, congrFun hinput 0, congrFun hinput 1⟩
  simpa only [memoryState, packed_frontier] using hfr

private def zeroMem (a : ℕ) : ℕ := if a = 2 then 1 else 0

private theorem zero_fits (a : ℕ) : Fits 1 (zeroMem a) := by
  unfold zeroMem
  split <;> decide

private theorem zero_local (a : ℕ) (ha : (Block.mk 0 (space 0)).Owns a) : zeroMem a = 0 := by
  simp only [Block.Owns, space] at ha
  simp only [zeroMem]
  split <;> omega

-- No extra cell and no materialized constant3: the old one-bit boundary remains inhabited.
example : Fits 1 (space 0) ∧ ¬Fits 1 (1 + space 0) ∧ ¬Fits 1 3 := by decide

example : ∃ y, ExecWithin 1 (realizes_reserve.code frontier srcR tmpR) (packed 0 0 zeroMem) y
      (2 * realizes_reserve.factor) ∧ y.mem 2 = 1 ∧ y.regs frontier = 1 ∧
    BinaryHeap.Memory.Inv (BinaryHeap.Memory.compactLayout 0 0) (memoryState frontier y) := by
  obtain ⟨y, hy, hm, hf, _, hinv, _⟩ := reservation (n := 0) (base := 0) zeroMem
    (by decide) (by decide)
    (by decide) zero_fits (by decide) zero_local
  refine ⟨y, hy, ?_, hf, hinv⟩
  rw [hm]
  rfl

example : ∃ y, ExecWithin 1 (realizes_metadata.code frontier srcM tmpM) (packed 0 0 zeroMem) y
      realizes_metadata.factor ∧ y.mem = zeroMem ∧
    (∀ i : Fin 3, y.regs (tmpM (Fin.castAdd (realizes_metadata.scratchSize + 1) i)) = ![0, 0, 1] i)
      ∧ y.regs (srcM 0) = 0 ∧ y.regs (srcM 1) = 0 := by
  obtain ⟨y, hy, hm, _, ho, hn, hb⟩ := metadata (n := 0) (base := 0) zeroMem (by decide) (by decide)
    (by decide) zero_fits (by decide)
  exact ⟨y, hy, hm, ho, hn, hb⟩

private def dirtyMem (a : ℕ) : ℕ := if a = 0 ∨ a = 100 then 7 else 0

private theorem dirty_fits (a : ℕ) : Fits 3 (dirtyMem a) := by
  unfold dirtyMem
  split <;> decide

private theorem dirty_local (a : ℕ) (ha : (Block.mk 3 (space 1)).Owns a) : dirtyMem a = 0 := by
  simp only [Block.Owns, space] at ha
  simp only [dirtyMem]
  split <;> omega

example : Fits 3 (3 + space 1) ∧ ¬Fits 3 (3 + 1 + space 1) := by decide

-- Same reservation code at a nonzero base, with dirty memory below and above the owned block.
example : ∃ y, ExecWithin 3 (realizes_reserve.code frontier srcR tmpR) (packed 1 3 dirtyMem) y
      (2 * realizes_reserve.factor) ∧ y.mem = dirtyMem ∧ y.regs frontier = 7 ∧
    y.regs (tmpR (Fin.castAdd (realizes_reserve.scratchSize + 1) 0)) = 3 ∧
    BinaryHeap.Memory.Inv (BinaryHeap.Memory.compactLayout 1 3) (memoryState frontier y) ∧
    ¬Memory.ZeroAbove (memoryState frontier y) := by
  obtain ⟨y, hy, hm, hf, ho, hi, _⟩ := reservation (n := 1) (base := 3) dirtyMem
    (by decide) (by decide)
    (by decide) dirty_fits (by decide) dirty_local
  refine ⟨y, hy, hm, hf, ho, hi, ?_⟩
  intro hz
  have hf7 : y.regs frontier = 7 := hf
  have h := hz 100 (by change y.regs frontier ≤ 100; omega)
  change y.mem 100 = 0 at h
  rw [hm] at h
  norm_num [dirtyMem] at h

example : ∃ y, ExecWithin 3 (realizes_metadata.code frontier srcM tmpM) (packed 1 3 dirtyMem) y
      realizes_metadata.factor ∧ y.mem = dirtyMem ∧
    (∀ i : Fin 3, y.regs (tmpM (Fin.castAdd (realizes_metadata.scratchSize + 1) i)) = ![1, 4, 1] i)
      ∧ y.regs (srcM 0) = 1 ∧ y.regs (srcM 1) = 3 := by
  obtain ⟨y, hy, hm, _, ho, hn, hb⟩ := metadata (n := 1) (base := 3) dirtyMem
    (by decide) (by decide)
    (by decide) dirty_fits (by decide)
  exact ⟨y, hy, hm, ho, hn, hb⟩

-- Dirty inside is NOT silently accepted: a stale position prevents the fresh empty invariant.
example : ¬BinaryHeap.Memory.Inv (BinaryHeap.Memory.compactLayout 1 3)
    ⟨Function.update dirtyMem 6 1, 7⟩ := by
  intro h
  have hp := h.heap.pos_le 0 (by decide)
  norm_num [BinaryHeap.Memory.compactLayout, dirtyMem] at hp

end

end ComplexityTests.WordRAMBinaryHeapInitialize
