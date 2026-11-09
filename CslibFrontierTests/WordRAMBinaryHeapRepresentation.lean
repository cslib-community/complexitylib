/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Representation

/-! The same global initializer produces the raw Backend representation at both compact
width boundaries. Cells outside its 3n+1 block may be dirty and may subsequently change; the
persistent layout words are necessary even when all memory is unchanged. -/

namespace CslibFrontierTests.WordRAMBinaryHeapRepresentation

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Representation
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

noncomputable section

private def initial (n base : ℕ) (mem : ℕ → ℕ) : Data Program.registers :=
  ⟨fun i => if i = Program.code.frontierReg then base else
    if i = Program.code.nReg then n else 0, mem⟩

private theorem initial_bounded {w n base : ℕ} (mem : ℕ → ℕ)
    (hn : Fits w n) (hb : Fits w base) (hm : ∀ a, Fits w (mem a)) :
    (initial n base mem).Bounded w := by
  refine ⟨fun i => ?_, hm⟩
  dsimp only [initial]
  split_ifs
  · exact hb
  · exact hn
  · exact fits_zero _

private theorem initial_frontier (n base : ℕ) (mem : ℕ → ℕ) :
    (initial n base mem).regs Program.code.frontierReg = base := by
  simp only [initial, ite_true]

private theorem initial_n (n base : ℕ) (mem : ℕ → ℕ) :
    (initial n base mem).regs Program.code.nReg = n := by
  simp only [initial, ite_eq_right Program.code.nReg_ne_frontier, ite_true]

private theorem native {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    (mem : ℕ → ℕ) (hb : Fits w base) (hm : ∀ a, Fits w (mem a))
    (hfit : Fits w (base + space n))
    (hz : ∀ a, (Block.mk base (space n)).Owns a → mem a = 0) :
    ∃ y, ExecWithin w Program.code.initFresh (initial n base mem) y
        (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
      y.mem = mem ∧ y.regs Program.code.frontierReg = base + space n ∧
      Rep base hn hK (IndexedMinPQ.empty n) y :=
  initFresh_rep hn hK (initial n base mem) (initial_bounded mem hn hb hm)
    (initial_frontier n base mem) (initial_n n base mem) hfit hz

private def oneOutside (a : ℕ) : ℕ := if a = 100 then 1 else 0

-- No gratuitous literal3 requirement: the zero-handle compact heap still works at one bit.
example : Fits 1 (space 0) ∧ ¬Fits 1 3 := by decide

example : ∃ y, ExecWithin 1 Program.code.initFresh (initial 0 0 oneOutside) y
      (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
    y.mem = oneOutside ∧ y.regs Program.code.frontierReg = 1 ∧
    Rep 0 (show Fits 1 0 by decide) (show Fits 1 0 by decide) (IndexedMinPQ.empty 0) y := by
  apply native (n := 0) (base := 0) (by decide) (by decide) oneOutside (by decide)
  · intro a
    unfold oneOutside
    split <;> decide
  · decide
  · intro a ha
    have ha0 : a = 0 := by dsimp only [Block.Owns, space] at ha; omega
    subst a
    rfl

private def dirtyOutside (a : ℕ) : ℕ := if a = 0 ∨ a = 100 then 7 else 0

private theorem dirty_bounded (a : ℕ) : Fits 3 (dirtyOutside a) := by
  unfold dirtyOutside
  split <;> decide

private theorem dirty_local_zero (a : ℕ) (ha : (Block.mk 3 (space 1)).Owns a) :
    dirtyOutside a = 0 := by
  dsimp only [Block.Owns, space] at ha
  unfold dirtyOutside
  split <;> omega

-- Same global code, nonzero frontier/end7, maximal fitting key bound and dirty outside cells.
example : ∃ y, ExecWithin 3 Program.code.initFresh (initial 1 3 dirtyOutside) y
      (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
    y.mem = dirtyOutside ∧ y.regs Program.code.frontierReg = 7 ∧
    Rep 3 (show Fits 3 1 by decide) (show Fits 3 7 by decide) (IndexedMinPQ.empty 1) y :=
  native (by decide) (by decide) dirtyOutside (by decide) dirty_bounded (by decide)
    dirty_local_zero

-- Local zero does not imply a global-zero allocation convention.
example : ¬Memory.ZeroAbove ⟨dirtyOutside, 3⟩ := by
  intro hz
  have h := hz 100 (by decide)
  norm_num [dirtyOutside] at h

-- A real initialized represented heap survives a change of an inaccessible outside cell.
example : ∃ y, Rep 3 (show Fits 3 1 by decide) (show Fits 3 7 by decide)
      (IndexedMinPQ.empty 1) y ∧ y.mem 100 = 7 ∧
    Rep 3 (show Fits 3 1 by decide) (show Fits 3 7 by decide) (IndexedMinPQ.empty 1)
      (⟨y.regs, Function.update y.mem 100 0⟩ : Data Program.registers) := by
  obtain ⟨y, _, hmem, _, hr⟩ := native (n := 1) (K := 7) (base := 3)
    (by decide) (by decide) dirtyOutside (by decide) dirty_bounded (by decide) dirty_local_zero
  refine ⟨y, hr, ?_, Rep.supported (x := y) (fun _ _ => rfl) ?_ ?_ hr⟩
  · rw [hmem]
    rfl
  · intro a ha
    have hne : a ≠ 100 := by
      rw [Block.mem_footprint] at ha
      dsimp only [Block.Owns, space] at ha
      omega
    exact Function.update_of_ne hne _ _
  · refine ⟨hr.bounded.1, fun a => ?_⟩
    change Fits 3 (Function.update y.mem 100 0 a)
    by_cases ha : a = 100
    · subst a
      simp only [Function.update_self]
      exact fits_zero _
    · rw [Function.update_of_ne ha]
      exact hr.bounded.2 a

-- Memory equality alone cannot replace the required persistent dimension word.
example (y : Data Program.registers) :
    ¬Rep 3 (show Fits 3 1 by decide) (show Fits 3 7 by decide) (IndexedMinPQ.empty 1)
      (⟨Function.update y.regs (Program.argument 0) 0, y.mem⟩ : Data Program.registers) := by
  intro hr
  have h := hr.2 0
  change Function.update y.regs (Program.argument 0) 0 (Program.argument 0) = 1 at h
  simp only [Function.update_self] at h
  contradiction

end

end CslibFrontierTests.WordRAMBinaryHeapRepresentation
