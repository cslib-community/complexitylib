/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Base

/-! The existing SubroutineBase fresh/dirty initialization theorems on the global heap code.
The dirty control additionally checks every cleared cell, by determinism and the shared
zeroFillCode execution theorem followed by the existing memory-preserving setup. -/

namespace ComplexityTests.WordRAMBinaryHeapBase

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
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

private theorem initial_params (n base : ℕ) (mem : ℕ → ℕ) (i : Fin 1) :
    (initial n base mem).regs (Program.code.initParams i) = (![n] : Fin 1 → ℕ) i := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [Program.code.initParams_eq, Matrix.cons_val_zero,
    initial, ite_eq_right Program.code.nReg_ne_frontier, ite_true]

private def freshMem (a : ℕ) : ℕ := if a = 100 then 1 else 0

-- A local-zero one-cell block at n0/w1 still permits a dirty inaccessible outside cell.
example : ∃ y, ExecWithin 1 Program.code.initFresh (initial 0 0 freshMem) y
      (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
    y.regs Program.code.frontierReg = 1 ∧
    Representation.Rep 0 (show Fits 1 0 by decide) (show Fits 1 0 by decide)
      (IndexedMinPQ.empty 0) y ∧ y.mem 100 = 1 := by
  let C := subroutineBase (n := 0) (base := 0) (show Fits 1 (0 + space 0) by decide)
    (show Fits 1 0 by decide)
  have hx : (initial 0 0 freshMem).Bounded 1 := initial_bounded _
    (by decide) (by decide) (fun a => by unfold freshMem; split <;> decide)
  have hz : ∀ a ∈ (Block.mk 0 C.space).footprint, (initial 0 0 freshMem).mem a = 0 := by
    rw [subroutineBase_space]
    intro a ha
    rw [Block.mem_footprint] at ha
    have ha0 : a = 0 := by dsimp only [Block.Owns, space] at ha; omega
    subst a
    rfl
  obtain ⟨y, he, hf, hr, _, hmod⟩ := C.initFresh_exec hx
    (initial_frontier _ _ _) (initial_params _ _ _) hz
  have htime : C.initTime =
      2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor :=
    subroutineBase_initTime _ _
  have hspace : C.space = space 0 := subroutineBase_space _ _
  refine ⟨y, ?_, ?_, (subroutineBase_rep_iff _ _ _ _).mp hr, ?_⟩
  · rwa [htime] at he
  · rw [hspace] at hf
    norm_num [space] at hf
    exact hf
  · have hm := hmod 100 (by
      rw [subroutineBase_space, Block.mem_footprint]
      dsimp only [Block.Owns, space]
      omega)
    exact hm

private def dirtyMem (a : ℕ) : ℕ := if a = 0 then 5 else if a = 100 then 7 else 3

private theorem dirty_bounded (a : ℕ) : Fits 3 (dirtyMem a) := by
  unfold dirtyMem
  split_ifs <;> decide

-- Actual initClear, with a dirty original four-cell block and unchanged width/end7 domain.
example : ∃ y, ExecWithin 3 Program.code.initClear (initial 1 3 dirtyMem) y
      (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor +
        4 * space 1 + 6) ∧
    y.regs Program.code.frontierReg = 7 ∧
    Representation.Rep 3 (show Fits 3 1 by decide) (show Fits 3 7 by decide)
      (IndexedMinPQ.empty 1) y ∧
    (∀ a ∈ (Block.mk 3 (space 1)).footprint, y.mem a = 0) ∧
    y.mem 0 = 5 ∧ y.mem 100 = 7 := by
  let C := subroutineBase (n := 1) (base := 3) (show Fits 3 (3 + space 1) by decide)
    (show Fits 3 7 by decide)
  have hx := initial_bounded dirtyMem (show Fits 3 1 by decide)
    (show Fits 3 3 by decide) dirty_bounded
  obtain ⟨y, he, hf, hr, _, hmod⟩ := C.initClear_exec hx
    (initial_frontier _ _ _) (initial_params _ _ _)
  have htime : C.initTime =
      2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor :=
    subroutineBase_initTime _ _
  have hspace : C.space = space 1 := subroutineBase_space _ _
  have hesaved := he
  -- The generic theorem supplies the certified result. Its actual zeroed-cell postcondition
  -- follows from the same deterministic clear/setup execution, without stepping a heap method.
  obtain ⟨z, hspan, hbz, _, hbase, hfront, hnz⟩ := Program.span_exec (n := 1) (base := 3)
    (initial 1 3 dirtyMem) hx (initial_frontier _ _ _) (by
      simp only [initial, ite_eq_right Program.code.nReg_ne_frontier, ite_true]) (by decide)
  have hpar : ∀ i, z.regs (Program.code.initParams i) = (![1] : Fin 1 → ℕ) i := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [Program.code.initParams_eq, Matrix.cons_val_zero] using hnz
  obtain ⟨t, hclear, hbt, hbaset, _, hpart, hzero, _⟩ :=
    Program.code.toSubroutineCode.zeroFillCode_exec Program.clear_nodup
      Program.params_not_clear Program.incCur_eval hbz hbase hfront hpar
  have hnt : t.regs Program.code.nReg = 1 := by
    simpa only [Program.code.initParams_eq, Matrix.cons_val_zero] using hpart 0
  obtain ⟨u, hsetup, _, hmemu, _, _, _, _, _⟩ :=
    Program.setup_registers t hbt hnt hbaset (by decide)
  have hurun : ExecWithin 3 Program.code.initClear (initial 1 3 dirtyMem) u
      (2 * Initialize.realizes_reserve.factor + (4 * space 1 + 6 +
        Initialize.realizes_metadata.factor)) := hspan.seq (hclear.seq hsetup)
  obtain ⟨_, _, hey⟩ := he
  obtain ⟨_, _, heu⟩ := hurun
  have heq : y = u := (hey.unique heu).1
  have hz : ∀ a ∈ (Block.mk 3 (space 1)).footprint, y.mem a = 0 := by
    intro a ha
    rw [heq, hmemu]
    exact hzero a ha
  refine ⟨y, ?_, ?_, (subroutineBase_rep_iff _ _ _ _).mp hr, hz, ?_, ?_⟩
  · rwa [htime, hspace] at hesaved
  · rw [hspace] at hf
    norm_num [space] at hf
    exact hf
  · exact hmod 0 (by
      rw [subroutineBase_space, Block.mem_footprint]
      dsimp only [Block.Owns, space]
      omega)
  · exact hmod 100 (by
      rw [subroutineBase_space, Block.mem_footprint]
      dsimp only [Block.Owns, space]
      omega)

-- The dirt inside is real; a fresh/local-zero hypothesis would fail on this same input.
example : dirtyMem 3 ≠ 0 ∧ (Block.mk 3 (space 1)).Owns 3 := by
  norm_num [dirtyMem, Block.Owns, space]

end

end ComplexityTests.WordRAMBinaryHeapBase
