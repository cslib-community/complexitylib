/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Update
import CslibFrontierTests.WordRAMRealizationPacking
import Mathlib.Tactic.IntervalCases

/-! Native insertion and decrease-key at a genuine compact one-handle heap. Maximum-word keys,
the count/position writes and an inaccessible dirty cell are observed through the original source
programs. The tests use shared kernel packing, not hand-stepped algorithm instructions. -/

namespace CslibFrontierTests.WordRAMBinaryHeapUpdate

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open CslibFrontierTests.WordRAMRealizationPacking

private def layout : PriorityQueue.BinaryHeap.Memory.Layout 1 :=
  PriorityQueue.BinaryHeap.Memory.compactLayout 1 0

private def mem (a : ℕ) : ℕ := if a = 0 then 15 else if a = 100 then 7 else 0
private def initial : Memory.State := ⟨mem, 4⟩
private def argument : (HeapLayout × ℕ) × ℕ := ((⟨1, layout⟩, 0), 15)

private theorem valid : layout.Valid 4 15 :=
  PriorityQueue.BinaryHeap.Memory.valid_compactLayout (by decide +kernel) (by decide +kernel)

private theorem inv : PriorityQueue.BinaryHeap.Memory.Inv layout initial := by
  apply (PriorityQueue.BinaryHeap.Memory.inv_empty ?_ ?_ ?_ ?_).1
  · change 1 + 1 ≤ 4; decide
  · change 0 + (3 * 1 + 1) ≤ 4; decide
  · rfl
  · intro v hv
    interval_cases v
    rfl

private theorem admissible :
    IndexedMinPQ.valid 15 (PriorityQueue.BinaryHeap.Memory.abs layout initial) (.insert 0 15) :=
  ⟨rfl, le_rfl⟩

private theorem safe : insertSafe 4 argument initial :=
  ⟨by decide +kernel, 15, valid, inv, admissible⟩

private theorem wellFormed : Memory.WellFormed 4 initial := by
  refine ⟨by decide +kernel, fun a => ?_⟩
  change Fits 4 (mem a)
  unfold mem
  split_ifs <;> decide

-- The visible index-domain condition rules out an out-of-range runtime handle.
example : ¬insertSafe 4 ((⟨1, layout⟩, 1), 15) initial := by
  rintro ⟨h, _⟩
  change 1 < 1 at h
  omega

-- The same source heap cannot decrease an absent handle.
example : ¬decreaseSafe 4 ((⟨1, layout⟩, 0), 7) initial := by
  rintro ⟨hv, K, hL, hs, ⟨key, hk, hle⟩, hK⟩
  have hn : PriorityQueue.BinaryHeap.Memory.abs layout initial ⟨0, hv⟩ = none := rfl
  rw [hn] at hk
  contradiction

noncomputable section

/-- A real insert writes count and position, retains the maximum key and returns Unit without
losing whole-memory equality. This is the same global word-body witness for every runtime input. -/
example : ∃ y, ExecWithin 4 (realizes_insert.code (frontier realizes_insert)
      (src realizes_insert) (tmp realizes_insert)) (packed realizes_insert argument initial) y
      (6 * realizes_insert.factor) ∧
    y.mem 0 = 15 ∧ y.mem 1 = 1 ∧ y.mem 3 = 1 ∧ y.mem 100 = 7 ∧
    y.regs (frontier realizes_insert) = 4 := by
  have hw : ∀ i, Fits 4 (updateWords argument i) := by
    intro i
    fin_cases i <;> decide +kernel
  obtain ⟨hv, _, _⟩ := triple_iff.mp
    (PriorityQueue.BinaryHeap.Memory.insert_triple valid inv (v := 0) (k := 15) admissible)
  obtain ⟨y, hy, hm, _⟩ := native realizes_insert 4 argument initial hw wellFormed safe hv
  have hc : memoryCost (PriorityQueue.BinaryHeap.Memory.insert layout 0 15) initial = 5 := by
    decide +kernel
  refine ⟨y, hy.mono ?_, ?_⟩
  · change realizes_insert.factor *
      (memoryCost (PriorityQueue.BinaryHeap.Memory.insert layout 0 15) initial + 0 + 1) ≤ _
    rw [hc]
    omega
  · have hmem := congrArg Memory.State.mem hm
    have hf := congrArg Memory.State.frontier hm
    change y.mem = _ at hmem
    change y.regs (frontier realizes_insert) = _ at hf
    rw [hmem, hf]
    decide +kernel

private def inserted : Memory.State :=
  (Memory.spec 4).clientState initial (PriorityQueue.BinaryHeap.Memory.insert layout 0 15)
private def decreaseArgument : (HeapLayout × ℕ) × ℕ := ((⟨1, layout⟩, 0), 7)

private theorem inserted_inv : PriorityQueue.BinaryHeap.Memory.Inv layout inserted :=
  (triple_iff.mp (PriorityQueue.BinaryHeap.Memory.insert_triple valid inv
    (v := 0) (k := 15) admissible)).2.2.2.1

private theorem decrease_admissible :
    IndexedMinPQ.valid 15 (PriorityQueue.BinaryHeap.Memory.abs layout inserted)
      (.decreaseKey 0 7) :=
  ⟨⟨15, by decide +kernel, by decide⟩, by decide⟩

/-- Decrease-key uses the actual previous insertion state. Its native body changes the key to 7,
retains count/position and the dirty sentinel, and executes the original source history. -/
example : ∃ y, ExecWithin 4 (realizes_decreaseKey.code (frontier realizes_decreaseKey)
      (src realizes_decreaseKey) (tmp realizes_decreaseKey))
      (packed realizes_decreaseKey decreaseArgument inserted) y
      (3 * realizes_decreaseKey.factor) ∧
    y.mem 0 = 7 ∧ y.mem 1 = 1 ∧ y.mem 3 = 1 ∧ y.mem 100 = 7 ∧
    y.regs (frontier realizes_decreaseKey) = 4 := by
  have hw : ∀ i, Fits 4 (updateWords decreaseArgument i) := by
    intro i
    fin_cases i <;> decide +kernel
  have hs : decreaseSafe 4 decreaseArgument inserted :=
    ⟨by decide +kernel, 15, valid, inserted_inv, decrease_admissible⟩
  have hm : Memory.WellFormed 4 inserted := by
    have hvalid := (triple_iff.mp (PriorityQueue.BinaryHeap.Memory.insert_triple valid inv
      (v := 0) (k := 15) admissible)).1
    have h := wellFormed.run hvalid
    rw [StateTransitionSpec.run_runClient] at h
    exact h
  obtain ⟨hv, _, _⟩ := triple_iff.mp
    (PriorityQueue.BinaryHeap.Memory.decreaseKey_triple valid inserted_inv
      (v := 0) (k := 7) decrease_admissible)
  obtain ⟨y, hy, hm, _⟩ := native realizes_decreaseKey 4 decreaseArgument inserted hw hm hs hv
  have hc : memoryCost (PriorityQueue.BinaryHeap.Memory.decreaseKey layout 0 7) inserted = 2 :=
    by decide +kernel
  refine ⟨y, hy.mono ?_, ?_⟩
  · change realizes_decreaseKey.factor *
      (memoryCost (PriorityQueue.BinaryHeap.Memory.decreaseKey layout 0 7) inserted + 0 + 1) ≤ _
    rw [hc]
    omega
  · have hmem := congrArg Memory.State.mem hm
    have hf := congrArg Memory.State.frontier hm
    change y.mem = _ at hmem
    change y.regs (frontier realizes_decreaseKey) = _ at hf
    rw [hmem, hf]
    decide +kernel

end

end CslibFrontierTests.WordRAMBinaryHeapUpdate
