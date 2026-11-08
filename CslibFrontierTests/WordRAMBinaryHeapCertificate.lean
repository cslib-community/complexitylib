/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Certificate

/-! The retained adaptive insert/tie/decrease/extract client runs through the new single raw
heap program, after actual compact initialization. Each operation pays its final halt; host
continuations and external argument delivery retain the existing DynamicProgram convention. -/

namespace CslibFrontierTests.WordRAMBinaryHeapCertificate

open Cslib Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

noncomputable section

private def sampleClient : (indexedMinPQSpec 4 20).Client (Option (Fin 4 × ℕ)) := do
  (indexedMinPQSpec 4 20).call (.insert 2 8)
  (indexedMinPQSpec 4 20).call (.insert 1 8)
  (indexedMinPQSpec 4 20).call (.decreaseKey 2 0)
  (indexedMinPQSpec 4 20).call .extractMin

private def outsideMemory (a : ℕ) : ℕ := if a = 100 then 7 else 0

private def initial : Data Program.registers :=
  ⟨fun i => if i = Program.code.frontierReg then 10 else
    if i = Program.code.nReg then 4 else 0, outsideMemory⟩

private theorem initial_bounded : initial.Bounded 10 := by
  constructor
  · intro i
    dsimp only [initial]
    split_ifs <;> decide
  · intro a
    change Fits 10 (outsideMemory a)
    unfold outsideMemory
    split <;> decide

-- The same source client as the legacy regression, using the replacement fixed program.
example :
    ∃ y₀ y traces,
      ExecWithin 10 Program.code.initFresh initial y₀
        (2 * Initialize.realizes_reserve.factor + Initialize.realizes_metadata.factor) ∧
      y₀.mem 100 = 7 ∧
      (certificate (n := 4) (base := 10) (show Fits 10 (10 + space 4) by decide)
        (show Fits 10 20 by decide)).rep (IndexedMinPQ.empty 4) y₀ ∧
      Executes ((dynamicProgram 4 20).ExecOp 10) sampleClient y₀ (some (2, 0)) y traces ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        (indexedMinPQSpec 4 20).totalCost (fun _ o => operationTime o + 1)
          (IndexedMinPQ.empty 4) ((indexedMinPQSpec 4 20).clientHistory
            (IndexedMinPQ.empty 4) sampleClient) := by
  have hS : Fits 10 (10 + space 4) := by decide
  have hK : Fits 10 20 := by decide
  have hfront : initial.regs Program.code.frontierReg = 10 := by
    simp only [initial, ite_true]
  have hn : initial.regs Program.code.nReg = 4 := by
    simp only [initial, ite_eq_right Program.code.nReg_ne_frontier, ite_true]
  have hz : ∀ a, (Block.mk 10 (space 4)).Owns a → initial.mem a = 0 := by
    intro a ha
    have hne : a ≠ 100 := by dsimp only [Block.Owns, space] at ha; omega
    simp only [initial, outsideMemory, ite_eq_right hne]
  obtain ⟨y₀, he, hm, _, hr₀⟩ := Representation.initFresh_rep
    (show Fits 10 4 by decide) hK initial initial_bounded hfront hn hS hz
  have hhist : (indexedMinPQSpec 4 20).clientHistory (IndexedMinPQ.empty 4) sampleClient =
      [.insert 2 8, .insert 1 8, .decreaseKey 2 0, .extractMin] := rfl
  have hv : (indexedMinPQSpec 4 20).ValidHistory (IndexedMinPQ.empty 4)
      ((indexedMinPQSpec 4 20).clientHistory (IndexedMinPQ.empty 4) sampleClient) := by
    rw [hhist]
    simp [IndexedMinPQ.valid, IndexedMinPQ.step, IndexedMinPQ.empty]
  have hres : (indexedMinPQSpec 4 20).clientResult (IndexedMinPQ.empty 4) sampleClient =
      some (2, 0) := by decide
  obtain ⟨y, traces, hex, _, hcost⟩ := run_client_bound hS hK sampleClient hr₀ hv
  rw [hres] at hex
  refine ⟨y₀, y, traces, he, ?_, (certificate_rep_iff hS hK _ _).mpr hr₀, hex, hcost⟩
  rw [hm]
  rfl

-- The domain is meaningful: decreasing an absent handle is not an admissible history.
example : ¬(indexedMinPQSpec 4 20).ValidHistory (IndexedMinPQ.empty 4) [.decreaseKey 2 0] := by
  simp [IndexedMinPQ.valid, IndexedMinPQ.empty]

end

end CslibFrontierTests.WordRAMBinaryHeapCertificate
