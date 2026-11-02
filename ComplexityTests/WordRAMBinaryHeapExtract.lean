/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.PriorityQueue.BinaryHeap.Native.Extract
import ComplexityTests.WordRAMRealizationPacking

/-! The same extraction emitter handles an empty minimum-width heap, an unshifted maximum key,
and a real sift after root removal. Every fixture keeps dirty memory outside the owned block.
The native execution comes only from the shared realization contract. -/

namespace ComplexityTests.WordRAMBinaryHeapExtract

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
open ComplexityTests.WordRAMRealizationPacking

private abbrev raw (d : HeapLayout) :=
  (PriorityQueue.BinaryHeap.Memory.extractMin d.2).map (Option.map fun a => (a.1.val, a.2))

noncomputable section

private abbrev out (i : Fin 3) :=
  tmp realizes_extractMin (Fin.castAdd (realizes_extractMin.scratchSize + 1) i)

private theorem execute {w n K : ℕ} (L : PriorityQueue.BinaryHeap.Memory.Layout n)
    (s : Memory.State) (hL : L.Valid w K) (hs : PriorityQueue.BinaryHeap.Memory.Inv L s)
    (hw : Memory.WellFormed w s) (hin : ∀ i, Fits w (layoutWords ⟨n, L⟩ i)) :
    ∃ y, ExecWithin w (realizes_extractMin.code (frontier realizes_extractMin)
        (src realizes_extractMin) (tmp realizes_extractMin))
        (packed realizes_extractMin ⟨n, L⟩ s) y
        (realizes_extractMin.factor * (memoryCost (raw ⟨n, L⟩) s + 1)) ∧
      memoryState (frontier realizes_extractMin) y =
        (Memory.spec w).clientState s (raw ⟨n, L⟩) ∧
      ∀ i : Fin 3,
        y.regs (tmp realizes_extractMin (Fin.castAdd (realizes_extractMin.scratchSize + 1) i)) =
          WordEncoding.encode ((Memory.spec w).clientResult s (raw ⟨n, L⟩)) i := by
  have hv := (triple_iff.mp (PriorityQueue.BinaryHeap.Memory.extractMin_triple hL hs)).1
  have hh := congrArg (fun r => r.2.2) (extractMin_run w ⟨n, L⟩ s)
  change (Memory.spec w).clientHistory s (PriorityQueue.BinaryHeap.Memory.extractMin L) =
    (Memory.spec w).clientHistory s (raw ⟨n, L⟩) at hh
  rw [hh] at hv
  exact native realizes_extractMin w ⟨n, L⟩ s hin hw ⟨K, hL, hs⟩ hv

private def emptyL : PriorityQueue.BinaryHeap.Memory.Layout 0 :=
  PriorityQueue.BinaryHeap.Memory.compactLayout 0 0
private def emptyState : Memory.State := ⟨fun a => if a = 100 then 1 else 0, 1⟩

private theorem emptyValid : emptyL.Valid 1 0 :=
  PriorityQueue.BinaryHeap.Memory.valid_compactLayout (by decide +kernel) (by decide +kernel)

private theorem emptyInv : PriorityQueue.BinaryHeap.Memory.Inv emptyL emptyState := by
  apply (PriorityQueue.BinaryHeap.Memory.inv_empty ?_ ?_ rfl ?_).1
  · change 0 + 1 ≤ 1; decide
  · change 0 + (3 * 0 + 1) ≤ 1; decide
  · intro v hv; omega

-- No unnecessary literal 2 or positive handle capacity is required by the empty branch.
example : ∃ y, ExecWithin 1 (realizes_extractMin.code (frontier realizes_extractMin)
      (src realizes_extractMin) (tmp realizes_extractMin))
      (packed realizes_extractMin ⟨0, emptyL⟩ emptyState) y (2 * realizes_extractMin.factor) ∧
    y.mem = emptyState.mem ∧ y.regs (frontier realizes_extractMin) = 1 ∧
    y.regs (out 0) = 0 ∧ y.regs (out 1) = 0 ∧
    y.regs (out 2) = 0 := by
  have hw : Memory.WellFormed 1 emptyState := by
    refine ⟨by decide +kernel, fun a => ?_⟩
    change Fits 1 (if a = 100 then 1 else 0)
    split_ifs <;> decide
  have hin : ∀ i, Fits 1 (layoutWords ⟨0, emptyL⟩ i) := by
    intro i; fin_cases i <;> decide +kernel
  obtain ⟨y, hy, hm, ho⟩ := execute emptyL emptyState emptyValid emptyInv hw hin
  have hc : memoryCost (raw ⟨0, emptyL⟩) emptyState = 1 := by decide +kernel
  rw [hc] at hy
  refine ⟨y, hy.mono (by omega), ?_⟩
  have hmem := congrArg Memory.State.mem hm
  have hf := congrArg Memory.State.frontier hm
  refine ⟨hmem, hf, ?_, ?_, ?_⟩ <;>
    first | exact ho 0 | exact ho 1 | exact ho 2

private def layout (n : ℕ) : PriorityQueue.BinaryHeap.Memory.Layout n :=
  PriorityQueue.BinaryHeap.Memory.compactLayout n 0
private def initial (n : ℕ) : Memory.State :=
  ⟨fun a => if a = 100 then 7 else 0, 3 * n + 1⟩
private def add (n v k : ℕ) (s : Memory.State) : Memory.State :=
  (Memory.spec 4).clientState s (PriorityQueue.BinaryHeap.Memory.insert (layout n) v k)

private theorem initialInv (n : ℕ) (hn : n ≤ 3) :
    PriorityQueue.BinaryHeap.Memory.Inv (layout n) (initial n) := by
  apply (PriorityQueue.BinaryHeap.Memory.inv_empty ?_ ?_ ?_ ?_).1
  · simp only [layout, PriorityQueue.BinaryHeap.Memory.compactLayout, Block.Allocated,
      initial, Nat.zero_add]
    omega
  · simp only [layout, PriorityQueue.BinaryHeap.Memory.compactLayout, Block.Allocated,
      initial, Nat.zero_add, PriorityQueue.BinaryHeap.space]
    exact le_rfl
  · simp only [initial, layout, PriorityQueue.BinaryHeap.Memory.compactLayout, Nat.zero_add]
    rw [ite_eq_right (by omega)]
  · intro v hv
    simp only [initial, layout, PriorityQueue.BinaryHeap.Memory.compactLayout,
      Nat.zero_add]
    rw [ite_eq_right (by omega)]

private theorem addInv {n K : ℕ} (hL : (layout n).Valid 4 K) {s : Memory.State}
    (hs : PriorityQueue.BinaryHeap.Memory.Inv (layout n) s) (v : Fin n) (k : ℕ)
    (hv : IndexedMinPQ.valid K (PriorityQueue.BinaryHeap.Memory.abs (layout n) s) (.insert v k)) :
    PriorityQueue.BinaryHeap.Memory.Inv (layout n) (add n v k s) :=
  (triple_iff.mp (PriorityQueue.BinaryHeap.Memory.insert_triple hL hs hv)).2.2.2.1

private def singleton := add 1 0 15 (initial 1)
private theorem valid1 : (layout 1).Valid 4 15 :=
  PriorityQueue.BinaryHeap.Memory.valid_compactLayout (by decide +kernel) (by decide +kernel)
private theorem inv1 : PriorityQueue.BinaryHeap.Memory.Inv (layout 1) singleton :=
  addInv valid1 (initialInv 1 (by decide)) 0 15 ⟨rfl, le_rfl⟩

private def one := add 3 0 1 (initial 3)
private def two := add 3 1 2 one
private def three := add 3 2 3 two
private theorem valid3 : (layout 3).Valid 4 3 :=
  PriorityQueue.BinaryHeap.Memory.valid_compactLayout (by decide +kernel) (by decide +kernel)
private theorem inv3 : PriorityQueue.BinaryHeap.Memory.Inv (layout 3) three := by
  have h1 := addInv valid3 (initialInv 3 (by decide)) 0 1 (by exact ⟨by decide +kernel, by decide⟩)
  have h2 := addInv valid3 h1 1 2 (by exact ⟨by decide +kernel, by decide⟩)
  exact addInv valid3 h2 2 3 (by exact ⟨by decide +kernel, by decide⟩)

private theorem initialWF (n : ℕ) (hn : n ≤ 3) :
    Memory.WellFormed 4 (initial n) := by
  refine ⟨Fits.of_le (by decide : Fits 4 10) (by dsimp [initial]; omega), fun a => ?_⟩
  change Fits 4 (if a = 100 then 7 else 0)
  split_ifs <;> decide

private theorem addWF {n K : ℕ} (hL : (layout n).Valid 4 K) {s : Memory.State}
    (hs : PriorityQueue.BinaryHeap.Memory.Inv (layout n) s) (hw : Memory.WellFormed 4 s)
    (v : Fin n) (k : ℕ)
    (hv : IndexedMinPQ.valid K (PriorityQueue.BinaryHeap.Memory.abs (layout n) s) (.insert v k)) :
    Memory.WellFormed 4 (add n v k s) := by
  have h := hw.run (triple_iff.mp (PriorityQueue.BinaryHeap.Memory.insert_triple hL hs hv)).1
  rw [StateTransitionSpec.run_runClient] at h
  exact h

private theorem singletonWF : Memory.WellFormed 4 singleton :=
  addWF valid1 (initialInv 1 (by decide)) (initialWF 1 (by decide)) 0 15 ⟨rfl, le_rfl⟩

private theorem threeWF : Memory.WellFormed 4 three := by
  have h1 := addInv valid3 (initialInv 3 (by decide)) 0 1 ⟨rfl, by decide⟩
  have h2 := addInv valid3 h1 1 2 ⟨by decide +kernel, by decide⟩
  have hw1 := addWF valid3 (initialInv 3 (by decide)) (initialWF 3 (by decide)) 0 1
    ⟨rfl, by decide⟩
  have hw2 := addWF valid3 h1 hw1 1 2 ⟨by decide +kernel, by decide⟩
  exact addWF valid3 h2 hw2 2 3 ⟨by decide +kernel, by decide⟩

-- The maximum key remains unshifted and extraction clears count/position while preserving it.
example : ∃ y, ExecWithin 4 (realizes_extractMin.code (frontier realizes_extractMin)
      (src realizes_extractMin) (tmp realizes_extractMin))
      (packed realizes_extractMin ⟨1, layout 1⟩ singleton) y (6 * realizes_extractMin.factor) ∧
    y.mem 0 = 15 ∧ y.mem 1 = 0 ∧ y.mem 3 = 0 ∧ y.mem 100 = 7 ∧
    y.regs (out 0) = 1 ∧ y.regs (out 1) = 0 ∧
    y.regs (out 2) = 15 := by
  have hin : ∀ i, Fits 4 (layoutWords ⟨1, layout 1⟩ i) := by
    intro i; fin_cases i <;> decide +kernel
  obtain ⟨y, hy, hm, ho⟩ := execute (layout 1) singleton valid1 inv1 singletonWF hin
  have hc : memoryCost (raw ⟨1, layout 1⟩) singleton = 5 := by decide +kernel
  rw [hc] at hy
  have hmem := congrArg Memory.State.mem hm
  change y.mem = _ at hmem
  refine ⟨y, hy.mono (by omega), ?_⟩
  rw [hmem]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    (ho 0).trans (by decide +kernel), (ho 1).trans (by decide +kernel),
    (ho 2).trans (by decide +kernel)⟩

-- Root removal invokes the real sift and swaps the last key 3 below key 2.
example : ∃ y, ExecWithin 4 (realizes_extractMin.code (frontier realizes_extractMin)
      (src realizes_extractMin) (tmp realizes_extractMin))
      (packed realizes_extractMin ⟨3, layout 3⟩ three) y (17 * realizes_extractMin.factor) ∧
    y.mem 3 = 2 ∧ y.mem 4 = 1 ∧ y.mem 5 = 2 ∧ y.mem 7 = 0 ∧ y.mem 100 = 7 ∧
    y.regs (out 0) = 1 ∧ y.regs (out 1) = 0 ∧
    y.regs (out 2) = 1 := by
  have hin : ∀ i, Fits 4 (layoutWords ⟨3, layout 3⟩ i) := by
    intro i; fin_cases i <;> decide +kernel
  obtain ⟨y, hy, hm, ho⟩ := execute (layout 3) three valid3 inv3 threeWF hin
  have hc : memoryCost (raw ⟨3, layout 3⟩) three = 16 := by decide +kernel
  rw [hc] at hy
  have hmem := congrArg Memory.State.mem hm
  change y.mem = _ at hmem
  refine ⟨y, hy.mono (by omega), ?_⟩
  rw [hmem]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, (ho 0).trans (by decide +kernel), (ho 1).trans (by decide +kernel),
    (ho 2).trans (by decide +kernel)⟩

end

end ComplexityTests.WordRAMBinaryHeapExtract
