/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Gather
public import ComplexityTests.FibonacciHeapNativeExtractSource
public import Complexity.Computability.WordRAM.Realization.Witness

/-!
# Native zero-capacity table scan

The original allocated zero-capacity heap is admissible at width three, although the address
coefficient `8` does not fit that width. The same uniformly selected native gather emitter scans
its empty table using the unchanged source/domain; all memory and the frontier are preserved.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeGather

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
open FibonacciHeapNativeExtractSource

private theorem zero_allocated : (layout 0 2).Inv emptyZero := by
  let a := zeroAllocator (n := 0) (K := 7) (w := 3) (by decide) (by decide)
  have hv : (indexedMinPQSpec 0 7).ValidHistory a.init
      ((indexedMinPQSpec 0 7).clientHistory a.init (pure ())) := trivial
  have hi : (framed (n := 0) (K := 7) (w := 3) (by decide) (by decide) 2).inv emptyZero :=
    (a.run_correct (pure ()) (Memory.zeroAbove_init [7]) (by decide) hv).2.2.1
  exact hi.1

private theorem zero_wellFormed : Memory.WellFormed 3 emptyZero := by
  have hv : (Memory.spec 3).ValidHistory (Memory.State.init [7])
      ((Memory.spec 3).clientHistory (Memory.State.init [7])
        ((zeroAllocator (n := 0) (K := 7) (w := 3) (by decide) (by decide)).run (pure ()))) :=
    by decide
  have h := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 3 (Memory.State.init [7])).run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

/-- The original `Gathering` assumptions are inhabited at zero capacity, with one table slot. -/
theorem zero_gathering : Gathering 0 (view 0 ((layout 0 2).abs emptyZero)) [] [] 0 := by
  refine ⟨SlotInv.empty ?_, ?_, Or.inl ⟨rfl, by decide⟩, by decide, by decide⟩
  · intro d hd
    obtain rfl : d = 0 := by omega
    decide
  · intro T hT
    contradiction

example : Fits 3 (2 + (9 * 0 + 5)) ∧ ¬Fits 3 8 := by decide

noncomputable section

private abbrev slots := 0 + realizes_gather.scratchSize + 1
private abbrev regs := 5 + slots
private def frontier : Fin regs := ⟨4, by unfold regs; omega⟩
private def source (i : Fin 4) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨5 + i, by unfold regs; omega⟩

private def loaded : Data regs where
  regs i := if i = frontier then emptyZero.frontier else if i.val = 1 then 2
    else if i.val = 2 then 1 else 0
  mem := emptyZero.mem

/-- The selected native emitter executes the actual single-query scan at width three, with
full source memory equality and the original maximum input/frontier retained. -/
example : ∃ y, ExecWithin 3 (realizes_gather.code frontier source scratch) loaded y
      (2 * realizes_gather.factor) ∧ y.mem = emptyZero.mem ∧ y.mem 1 = 7 ∧
    y.regs frontier = 7 := by
  have hi : Function.Injective scratch := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa only [scratch, Nat.add_left_cancel_iff] using this
  have hd : ∀ i j, source i ≠ scratch j := by
    intro i j h
    have := congrArg Fin.val h
    simp only [source, scratch] at this
    have := i.isLt
    omega
  have hf : ∀ j, scratch j ≠ frontier := by
    intro j h
    have := congrArg Fin.val h
    simp only [scratch, frontier] at this
    omega
  have hs : ∀ i, source i ≠ frontier := by
    intro i h
    have := congrArg Fin.val h
    simp only [source, frontier] at this
    have := i.isLt
    omega
  have hb : loaded.Bounded 3 := by
    refine ⟨fun i => ?_, zero_wellFormed.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact zero_wellFormed.frontier_fits
    · decide
    · decide
    · decide
  have hin : loaded.regs ∘ source = (![0, 2, 1, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier loaded = emptyZero := rfl
  have hSafe : gatherSafe 3 ![0, 2, 1, 0] emptyZero :=
    gatherSafe_of_gathering (by decide) zero_allocated zero_gathering
      (by intro T hT; contradiction) (by decide)
  have hspec := (realizes_gather.code_spec frontier source scratch hi hd hf hs).2 3
    (![0, 2, 1, 0] : Fin 4 → ℕ) loaded hb hin
  rw [hp] at hspec
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Nat.add_zero] at hspec
  obtain ⟨y, hy, hm, _, _⟩ := hspec hSafe (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 0 2).methods 0)
      (gather 1 0)) emptyZero = 1 := by decide
  rw [hc] at hy
  refine ⟨y, ?_, (congrArg Memory.State.mem hm).trans (by rfl),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩
  simpa only [Nat.mul_comm] using hy

end

end ComplexityTests.FibonacciHeapNativeGather
