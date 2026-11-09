/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Cascade
public import ComplexityTests.FibonacciHeapNativeCut

/-!
# Actual native cascade branches

The consolidated source heap supplies a real parent/child pair. Its unmarked child takes the
mark-and-stop branch. A marked source-memory fixture takes the native cut and then stops at the
parent root. The latter checks the native reached-state contract, without asserting that an
arbitrary manually modified record satisfies the full heap invariant.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeCascade

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native
open FibonacciHeapNativeCut

/-- A marked child and its matching counter, for the native continuation branch. -/
@[expose] def marked : Memory.State :=
  (Memory.spec 6).clientState consolidated do
    Memory.write (2 + 6 * 3 + 2) 1
    Memory.write (2 + 9 * 3 + 3) 1

private theorem marked_wellFormed : Memory.WellFormed 6 marked := by
  have hv : (Memory.spec 6).ValidHistory consolidated
      ((Memory.spec 6).clientHistory consolidated do
        Memory.write (2 + 6 * 3 + 2) 1
        Memory.write (2 + 9 * 3 + 3) 1) := by decide
  have h := consolidated_wellFormed.run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

private theorem root_safe : cascadeSafe 6 ![3, 2, 1] consolidated := by
  change Fits 6 (2 + (9 * 3 + 5)) ∧ (1 : ℕ) < 3 ∧
    (cascadeStepSafe 6 ![3, 2, 1] consolidated ∧ True)
  exact ⟨by decide, by decide, ⟨by unfold cascadeStepSafe cutSafe; decide, trivial⟩⟩

private theorem mark_safe : cascadeSafe 6 ![3, 2, 2] consolidated := by
  change Fits 6 (2 + (9 * 3 + 5)) ∧ (2 : ℕ) < 3 ∧
    (cascadeStepSafe 6 ![3, 2, 2] consolidated ∧ True)
  exact ⟨by decide, by decide, ⟨by unfold cascadeStepSafe cutSafe; decide, trivial⟩⟩

private theorem cut_safe : cascadeSafe 6 ![3, 2, 2] marked := by
  let next := (Memory.spec 0).clientState marked
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (cascadeStep 2))
  change Fits 6 (2 + (9 * 3 + 5)) ∧ (2 : ℕ) < 3 ∧
    (cascadeStepSafe 6 ![3, 2, 2] marked ∧ cascadeStepSafe 6 ![3, 2, 1] next ∧ True)
  exact ⟨by decide, by decide, ⟨by unfold cascadeStepSafe cutSafe; decide,
    by unfold cascadeStepSafe cutSafe next; decide, trivial⟩⟩

/-- The source domain includes the root stop, the mark stop, and the continuing cut. -/
example : cascadeSafe 6 ![3, 2, 1] consolidated ∧
    cascadeSafe 6 ![3, 2, 2] consolidated ∧ cascadeSafe 6 ![3, 2, 2] marked :=
  ⟨root_safe, mark_safe, cut_safe⟩

/-- A marked child with a zero mark counter violates the cut's exact subtraction domain. -/
example : ¬cascadeStepSafe 6 ![3, 2, 2]
    { marked with mem := Function.update marked.mem (2 + 9 * 3 + 3) 0 } := by
  unfold cascadeStepSafe cutSafe
  decide

noncomputable section

private abbrev slots := 0 + realizes_cascade.scratchSize + 1
private abbrev regs := 4 + slots
private def frontier : Fin regs := ⟨3, by unfold regs; omega⟩
private def source (i : Fin 3) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨4 + i, by unfold regs; omega⟩

private def loaded (mem : Memory.State) (z : ℕ) : Data regs where
  regs i := if i = frontier then mem.frontier else if i.val = 0 then 3
    else if i.val = 1 then 2 else if i.val = 2 then z else 0
  mem := mem.mem

private theorem native_cascade (mem : Memory.State) (hw : Memory.WellFormed 6 mem)
    (z : ℕ) (hz : z < 3) (hSafe : cascadeSafe 6 ![3, 2, z] mem)
    (hValid : (Memory.spec 6).ValidHistory mem ((Memory.spec 6).clientHistory mem
      (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (cascade 4 z)))) :
    ∃ y, ExecWithin 6 (realizes_cascade.code frontier source scratch) (loaded mem z) y
        ((memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
          (cascade 4 z)) mem + 1) * realizes_cascade.factor) ∧
      memoryState frontier y = (Memory.spec 0).clientState mem
        (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (cascade 4 z)) := by
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
  have hb : (loaded mem z).Bounded 6 := by
    refine ⟨fun i => ?_, hw.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact hw.frontier_fits
    · decide
    · decide
    · exact (by decide : Fits 6 3).of_le (by omega)
    · decide
  have hin : (loaded mem z).regs ∘ source = (![3, 2, z] : Fin 3 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier (loaded mem z) = mem := rfl
  obtain ⟨y, hy, hm, _, _⟩ :=
    (realizes_cascade.code_spec frontier source scratch hi hd hf hs).2 6 ![3, 2, z]
      (loaded mem z) hb hin (by rwa [hp]) (by rwa [hp])
  rw [hp] at hy hm
  rw [clientState_width 6] at hm
  refine ⟨y, ?_, hm⟩
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Nat.add_zero, Nat.mul_comm] using hy

/-- A root only reads its null parent; it never consumes the ghost cutoff as native fuel. -/
example : ∃ y, ExecWithin 6 (realizes_cascade.code frontier source scratch)
      (loaded consolidated 1) y (2 * realizes_cascade.factor) ∧
    y.mem = consolidated.mem ∧ y.regs frontier = consolidated.frontier := by
  obtain ⟨y, hy, hm⟩ := native_cascade consolidated consolidated_wellFormed 1 (by decide)
    root_safe (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (cascade 4 1)) consolidated = 1 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (congrArg Memory.State.mem hm).trans (by rfl),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

/-- The unmarked child is marked once and stops, with five actual source memory queries. -/
example : ∃ y, ExecWithin 6 (realizes_cascade.code frontier source scratch)
      (loaded consolidated 2) y (6 * realizes_cascade.factor) ∧
    y.mem 22 = 1 ∧ y.mem 32 = 1 ∧ y.mem 7 = 2 ∧ y.mem 18 = 1 ∧
    y.mem 1 = 63 ∧ y.regs frontier = 34 := by
  obtain ⟨y, hy, hm⟩ := native_cascade consolidated consolidated_wellFormed 2 (by decide)
    mark_safe (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (cascade 4 2)) consolidated = 5 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 22).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 32).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 18).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

/-- The marked child is cut, the parent root stops the loop, and both native/source states
agree. The nineteen source queries include the final parent test; ghost fuel is not executed. -/
example : ∃ y, ExecWithin 6 (realizes_cascade.code frontier source scratch)
      (loaded marked 2) y (20 * realizes_cascade.factor) ∧
    y.mem 7 = 0 ∧ y.mem 18 = 0 ∧ y.mem 31 = 2 ∧ y.mem 32 = 0 ∧
    y.mem 1 = 63 ∧ y.regs frontier = 34 := by
  obtain ⟨y, hy, hm⟩ := native_cascade marked marked_wellFormed 2 (by decide)
    cut_safe (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (cascade 4 2)) marked = 19 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 18).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 31).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 32).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

end

end ComplexityTests.FibonacciHeapNativeCascade
