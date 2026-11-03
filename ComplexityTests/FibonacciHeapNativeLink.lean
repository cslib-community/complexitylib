/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Allocation
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Link
public import Complexity.Computability.WordRAM.Realization.Witness

/-!
# Native linking of actual source roots

Two valid original inserts produce distinct leaf roots. The selected native link returns the
lower-key root, attaches the other as its first child, and preserves the complete original memory
run. A malformed nonempty child pointer is rejected by the exact-subtraction domain.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeLink

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native

/-- Two original valid insertions, without consolidation. -/
@[expose] def twoRootClient : (indexedMinPQSpec 2 31).Client Unit := do
  (indexedMinPQSpec 2 31).call (.insert 0 31)
  (indexedMinPQSpec 2 31).call (.insert 1 7)

/-- Actual allocated source memory with two distinct degree-zero roots. -/
@[expose] def twoRoots : Memory.State :=
  (Memory.spec 5).clientState (Memory.State.init [31])
    ((zeroAllocator (n := 2) (K := 31) (w := 5) (by decide) (by decide)).run twoRootClient)

private theorem twoRoots_wellFormed : Memory.WellFormed 5 twoRoots := by
  have hv : (Memory.spec 5).ValidHistory (Memory.State.init [31])
      ((Memory.spec 5).clientHistory (Memory.State.init [31])
        ((zeroAllocator (n := 2) (K := 31) (w := 5) (by decide) (by decide)).run twoRootClient)) :=
    by decide
  have h := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 5 (Memory.State.init [31])).run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

example : linkSafe 5 ![2, 2, 0, 1] twoRoots := by
  unfold linkSafe linkAsSafe
  decide

example : ¬linkAsSafe 5 ![2, 2, 1, 0]
    { twoRoots with mem := Function.update twoRoots.mem 13 1 } := by
  unfold linkAsSafe
  decide

noncomputable section

private abbrev slots := 1 + realizes_link.scratchSize + 1
private abbrev regs := 5 + slots
private def frontier : Fin regs := ⟨4, by unfold regs; omega⟩
private def source (i : Fin 4) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨5 + i, by unfold regs; omega⟩

private def loaded : Data regs where
  regs i := if i = frontier then twoRoots.frontier else if i.val = 0 ∨ i.val = 1 then 2
    else if i.val = 3 then 1 else 0
  mem := twoRoots.mem

/-- The actual selected native code returns root `1`, taking eight source queries, with the
whole source memory/frontier retained and the maximum five-bit input untouched. -/
example : ∃ y, ExecWithin 5 (realizes_link.code frontier source scratch) loaded y
      (9 * realizes_link.factor) ∧ y.regs (scratch 0) = 1 ∧ y.mem 4 = 2 ∧
    y.mem 13 = 1 ∧ y.mem 7 = 1 ∧ y.mem 1 = 31 ∧ y.regs frontier = 25 := by
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
  have hb : loaded.Bounded 5 := by
    refine ⟨fun i => ?_, twoRoots_wellFormed.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact twoRoots_wellFormed.frontier_fits
    · decide
    · decide
    · decide
  have hin : loaded.regs ∘ source = (![2, 2, 0, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier loaded = twoRoots := rfl
  obtain ⟨y, hy, hm, hout, _⟩ :=
    (realizes_link.code_spec frontier source scratch hi hd hf hs).2 5 ![2, 2, 0, 1]
      loaded hb hin (by rw [hp]; unfold linkSafe linkAsSafe; decide) (by rw [hp]; decide)
  rw [hp] at hy hm hout
  have hr := hout 0
  change y.regs (scratch 0) = (Memory.spec 5).clientResult twoRoots
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 2 2).methods 0)
      (FibonacciHeap.link 0 1)) at hr
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 2 2).methods 0)
      (FibonacciHeap.link 0 1)) twoRoots = 8 := by decide
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Nat.add_zero] at hy hm
  rw [hc] at hy
  refine ⟨y, ?_, hr.trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 4).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 13).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩
  simpa only [Nat.mul_comm] using hy

end

end ComplexityTests.FibonacciHeapNativeLink
