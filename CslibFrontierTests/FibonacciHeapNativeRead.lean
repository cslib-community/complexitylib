/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Allocation
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Read

/-!
# Executing a Fibonacci-heap native lookup at the maximum word

The initial memory is obtained by actually allocating and inserting through the existing
indexed-queue source. The selected uniform lookup emitter then returns the maximum five-bit key
as `[1,31]`, within its native instruction bound, retaining the input cell and frontier.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeRead

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native

private def input : Memory.State := Memory.State.init [31]
private def allocator : Memory.Allocator (indexedMinPQSpec 2 31) 5 :=
  zeroAllocator (by decide) (by decide)
private def insertClient : (indexedMinPQSpec 2 31).Client Unit :=
  (indexedMinPQSpec 2 31).call (.insert 0 31)

/-- A genuine maximum-key heap state, after the existing allocation and insertion programs. -/
@[expose] def planted : Memory.State :=
  (Memory.spec 5).clientState (Memory.State.init [31])
    ((zeroAllocator (n := 2) (K := 31) (w := 5) (by decide) (by decide)).run
      ((indexedMinPQSpec 2 31).call (.insert 0 31)))

/-- The maximum-key fixture is an actual heap invariant instance, not just a memory pattern. -/
example : (framed (n := 2) (K := 31) (w := 5) (by decide) (by decide) 2).inv planted := by
  have hv : (indexedMinPQSpec 2 31).ValidHistory allocator.init
      ((indexedMinPQSpec 2 31).clientHistory allocator.init insertClient) := by
    change ((none : Option ℕ) = none ∧ (31 : ℕ) ≤ 31) ∧ True
    decide
  exact (allocator.run_correct insertClient (Memory.zeroAbove_init [31]) (by decide) hv).2.2.1

private theorem planted_wellFormed : Memory.WellFormed 5 planted := by
  have hv : (Memory.spec 5).ValidHistory input
      ((Memory.spec 5).clientHistory input (allocator.run insertClient)) := by decide
  have hw : Memory.WellFormed 5 input := Memory.wellFormed_init (by decide) (by decide)
  have h := hw.run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

noncomputable section

private abbrev slots := 2 + realizes_getKey.scratchSize + 1
private abbrev regs := 4 + slots
private def frontier : Fin regs := ⟨3, by unfold regs; omega⟩
private def source (i : Fin 3) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨4 + i, by unfold regs; omega⟩

private def loaded : Data regs where
  regs i := if i = frontier then planted.frontier else if i.val < 2 then 2 else 0
  mem := planted.mem

/-- The actual selected native emitter retains a maximum key as an unshifted payload. -/
example : ∃ y, ExecWithin 5 (realizes_getKey.code frontier source scratch) loaded y
      (3 * realizes_getKey.factor) ∧
    y.regs (scratch (Fin.castAdd (realizes_getKey.scratchSize + 1) 0)) = 1 ∧
    y.regs (scratch (Fin.castAdd (realizes_getKey.scratchSize + 1) 1)) = 31 ∧
    y.mem 1 = 31 ∧ y.regs frontier = 25 := by
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
    refine ⟨fun i => ?_, planted_wellFormed.2⟩
    dsimp only [loaded]
    split_ifs
    · exact planted_wellFormed.1
    · decide
    · decide
  have hin : loaded.regs ∘ source = (![2, 2, 0] : Fin 3 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier loaded = planted := rfl
  -- The linked syntax uses Memory.Prog's canonical width; admissibility below uses five bits.
  have hv : (Memory.spec 5).ValidHistory planted
      ((Memory.spec 5).clientHistory planted
        (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 2 2).methods 0)
          (getKey 0))) := by decide
  obtain ⟨y, hy, hm, ho, _⟩ :=
    (realizes_getKey.code_spec frontier source scratch hi hd hf hs).2 5 ![2, 2, 0]
      loaded hb hin (by decide) (by simpa only [hp, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using hv)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0)
      ((layout 2 2).methods 0) (getKey 0))
      planted = 2 := by decide
  have ha : (Memory.spec 5).clientResult planted
      (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 2 2).methods 0)
        (getKey 0)) = some 31 := by decide
  have hm' : memoryState frontier y = planted := hm
  rw [hp] at hy ho
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hy ho
  rw [hc] at hy
  rw [ha] at ho
  refine ⟨y, ?_, ho 0, ho 1, ?_, congrArg Memory.State.frontier hm'⟩
  · simpa only [Nat.add_zero, Nat.mul_comm] using hy
  · exact congrFun (congrArg Memory.State.mem hm') 1

end

end ComplexityTests.FibonacciHeapNativeRead
