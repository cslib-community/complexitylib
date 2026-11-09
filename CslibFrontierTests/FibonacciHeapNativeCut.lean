/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Allocation
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain
public import CslibFrontier.Computability.WordRAM.Realization.Witness

/-!
# Genuine parent/child domains for native Fibonacci updates

Three valid inserts followed by extraction leave a root with one child. The fixture retains
the full existing heap invariant, and witnesses the positive-degree and minimum-pointer domains
used by the native source blocks. These domain checks are distinct from full native decrease-key
or extraction, which still require the loop certificates and their reached-state proofs.
-/

public section

namespace CslibFrontierTests.FibonacciHeapNativeCut

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native

/-- Original indexed operations that create a parent/child pair by actual consolidation. -/
@[expose] def consolidationClient : (indexedMinPQSpec 3 63).Client Unit := do
  (indexedMinPQSpec 3 63).call (.insert 0 0)
  (indexedMinPQSpec 3 63).call (.insert 1 5)
  (indexedMinPQSpec 3 63).call (.insert 2 7)
  let _ ← (indexedMinPQSpec 3 63).call .extractMin
  pure ()

private def allocator : Memory.Allocator (indexedMinPQSpec 3 63) 6 :=
  zeroAllocator (by decide) (by decide)

/-- Heap memory obtained from the existing source, above an untouched maximum-word input. -/
@[expose] def consolidated : Memory.State :=
  (Memory.spec 6).clientState (Memory.State.init [63])
    ((zeroAllocator (n := 3) (K := 63) (w := 6) (by decide) (by decide)).run
      consolidationClient)

theorem consolidated_inv :
    (framed (n := 3) (K := 63) (w := 6) (by decide) (by decide) 2).inv
    consolidated := by
  have hv : (indexedMinPQSpec 3 63).ValidHistory allocator.init
      ((indexedMinPQSpec 3 63).clientHistory allocator.init consolidationClient) := by
    change ((none : Option ℕ) = none ∧ (0 : ℕ) ≤ 63) ∧
      ((none : Option ℕ) = none ∧ (5 : ℕ) ≤ 63) ∧
      ((none : Option ℕ) = none ∧ (7 : ℕ) ≤ 63) ∧ True ∧ True
    decide
  exact (allocator.run_correct _ (Memory.zeroAbove_init [63]) (by decide) hv).2.2.1

/-- The new native-domain bridge applies to an actual existing heap invariant. -/
example : cutSafe 6 ![3, 2, 2, 1] consolidated := by
  have hi : (layout 3 2).Inv consolidated ∧ Inv 3 63 ((layout 3 2).abs consolidated) :=
    consolidated_inv
  have hc : (abs 3 ((layout 3 2).abs consolidated) (2 : Fin 3)).isSome := by decide
  obtain ⟨m, ts, h⟩ := cascading_of_fibRawInv hi.2 hc
  have hcur : (2 : Fin 3) ∈
      Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.forestNodes ts := (h.dom 2).mpr hc
  have hpar : (view 3 ((layout 3 2).abs consolidated)).par (2 : Fin 3) =
      (1 : Fin 3).val + 1 := by decide
  exact cutSafe_of_cascading (by decide) hi.1 h hcur hpar

theorem consolidated_wellFormed : Memory.WellFormed 6 consolidated := by
  have hv : (Memory.spec 6).ValidHistory (Memory.State.init [63])
      ((Memory.spec 6).clientHistory (Memory.State.init [63])
        (allocator.run consolidationClient)) := by decide
  have h := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 6 (Memory.State.init [63])).run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

/-- Handle `1` is the minimum root with child `2`, and its degree is positive. -/
example : consolidated.mem 30 = 2 ∧ consolidated.mem 18 = 1 ∧
    consolidated.mem 9 = 3 ∧ consolidated.mem 7 = 2 ∧
    consolidated.mem 1 = 63 ∧ consolidated.frontier = 34 := by decide

/-- The source unlink takes the single-child branch and leaves the input and frontier intact. -/
example :
    let p := Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (unlink 2 1)
    (Memory.spec 6).ValidHistory consolidated ((Memory.spec 6).clientHistory consolidated p) ∧
    ((Memory.spec 6).clientHistory consolidated p).length = 3 ∧
    ((Memory.spec 6).clientState consolidated p).mem 18 = 0 ∧
    ((Memory.spec 6).clientState consolidated p).mem 9 = 0 ∧
    ((Memory.spec 6).clientState consolidated p).mem 1 = 63 ∧
    ((Memory.spec 6).clientState consolidated p).frontier = 34 := by decide

/-- The native unlink domain is inhabited on this genuine source heap. -/
example : Fits 6 (2 + (9 * 3 + 5)) ∧ (2 : ℕ) < 3 ∧ (1 : ℕ) < 3 ∧
    1 ≤ consolidated.mem (2 + 5 * 3 + 1) := by decide

/-- A root-key decrease has the positive minimum pointer required by exact subtraction. -/
example : Fits 6 (2 + (9 * 3 + 5)) ∧ (1 : ℕ) < 3 ∧
    1 ≤ consolidated.mem (2 + 9 * 3 + 1) ∧
    ((Memory.spec 6).clientState consolidated
      (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
        (setKey 1 4))).mem 3 = 4 := by decide

/-- Empty allocated memory fails both nonempty-update premises, as intended. -/
example :
    let s := (Memory.spec 6).clientState (Memory.State.init [63])
      (allocator.run (pure ()))
    ¬1 ≤ s.mem (2 + 5 * 3 + 1) ∧ ¬1 ≤ s.mem (2 + 9 * 3 + 1) := by decide

noncomputable section

private abbrev slots := 0 + realizes_cut.scratchSize + 1
private abbrev regs := 5 + slots
private def frontier : Fin regs := ⟨4, by unfold regs; omega⟩
private def source (i : Fin 4) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨5 + i, by unfold regs; omega⟩

private def loaded : Data regs where
  regs i := if i = frontier then consolidated.frontier else if i.val = 0 then 3
    else if i.val = 1 ∨ i.val = 2 then 2 else if i.val = 3 then 1 else 0
  mem := consolidated.mem

/-- The selected native cut executes the real single-child case, retains all source memory,
and is charged by its sixteen actual memory queries plus the realization overhead. -/
example : ∃ y, ExecWithin 6 (realizes_cut.code frontier source scratch) loaded y
      (17 * realizes_cut.factor) ∧
    y.mem 7 = 0 ∧ y.mem 18 = 0 ∧ y.mem 9 = 0 ∧ y.mem 31 = 2 ∧
    y.mem 1 = 63 ∧ y.regs frontier = 34 := by
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
  have hb : loaded.Bounded 6 := by
    refine ⟨fun i => ?_, consolidated_wellFormed.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact consolidated_wellFormed.frontier_fits
    · decide
    · decide
    · decide
    · decide
  have hin : loaded.regs ∘ source = (![3, 2, 2, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier loaded = consolidated := rfl
  obtain ⟨y, hy, hm, _, _⟩ :=
    (realizes_cut.code_spec frontier source scratch hi hd hf hs).2 6 ![3, 2, 2, 1]
      loaded hb hin (by rw [hp]; unfold cutSafe; decide) (by rw [hp]; decide)
  rw [hp] at hy hm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hy hm
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0)
      ((layout 3 2).methods 0) (cut 2 1)) consolidated = 16 := by decide
  rw [hc] at hy
  refine ⟨y, ?_, (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 18).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 9).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 31).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩
  simpa only [Nat.add_zero, Nat.mul_comm] using hy

end

end CslibFrontierTests.FibonacciHeapNativeCut
