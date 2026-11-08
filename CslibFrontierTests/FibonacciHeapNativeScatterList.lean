/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.ScatterList
public import CslibFrontierTests.FibonacciHeapNativeExtractSource
public import CslibFrontierTests.FibonacciHeapNativeScatter
public import CslibFrontier.Computability.WordRAM.Realization.Witness

/-!
# Native root-list consolidation and marked-child preparation

Two roots from the original allocated source are walked through their actual right pointers,
collide in the degree table, and are linked. The preparation fixture marks the first root and
sets its parent, so the native true phase must clear both fields and decrement the real counter.
The existing `Scattering` invariant supplies the complete loop domain in both phases.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeScatterList

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
open FibonacciHeapNativeScatter

/-- The same original source roots, optionally made into the marked-child input to preparation. -/
@[expose] def roots (prep : Bool) : Memory.State :=
  (Memory.spec 6).clientState threeRoots (do
    Memory.write (2 + 3) (if prep then 3 else 0)
    Memory.write (2 + 6 * 3) (if prep then 1 else 0)
    Memory.write (2 + 9 * 3 + 3) (if prep then 1 else 0))

private theorem roots_wellFormed (prep : Bool) : Memory.WellFormed 6 (roots prep) := by
  have hv : (Memory.spec 6).ValidHistory (Memory.State.init [63])
      ((Memory.spec 6).clientHistory (Memory.State.init [63])
        ((zeroAllocator (n := 3) (K := 63) (w := 6) (by decide) (by decide)).run
          threeRootClient)) := by decide
  have hw := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 6 (Memory.State.init [63])).run hv
  rw [StateTransitionSpec.run_runClient] at hw
  change Memory.WellFormed 6 threeRoots at hw
  have hv' : (Memory.spec 6).ValidHistory threeRoots
      ((Memory.spec 6).clientHistory threeRoots (do
        Memory.write (2 + 3) (if prep then 3 else 0)
        Memory.write (2 + 6 * 3) (if prep then 1 else 0)
        Memory.write (2 + 9 * 3 + 3) (if prep then 1 else 0))) := by
    cases prep <;> decide
  have h := hw.run hv'
  rw [StateTransitionSpec.run_runClient] at h
  exact h

private theorem roots_allocated (prep : Bool) : (layout 3 2).Inv (roots prep) := by
  intro i hi
  have hf : (roots prep).frontier = 34 := by cases prep <;> rfl
  rw [hf]
  cases i <;> simp only [layout, Cell.ok] at hi ⊢ <;> omega

private theorem leaf_valid {st : RawState 3} (v : Fin 3)
    (hin : st.inHeap v ≠ 0) (hm : st.mark v ≤ 1) (hc : st.child v = 0) (hd : st.deg v = 0) :
    ValidSubtree st none (.node v []) := by
  refine ⟨hin, hm, hd, Or.inl ⟨rfl, hc⟩, ?_, ?_, ?_, ?_⟩
  · intro _ h; contradiction
  · intro _ h; contradiction
  · intro i hi; simp at hi
  · intro _ h; contradiction

/-- Nonvacuity of the original root-list assumptions for both native extraction phases. -/
theorem roots_scattering (prep : Bool) :
    Scattering 2 (2 : Fin 3) prep (view 3 ((layout 3 2).abs (roots prep)))
      [] [.node 0 [], .node 1 []] 0 := by
  refine ⟨SlotInv.empty ?_, ?_, ?_, ?_, by decide, by decide, ?_, ?_⟩
  · intro d hd
    have h : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> cases prep <;> decide
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact leaf_valid 0 (by cases prep <;> decide) (by cases prep <;> decide)
        (by cases prep <;> decide) (by cases prep <;> decide)
    · exact leaf_valid 1 (by cases prep <;> decide) (by cases prep <;> decide)
        (by cases prep <;> decide) (by cases prep <;> decide)
  · intro hp T hT
    subst prep
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl <;> decide
  · change (view 3 ((layout 3 2).abs (roots prep))).right (0 : Fin 3) = 1 ∧ True
    cases prep <;> decide
  · intro y _
    fin_cases y <;> cases prep <;> decide
  · cases prep <;> decide

private theorem roots_safe (prep : Bool) : scatterListSafe prep 6 ![3, 2, 2, 0, 0] (roots prep) :=
  scatterListSafe_of_scattering (by decide) (roots_allocated prep) (roots_scattering prep)
    rfl (by intro y hy; cases hy; rfl)

/-- A mismatched original mark counter is rejected before preparation, rather than hidden in
an added native subtraction assumption. -/
example : ¬prepareSafe 6 ![3, 2, 0]
    { roots true with mem := Function.update (roots true).mem (2 + 9 * 3 + 3) 0 } := by
  unfold prepareSafe
  decide

noncomputable section

private abbrev slots (prep : Bool) := 1 + (realizes_scatterList prep).scratchSize + 1
private abbrev regs (prep : Bool) := 6 + slots prep
private def frontier (prep : Bool) : Fin (regs prep) := ⟨5, by unfold regs; omega⟩
private def source (prep : Bool) (i : Fin 5) : Fin (regs prep) := ⟨i, by unfold regs; omega⟩
private def scratch (prep : Bool) (i : Fin (slots prep)) : Fin (regs prep) :=
  ⟨6 + i, by unfold regs; omega⟩

private def loaded (prep : Bool) : Data (regs prep) where
  regs i := if i = frontier prep then (roots prep).frontier else if i.val = 0 then 3
    else if i.val = 1 then 2 else if i.val = 2 then 2 else 0
  mem := (roots prep).mem

private theorem native_scatterList (prep : Bool) :
    ∃ y, ExecWithin 6
        ((realizes_scatterList prep).code (frontier prep) (source prep) (scratch prep))
        (loaded prep) y ((if prep then 30 else 20) * (realizes_scatterList prep).factor) ∧
      y.regs (scratch prep 0) = 1 ∧ y.mem 27 = 2 ∧ y.mem 5 = 2 ∧ y.mem 20 = 0 ∧
      y.mem 32 = 0 ∧ y.mem 1 = 63 ∧ y.regs (frontier prep) = 34 := by
  have hi : Function.Injective (scratch prep) := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa only [scratch, Nat.add_left_cancel_iff] using this
  have hd : ∀ i j, source prep i ≠ scratch prep j := by
    intro i j h
    have := congrArg Fin.val h
    simp only [source, scratch] at this
    have := i.isLt
    omega
  have hf : ∀ j, scratch prep j ≠ frontier prep := by
    intro j h
    have := congrArg Fin.val h
    simp only [scratch, frontier] at this
    omega
  have hs : ∀ i, source prep i ≠ frontier prep := by
    intro i h
    have := congrArg Fin.val h
    simp only [source, frontier] at this
    have := i.isLt
    omega
  have hb : (loaded prep).Bounded 6 := by
    refine ⟨fun i => ?_, (roots_wellFormed prep).mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact (roots_wellFormed prep).frontier_fits
    · decide
    · decide
    · decide
    · decide
  have hin : (loaded prep).regs ∘ source prep = (![3, 2, 2, 0, 0] : Fin 5 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState (frontier prep) (loaded prep) = roots prep := rfl
  have hspec := ((realizes_scatterList prep).code_spec (frontier prep) (source prep) (scratch prep)
    hi hd hf hs).2 6 (![3, 2, 2, 0, 0] : Fin 5 → ℕ) (loaded prep) hb hin
  rw [hp] at hspec
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Nat.add_zero] at hspec
  have hv : (Memory.spec 6).ValidHistory (roots prep)
      ((Memory.spec 6).clientHistory (roots prep)
        (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
          (scatterList 4 prep 2 0 0))) := by cases prep <;> decide
  obtain ⟨y, hy, hm, hout, _⟩ := hspec (roots_safe prep) hv
  have hr := hout 0
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (scatterList 4 prep 2 0 0)) (roots prep) = if prep then 29 else 19 := by
    cases prep <;> decide
  rw [hc] at hy
  refine ⟨y, ?_, hr.trans (by cases prep <;> decide),
    (congrFun (congrArg Memory.State.mem hm) 27).trans (by cases prep <;> decide),
    (congrFun (congrArg Memory.State.mem hm) 5).trans (by cases prep <;> decide),
    (congrFun (congrArg Memory.State.mem hm) 20).trans (by cases prep <;> decide),
    (congrFun (congrArg Memory.State.mem hm) 32).trans (by cases prep <;> decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by cases prep <;> decide),
    (congrArg Memory.State.frontier hm).trans (by cases prep <;> decide)⟩
  cases prep <;> simpa only [ite_true, Bool.false_eq_true, ite_false, Nat.mul_comm] using hy

/-- The original root phase executes two real iterations and a table collision. -/
example : ∃ y, ExecWithin 6 ((realizes_scatterList false).code
      (frontier false) (source false) (scratch false)) (loaded false) y
      (20 * (realizes_scatterList false).factor) ∧ y.regs (scratch false 0) = 1 := by
  obtain ⟨y, hy, hr, _⟩ := native_scatterList false
  exact ⟨y, hy, hr⟩

/-- The child phase additionally clears a genuine mark and parent and decrements the counter. -/
example : ∃ y, ExecWithin 6 ((realizes_scatterList true).code
      (frontier true) (source true) (scratch true)) (loaded true) y
      (30 * (realizes_scatterList true).factor) ∧ y.regs (scratch true 0) = 1 ∧ y.mem 32 = 0 := by
  obtain ⟨y, hy, hr, _, _, _, hc, _⟩ := native_scatterList true
  exact ⟨y, hy, hr, hc⟩

end

namespace Zero

noncomputable section

open FibonacciHeapNativeExtractSource

private abbrev slots := 1 + (realizes_scatterList true).scratchSize + 1
private abbrev regs := 6 + slots
private def frontier : Fin regs := ⟨5, by unfold regs; omega⟩
private def source (i : Fin 5) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨6 + i, by unfold regs; omega⟩

private def loaded : Data regs where
  regs i := if i = frontier then emptyZero.frontier else if i.val = 1 then 2
    else if i.val = 3 ∨ i.val = 4 then 7 else 0
  mem := emptyZero.mem

/-- A zero count executes no list step: the unused cursor and maximum may be maximum words,
even at zero capacity. The original small-width layout remains admitted. -/
example : ∃ y, ExecWithin 3 ((realizes_scatterList true).code frontier source scratch) loaded y
      (realizes_scatterList true).factor ∧ y.regs (scratch 0) = 7 ∧
    y.mem = emptyZero.mem ∧ y.regs frontier = 7 := by
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
  have hw : Memory.WellFormed 3 emptyZero := by
    have hv : (Memory.spec 3).ValidHistory (Memory.State.init [7])
        ((Memory.spec 3).clientHistory (Memory.State.init [7])
          ((zeroAllocator (n := 0) (K := 7) (w := 3) (by decide) (by decide)).run (pure ()))) :=
      by decide
    have h := (Memory.wellFormed_init (by decide) (by decide) :
      Memory.WellFormed 3 (Memory.State.init [7])).run hv
    rw [StateTransitionSpec.run_runClient] at h
    exact h
  have hb : loaded.Bounded 3 := by
    refine ⟨fun i => ?_, hw.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact hw.frontier_fits
    · decide
    · decide
    · decide
  have hin : loaded.regs ∘ source = (![0, 2, 0, 7, 7] : Fin 5 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier loaded = emptyZero := rfl
  have hSafe : scatterListSafe true 3 ![0, 2, 0, 7, 7] emptyZero := ⟨by decide, trivial⟩
  have hspec := ((realizes_scatterList true).code_spec frontier source scratch hi hd hf hs).2 3
    (![0, 2, 0, 7, 7] : Fin 5 → ℕ) loaded hb hin
  rw [hp] at hspec
  obtain ⟨y, hy, hm, hout, _⟩ := hspec hSafe (by decide)
  have hr := hout 0
  change y.regs (scratch 0) = 7 at hr
  change ExecWithin 3 _ _ _ ((realizes_scatterList true).factor * (0 + 1)) at hy
  have hm' : memoryState frontier y = emptyZero := hm
  exact ⟨y, by simpa only [Nat.zero_add, Nat.mul_one] using hy, hr,
    congrArg Memory.State.mem hm', congrArg Memory.State.frontier hm'⟩

end

end Zero

end ComplexityTests.FibonacciHeapNativeScatterList
