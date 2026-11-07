/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Allocation
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Scatter
public import Complexity.Computability.WordRAM.Realization.Witness

/-!
# Native consolidation from a real source table collision

Original allocated inserts supply three distinct leaf roots. Placing one root while another
occupies degree zero witnesses the original `Placing` invariant with the third handle excluded.
The selected native loop links the collision and places the resulting degree-one root. A maximum
word accumulator checks that the source maximum is retained without a new arithmetic envelope.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeScatter

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- Three original insertions; extraction phases can consume these distinct singleton roots. -/
@[expose] def threeRootClient : (indexedMinPQSpec 3 63).Client Unit := do
  (indexedMinPQSpec 3 63).call (.insert 0 31)
  (indexedMinPQSpec 3 63).call (.insert 1 7)
  (indexedMinPQSpec 3 63).call (.insert 2 63)

/-- Original source allocation and inserts, above an untouched maximum-word input. -/
@[expose] def threeRoots : Memory.State :=
  (Memory.spec 6).clientState (Memory.State.init [63])
    ((zeroAllocator (n := 3) (K := 63) (w := 6) (by decide) (by decide)).run threeRootClient)

/-- The table's degree-zero slot holds root `1`, as after one source placement. -/
@[expose] def occupied : Memory.State :=
  (Memory.spec 6).clientState threeRoots (Memory.write (2 + 8 * 3) 2)

private theorem occupied_wellFormed : Memory.WellFormed 6 occupied := by
  have hv : (Memory.spec 6).ValidHistory (Memory.State.init [63])
      ((Memory.spec 6).clientHistory (Memory.State.init [63])
        ((zeroAllocator (n := 3) (K := 63) (w := 6) (by decide) (by decide)).run
          threeRootClient)) :=
    by decide
  have hw := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 6 (Memory.State.init [63])).run hv
  rw [StateTransitionSpec.run_runClient] at hw
  change Memory.WellFormed 6 threeRoots at hw
  have hv' : (Memory.spec 6).ValidHistory threeRoots
      ((Memory.spec 6).clientHistory threeRoots (Memory.write (2 + 8 * 3) 2)) := by decide
  have h := hw.run hv'
  rw [StateTransitionSpec.run_runClient] at h
  exact h

private theorem occupied_allocated : (layout 3 2).Inv occupied := by
  let a := zeroAllocator (n := 3) (K := 63) (w := 6) (by decide) (by decide)
  have hv : (indexedMinPQSpec 3 63).ValidHistory a.init
      ((indexedMinPQSpec 3 63).clientHistory a.init threeRootClient) := by
    change ((none : Option ℕ) = none ∧ (31 : ℕ) ≤ 63) ∧
      ((none : Option ℕ) = none ∧ (7 : ℕ) ≤ 63) ∧
      ((none : Option ℕ) = none ∧ (63 : ℕ) ≤ 63) ∧ True
    decide
  have hi : (framed (n := 3) (K := 63) (w := 6) (by decide) (by decide) 2).inv threeRoots :=
    (a.run_correct _ (Memory.zeroAbove_init [63]) (by decide) hv).2.2.1
  exact hi.1

/-- A concrete instance of the existing forest placement assumptions supplies native safety. -/
theorem occupied_placing : Placing 2 (2 : Fin 3) (view 3 ((layout 3 2).abs occupied))
    (.node 0 []) [.node 1 []] 0 := by
  have h0 : ValidRoot (view 3 ((layout 3 2).abs occupied)) none (.node (0 : Fin 3) []) :=
    ValidRoot.singleton (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1 : ValidRoot (view 3 ((layout 3 2).abs occupied)) none (.node (1 : Fin 3) []) :=
    ValidRoot.singleton (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, h0, by decide, by decide⟩
  refine ⟨by decide, ?_, ?_, ?_, by decide, Or.inl rfl⟩
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst T
    exact ⟨h1, by decide⟩
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst T
    decide
  · intro d hd hnone
    have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
    rcases hd' with rfl | rfl | rfl | rfl
    · exact (hnone (.node 1 []) (by simp) rfl).elim
    · decide
    · decide
    · decide

example : scatterSafe 6 ![3, 2, 0, 0] occupied :=
  scatterSafe_of_placing (by decide) occupied_allocated occupied_placing

private theorem max_safe : scatterSafe 6 ![3, 2, 0, 63] occupied := by
  let next := (Memory.spec 0).clientState occupied
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatterStep (0, 63)))
  change Fits 6 (2 + (9 * 3 + 5)) ∧ (0 : ℕ) < 3 ∧
    (scatterStepSafe 6 ![3, 2, 0, 63] occupied ∧ scatterStepSafe 6 ![3, 2, 1, 63] next ∧ True)
  exact ⟨by decide, by decide, ⟨by unfold scatterStepSafe linkSafe linkAsSafe; decide,
    by unfold scatterStepSafe linkSafe linkAsSafe next; decide, trivial⟩⟩

private theorem source_run (w md : ℕ) : (Memory.spec w).runClient occupied
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatter 4 0 md)) =
    (max md 1, (Memory.spec w).clientState occupied
      (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatter 4 0 0)),
      (Memory.spec w).clientHistory occupied
        (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
          (scatter 4 0 0))) := by
  rfl

private theorem source_valid (md : ℕ) : (Memory.spec 6).ValidHistory occupied
    ((Memory.spec 6).clientHistory occupied
      (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
        (scatter 4 0 md))) := by
  rw [StateTransitionSpec.clientHistory, source_run 6 md]
  change (Memory.spec 6).ValidHistory occupied ((Memory.spec 6).clientHistory occupied
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatter 4 0 0)))
  decide

private theorem source_cost (md : ℕ) : memoryCost
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatter 4 0 md))
    occupied = 14 := by
  unfold memoryCost
  rw [StateTransitionSpec.clientHistory, source_run 0 md]
  change memoryCost
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatter 4 0 0))
    occupied = 14
  decide

noncomputable section

private abbrev slots := 1 + realizes_scatter.scratchSize + 1
private abbrev regs := 5 + slots
private def frontier : Fin regs := ⟨4, by unfold regs; omega⟩
private def source (i : Fin 4) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨5 + i, by unfold regs; omega⟩

private def loaded (md : ℕ) : Data regs where
  regs i := if i = frontier then occupied.frontier else if i.val = 0 then 3
    else if i.val = 1 then 2 else if i.val = 3 then md else 0
  mem := occupied.mem

private theorem native_scatter (md : ℕ) (hmd : Fits 6 md)
    (hSafe : scatterSafe 6 ![3, 2, 0, md] occupied) :
    ∃ y, ExecWithin 6 (realizes_scatter.code frontier source scratch) (loaded md) y
        (15 * realizes_scatter.factor) ∧ y.regs (scratch 0) = max md 1 ∧
      y.mem 26 = 0 ∧ y.mem 27 = 2 ∧ y.mem 5 = 2 ∧ y.mem 18 = 1 ∧
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
  have hb : (loaded md).Bounded 6 := by
    refine ⟨fun i => ?_, occupied_wellFormed.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact occupied_wellFormed.frontier_fits
    · decide
    · decide
    · exact hmd
    · decide
  have hin : (loaded md).regs ∘ source = (![3, 2, 0, md] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier (loaded md) = occupied := rfl
  have hspec := (realizes_scatter.code_spec frontier source scratch hi hd hf hs).2 6
    (![3, 2, 0, md] : Fin 4 → ℕ) (loaded md) hb hin
  rw [hp] at hspec
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Nat.add_zero] at hspec
  obtain ⟨y, hy, hm, hout, _⟩ := hspec hSafe (source_valid md)
  have hr := hout 0
  change y.regs (scratch 0) = (Memory.spec 6).clientResult occupied
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatter 4 0 md)) at hr
  have hres : (Memory.spec 6).clientResult occupied
      (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatter 4 0 md)) =
      max md 1 := by
    rw [StateTransitionSpec.clientResult, source_run]
  rw [source_cost md] at hy
  rw [StateTransitionSpec.clientState, source_run 6 md] at hm
  change memoryState frontier y = (Memory.spec 6).clientState occupied
    (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0) (scatter 4 0 0)) at hm
  refine ⟨y, ?_, hr.trans hres,
    (congrFun (congrArg Memory.State.mem hm) 26).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 27).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 5).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 18).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩
  simpa only [Nat.mul_comm] using hy

/-- Collision and subsequent placement, justified by the real original forest assumptions. -/
example : ∃ y, ExecWithin 6 (realizes_scatter.code frontier source scratch) (loaded 0) y
      (15 * realizes_scatter.factor) ∧ y.regs (scratch 0) = 1 ∧ y.mem 27 = 2 := by
  obtain ⟨y, hy, hr, _, hs, _⟩ := native_scatter 0 (by decide)
    (scatterSafe_of_placing (by decide) occupied_allocated occupied_placing)
  exact ⟨y, hy, hr, hs⟩

/-- The same code also retains a maximum fitting accumulator through the collision. -/
example : ∃ y, ExecWithin 6 (realizes_scatter.code frontier source scratch) (loaded 63) y
      (15 * realizes_scatter.factor) ∧ y.regs (scratch 0) = 63 ∧ y.mem 27 = 2 := by
  obtain ⟨y, hy, hr, _, hs, _⟩ := native_scatter 63 (by decide) max_safe
  exact ⟨y, hy, hr, hs⟩

end

end ComplexityTests.FibonacciHeapNativeScatter
