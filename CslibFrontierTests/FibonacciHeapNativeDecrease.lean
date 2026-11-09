/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Decrease
public import CslibFrontierTests.FibonacciHeapNativeCut

/-!
# Native decrease-key on the original allocated heap

All fixtures start from three original valid inserts and an extraction that creates a real
parent/child pair. One emitter precedes the runtime handle and key. Cases cover a root, keeping
heap order at a child (including equal-key handle priority), and cutting followed by cascading.
-/

public section

namespace CslibFrontierTests.FibonacciHeapNativeDecrease

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native
open FibonacciHeapNativeCut

/-- The conventional valid domain is inhabited on both a root and the consolidated child. -/
theorem valid_cases : decreaseValid 6 ![3, 2, 1, 4] consolidated ∧
    decreaseValid 6 ![3, 2, 2, 6] consolidated ∧
    decreaseValid 6 ![3, 2, 2, 5] consolidated ∧
    decreaseValid 6 ![3, 2, 2, 4] consolidated := by
  have hi : (layout 3 2).Inv consolidated ∧ Inv 3 63 ((layout 3 2).abs consolidated) :=
    consolidated_inv
  simp only [decreaseValid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨by decide, hi.1, 1, 63, 5, rfl, by decide, hi.2, by decide, by decide, by decide⟩,
    ⟨by decide, hi.1, 2, 63, 7, rfl, by decide, hi.2, by decide, by decide, by decide⟩,
    ⟨by decide, hi.1, 2, 63, 7, rfl, by decide, hi.2, by decide, by decide, by decide⟩,
    ⟨by decide, hi.1, 2, 63, 7, rfl, by decide, hi.2, by decide, by decide, by decide⟩⟩

/-- An absent handle is not admitted merely because its raw word fits. -/
example : ¬decreaseValid 6 ![3, 2, 0, 0] consolidated := by
  simp only [decreaseValid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rintro ⟨_, _, v, K, k₀, hv, _, _, hsv, _⟩
  have : v = 0 := Fin.ext hv
  subst v
  have hnone : abs 3 ((layout 3 2).abs consolidated) (0 : Fin 3) = none := by decide
  change abs 3 ((layout 3 2).abs consolidated) (0 : Fin 3) = some k₀ at hsv
  rw [hnone] at hsv
  contradiction

noncomputable section

private abbrev slots := 0 + realizes_decreaseKey.scratchSize + 1
private abbrev regs := 5 + slots
private def frontier : Fin regs := ⟨4, by unfold regs; omega⟩
private def source (i : Fin 4) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨5 + i, by unfold regs; omega⟩

private def loaded (v k : ℕ) : Data regs where
  regs i := if i = frontier then consolidated.frontier else if i.val = 0 then 3
    else if i.val = 1 then 2 else if i.val = 2 then v else if i.val = 3 then k else 0
  mem := consolidated.mem

private theorem native_decrease (v k : ℕ) (hv : v < 3) (hk : Fits 6 k)
    (hSafe : decreaseValid 6 ![3, 2, v, k] consolidated)
    (hValid : (Memory.spec 6).ValidHistory consolidated
      ((Memory.spec 6).clientHistory consolidated
        (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
          (decreaseKey 3 v k)))) :
    ∃ y, ExecWithin 6 (realizes_decreaseKey.code frontier source scratch) (loaded v k) y
        ((memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
          (decreaseKey 3 v k)) consolidated + 1) * realizes_decreaseKey.factor) ∧
      memoryState frontier y = (Memory.spec 0).clientState consolidated
        (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
          (decreaseKey 3 v k)) := by
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
  have hb : (loaded v k).Bounded 6 := by
    refine ⟨fun i => ?_, consolidated_wellFormed.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact consolidated_wellFormed.frontier_fits
    · decide
    · decide
    · exact (by decide : Fits 6 3).of_le (Nat.le_of_lt hv)
    · exact hk
    · decide
  have hin : (loaded v k).regs ∘ source = (![3, 2, v, k] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier (loaded v k) = consolidated := rfl
  obtain ⟨y, hy, hm, _, _⟩ :=
    (realizes_decreaseKey.code_spec frontier source scratch hi hd hf hs).2 6 ![3, 2, v, k]
      (loaded v k) hb hin (by rwa [hp]) (by rwa [hp])
  rw [hp] at hy hm
  rw [clientState_width 6] at hm
  refine ⟨y, ?_, hm⟩
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Nat.add_zero, Nat.mul_comm] using hy

/-- Root decrease keeps the structure and pays four actual source memory queries. -/
example : ∃ y, ExecWithin 6 (realizes_decreaseKey.code frontier source scratch)
      (loaded 1 4) y (5 * realizes_decreaseKey.factor) ∧
    y.mem 3 = 4 ∧ y.mem 30 = 2 ∧ y.mem 7 = 2 ∧ y.mem 31 = 1 ∧
    y.mem 1 = 63 ∧ y.regs frontier = 34 := by
  obtain ⟨y, hy, hm⟩ := native_decrease 1 4 (by decide) (by decide) valid_cases.1 (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (decreaseKey 3 1 4)) consolidated = 4 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 3).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 30).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 31).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

/-- Keeping a larger child key needs five source queries and performs no cut. -/
example : ∃ y, ExecWithin 6 (realizes_decreaseKey.code frontier source scratch)
      (loaded 2 6) y (6 * realizes_decreaseKey.factor) ∧
    y.mem 4 = 6 ∧ y.mem 30 = 2 ∧ y.mem 7 = 2 ∧ y.mem 18 = 1 ∧
    y.mem 1 = 63 ∧ y.regs frontier = 34 := by
  obtain ⟨y, hy, hm⟩ := native_decrease 2 6 (by decide) (by decide) valid_cases.2.1 (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (decreaseKey 3 2 6)) consolidated = 5 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 4).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 30).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 18).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

/-- Equal keys retain the smaller parent handle, with no structural update. -/
example : ∃ y, ExecWithin 6 (realizes_decreaseKey.code frontier source scratch)
      (loaded 2 5) y (6 * realizes_decreaseKey.factor) ∧
    y.mem 4 = 5 ∧ y.mem 30 = 2 ∧ y.mem 7 = 2 ∧ y.mem 18 = 1 := by
  obtain ⟨y, hy, hm⟩ := native_decrease 2 5 (by decide) (by decide) valid_cases.2.2.1 (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (decreaseKey 3 2 5)) consolidated = 5 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 4).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 30).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 18).trans (by decide)⟩

/-- A smaller key cuts the child, stops the cascade at the parent root, and changes the minimum.
All twenty-three source queries and the unchanged input/frontier are retained. -/
example : ∃ y, ExecWithin 6 (realizes_decreaseKey.code frontier source scratch)
      (loaded 2 4) y (24 * realizes_decreaseKey.factor) ∧
    y.mem 4 = 4 ∧ y.mem 30 = 3 ∧ y.mem 7 = 0 ∧ y.mem 18 = 0 ∧ y.mem 31 = 2 ∧
    y.mem 1 = 63 ∧ y.regs frontier = 34 := by
  obtain ⟨y, hy, hm⟩ := native_decrease 2 4 (by decide) (by decide) valid_cases.2.2.2 (by decide)
  have hc : memoryCost (Cslib.DataStructure.link (E := Memory.spec 0) ((layout 3 2).methods 0)
      (decreaseKey 3 2 4)) consolidated = 23 := by decide
  rw [hc] at hy
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 4).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 30).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 7).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 18).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 31).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

end

end CslibFrontierTests.FibonacciHeapNativeDecrease
