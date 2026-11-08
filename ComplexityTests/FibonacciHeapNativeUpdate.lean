/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.WordRAM.Realization.Witness
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Allocation
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Native.Update

/-!
# Native Fibonacci insertion on allocated states

One selected emitter handles first insertion, equal maximum keys with both handle orders,
and a strictly smaller key. Every fixture comes from the original allocator and indexed-queue
source. Native execution keeps the entire source memory state, including the input cell.
-/

public section

namespace ComplexityTests.FibonacciHeapNativeUpdate

open Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization FibonacciHeap FibonacciHeap.Native

private def allocator : Memory.Allocator (indexedMinPQSpec 2 31) 5 :=
  zeroAllocator (by decide) (by decide)

/-- The original allocator reserves the indexed layout above a retained input cell. -/
@[expose] def emptyHeap : Memory.State :=
  (Memory.spec 5).clientState (Memory.State.init [31])
    ((zeroAllocator (n := 2) (K := 31) (w := 5) (by decide) (by decide)).run (pure ()))

private def seeded (v : Fin 2) : Memory.State :=
  (Memory.spec 5).clientState (Memory.State.init [31])
    (allocator.run ((indexedMinPQSpec 2 31).call (.insert v 31)))

example (v : Fin 2) :
    (framed (n := 2) (K := 31) (w := 5) (by decide) (by decide) 2).inv (seeded v) := by
  have hv : (indexedMinPQSpec 2 31).ValidHistory allocator.init
      ((indexedMinPQSpec 2 31).clientHistory allocator.init
        ((indexedMinPQSpec 2 31).call (.insert v 31))) := by
    change ((none : Option ℕ) = none ∧ (31 : ℕ) ≤ 31) ∧ True
    decide
  exact (allocator.run_correct _ (Memory.zeroAbove_init [31]) (by decide) hv).2.2.1

private theorem empty_wellFormed : Memory.WellFormed 5 emptyHeap := by
  have hv : (Memory.spec 5).ValidHistory (Memory.State.init [31])
      ((Memory.spec 5).clientHistory (Memory.State.init [31]) (allocator.run (pure ()))) := by
    decide
  have h := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 5 (Memory.State.init [31])).run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

private theorem seeded_wellFormed (v : Fin 2) : Memory.WellFormed 5 (seeded v) := by
  have hv : (Memory.spec 5).ValidHistory (Memory.State.init [31])
      ((Memory.spec 5).clientHistory (Memory.State.init [31])
        (allocator.run ((indexedMinPQSpec 2 31).call (.insert v 31)))) := by
    fin_cases v <;> decide
  have h := (Memory.wellFormed_init (by decide) (by decide) :
    Memory.WellFormed 5 (Memory.State.init [31])).run hv
  rw [StateTransitionSpec.run_runClient] at h
  exact h

private def insertion (v k : ℕ) : Memory.Prog Unit :=
  Cslib.DataStructure.link (E := Memory.spec 0) ((layout 2 2).methods 0) (insert v k)

noncomputable section

private abbrev slots := 0 + realizes_insert.scratchSize + 1
private abbrev regs := 5 + slots
private def frontier : Fin regs := ⟨4, by unfold regs; omega⟩
private def source (i : Fin 4) : Fin regs := ⟨i, by unfold regs; omega⟩
private def scratch (i : Fin slots) : Fin regs := ⟨5 + i, by unfold regs; omega⟩

private def loaded (s : Memory.State) (v k : ℕ) : Data regs where
  regs i := if i = frontier then s.frontier else if i.val < 2 then 2
    else if i.val = 2 then v else if i.val = 3 then k else 0
  mem := s.mem

private theorem run_insert (s : Memory.State) (v k q : ℕ)
    (hw : Memory.WellFormed 5 s) (hv : v < 2) (hk : Fits 5 k)
    (hh : (Memory.spec 5).ValidHistory s ((Memory.spec 5).clientHistory s (insertion v k)))
    (hc : memoryCost (insertion v k) s = q) :
    ∃ y, ExecWithin 5 (realizes_insert.code frontier source scratch) (loaded s v k) y
        ((q + 1) * realizes_insert.factor) ∧
      memoryState frontier y = (Memory.spec 5).clientState s (insertion v k) := by
  dsimp only [insertion] at hh hc ⊢
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
  have hb : (loaded s v k).Bounded 5 := by
    refine ⟨fun i => ?_, hw.mem_fits⟩
    dsimp only [loaded]
    split_ifs
    · exact hw.frontier_fits
    · decide
    · exact (show Fits 5 2 by decide).of_le hv.le
    · exact hk
    · decide
  have hin : (loaded s v k).regs ∘ source = (![2, 2, v, k] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  have hp : memoryState frontier (loaded s v k) = s := rfl
  obtain ⟨y, hy, hm, _, _⟩ :=
    (realizes_insert.code_spec frontier source scratch hi hd hf hs).2 5 ![2, 2, v, k]
      (loaded s v k) hb hin (by
        change Fits 5 (2 + (9 * 2 + 5)) ∧ v < 2
        exact ⟨by decide, hv⟩) (by
        simpa only [hp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three,
          Matrix.head_cons, Matrix.tail_cons] using hh)
  rw [hp] at hy hm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at hy hm
  rw [hc] at hy
  exact ⟨y, by simpa only [Nat.add_zero, Nat.mul_comm] using hy, hm⟩

/-- First insertion retains the maximum key, writes size/minimum, and preserves dirty input. -/
example : ∃ y, ExecWithin 5 (realizes_insert.code frontier source scratch)
      (loaded emptyHeap 0 31) y (15 * realizes_insert.factor) ∧
    y.mem 2 = 31 ∧ y.mem 21 = 1 ∧ y.mem 24 = 1 ∧ y.mem 1 = 31 ∧ y.regs frontier = 25 := by
  obtain ⟨y, hy, hm⟩ := run_insert emptyHeap 0 31 14 empty_wellFormed
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨y, hy, ?_⟩
  have hstate : ((Memory.spec 5).clientState emptyHeap (insertion 0 31)).mem 2 = 31 := by
    decide
  exact ⟨(congrFun (congrArg Memory.State.mem hm) 2).trans hstate,
    (congrFun (congrArg Memory.State.mem hm) 21).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 24).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide),
    (congrArg Memory.State.frontier hm).trans (by decide)⟩

/-- Equal maximum keys retain the smaller old handle as the minimum. -/
example : ∃ y, ExecWithin 5 (realizes_insert.code frontier source scratch)
      (loaded (seeded 0) 1 31) y (19 * realizes_insert.factor) ∧
    y.mem 3 = 31 ∧ y.mem 21 = 1 ∧ y.mem 24 = 2 ∧ y.mem 1 = 31 := by
  obtain ⟨y, hy, hm⟩ := run_insert (seeded 0) 1 31 18 (seeded_wellFormed 0)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 3).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 21).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 24).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide)⟩

/-- An equal key with the smaller new handle takes the tie-breaking branch. -/
example : ∃ y, ExecWithin 5 (realizes_insert.code frontier source scratch)
      (loaded (seeded 1) 0 31) y (20 * realizes_insert.factor) ∧
    y.mem 2 = 31 ∧ y.mem 21 = 1 ∧ y.mem 24 = 2 ∧ y.mem 1 = 31 := by
  obtain ⟨y, hy, hm⟩ := run_insert (seeded 1) 0 31 19 (seeded_wellFormed 1)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 2).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 21).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 24).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide)⟩

/-- A strictly smaller key becomes the minimum without changing the input cell. -/
example : ∃ y, ExecWithin 5 (realizes_insert.code frontier source scratch)
      (loaded (seeded 0) 1 30) y (20 * realizes_insert.factor) ∧
    y.mem 3 = 30 ∧ y.mem 21 = 2 ∧ y.mem 24 = 2 ∧ y.mem 1 = 31 := by
  obtain ⟨y, hy, hm⟩ := run_insert (seeded 0) 1 30 19 (seeded_wellFormed 0)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨y, hy, (congrFun (congrArg Memory.State.mem hm) 3).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 21).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 24).trans (by decide),
    (congrFun (congrArg Memory.State.mem hm) 1).trans (by decide)⟩

end

end ComplexityTests.FibonacciHeapNativeUpdate
