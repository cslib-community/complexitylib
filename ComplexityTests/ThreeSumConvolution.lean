/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.Weight

/-!
# Convolution-3SUM reduction and native graph-weight regressions

These are checks of a reduction and its one-weight construction kernel, not a fast 3SUM solver.
-/

namespace ComplexityTests.ThreeSumConvolution

open Cslib
open Algorithms.ThreeSum
open Algorithms.ExactTriangle (HasZeroTriangle)
open WordRAM.Signed (encode result)

private def values (i : ℕ) : ℤ := [9, -2, -4].getD i 0

/-- Repeated indices are allowed, this convolution yes-instance is not an ordinary distinct-position
3SUM yes-instance, a zero at index zero suffices, and the corresponding triangle has two negative
edges and a positive negated edge. -/
example :
    Convolution 3 values ∧
    (¬∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ values i + values j + values k = 0) ∧
    Convolution 3 (fun i => if i = 0 then 0 else 1) ∧
    HasZeroTriangle (fun _ _ : Fin 1 => -2) (fun _ _ => 3) (fun _ _ => -1) ∧
    ¬HasZeroTriangle (fun _ _ : Fin 1 => 1) (fun _ _ => 1) (fun _ _ => 1) ∧
    weightAB 3 values 19 (0 : Fin 2) 1 = -2 ∧
    weightBC 3 2 values 19 (1 : Fin 2) 0 = -2 ∧
    weightAC 3 2 values 19 (0 : Fin 2) 0 = 4 := by
  refine ⟨⟨1, 1, by decide, by decide⟩, by decide, ⟨0, 0, by decide, by decide⟩,
    ⟨0, 0, 0, by decide⟩, ?_, by decide, by decide, by decide⟩
  rintro ⟨a, b, c, h⟩
  exact (by decide : (1 : ℤ) + 1 + 1 ≠ 0) h

/-- The public reduction theorem applies with satisfiable size and magnitude premises. -/
example : ∃ s < 4, HasZeroTriangle (weightAB (t := 2) 3 values 19)
    (weightBC 3 s values 19) (weightAC 3 s values 19) := by
  apply (convolution_iff (t := 2) (N := 3) (x := values) (U := 9) (by decide) (by decide) ?_).mp
  · exact ⟨1, 1, by decide, by decide⟩
  · intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide

/-- A no-instance remains a no-instance; empty input is also handled. -/
example : (¬∃ s < 4, HasZeroTriangle
      (weightAB (t := 2) 3 (fun _ => 1) 3) (weightBC 3 s (fun _ => 1) 3)
      (weightAC 3 s (fun _ => 1) 3)) ∧
    (¬∃ s < 2, HasZeroTriangle
      (weightAB (t := 1) 0 (fun _ => 0) 1) (weightBC 0 s (fun _ => 0) 1)
      (weightAC 0 s (fun _ => 0) 1)) := by
  constructor
  · intro ht
    obtain ⟨i, j, _, h⟩ := (convolution_iff (t := 2) (N := 3) (x := fun _ => 1)
      (U := 1) (by decide) (by decide) (by intros; decide)).mpr ht
    exact (by decide : (1 : ℤ) + 1 ≠ 1) h
  · intro ht
    obtain ⟨i, j, h, _⟩ := (convolution_iff_sqrt (N := 0) (x := fun _ => 0)
      (U := 0) (by decide) (by intros; decide)).mpr ht
    omega

/-- Using zero filler would manufacture a false triangle out of three invalid indices. -/
example : ¬Convolution 1 (fun _ => 1) ∧ HasZeroTriangle
    (weightAB (t := 2) 1 (fun _ => 1) 0) (weightBC 1 3 (fun _ => 1) 0)
    (weightAC 1 3 (fun _ => 1) 0) := by
  constructor
  · rintro ⟨i, j, _, h⟩
    exact (by decide : (1 : ℤ) + 1 ≠ 1) h
  · exact ⟨1, 1, 1, by decide⟩

private def args (z fill : ℤ) (d : ℕ := 20) : WordRAM.Data 14 :=
  ⟨fun i => if i.val = 9 then encode z else if i.val = 10 then 3
    else if i.val = 11 then 5 else if i.val = 12 then encode fill
    else if i.val = 13 then d else 37,
    fun a => if 5 ≤ a ∧ a < 8 then encode (values (a - 5)) else 41⟩

/-- The native client starts with actual bounded words in every register and memory cell. -/
example : (args 2 (-19)).Bounded 8 := by
  constructor
  · intro i
    simp only [args, WordRAM.Fits]
    split_ifs <;> decide
  · intro a
    by_cases ha : 5 ≤ a ∧ a < 8
    · have : a = 5 ∨ a = 6 ∨ a = 7 := by omega
      rcases this with rfl | rfl | rfl <;> decide
    · simp [args, ha, WordRAM.Fits]

open Algorithms.WordRAM.ThreeSum

/-- Execute actual compiled instruction lists, with their halts charged: AB, BC and AC,
including a negative index, an invalid AC index that must retain positive filler, zero
normalization, minimum signed negation, and destination aliasing. -/
example :
    WordRAM.run 8 ((Weight.store false).program result) 50 ⟨0, args 1 19⟩ =
      some (5, 13) ∧
    WordRAM.run 8 ((Weight.store false).program result) 50 ⟨0, args (-1) 19⟩ =
      some (38, 12) ∧
    WordRAM.run 8 ((Weight.store true).program result) 50 ⟨0, args 2 (-19)⟩ =
      some (8, 26) ∧
    WordRAM.run 8 ((Weight.store true).program result) 50 ⟨0, args 4 (-19)⟩ =
      some (38, 26) ∧
    (WordRAM.Code.eval 8 0 (Weight.store true) (args (-1) 0)).map
      (fun yn => yn.1.mem 20) = some 0 ∧
    (WordRAM.Code.eval 8 0 (Weight.store true) (args (-1) (-32))).map
      (fun yn => yn.1.mem 20) = some 64 ∧
    (WordRAM.Code.eval 8 0 (Weight.store true) (args 0 (-19) 5)).map
      (fun yn => (yn.1.mem 5, yn.1.mem 6)) = some (19, 5) := by decide

/-- The public charged theorem constructs a genuine AC weight, preserves unrelated memory
and retains the argument registers. This checks the mathematical/native connection. -/
example : ∃ y, WordRAM.ExecWithin 8 (Weight.store true) (args 2 (-19)) y 28 ∧
    y.mem 20 = encode (weightAC 3 2 values 19 (0 : Fin 2) 0) ∧
    y.mem 6 = encode (-2) ∧ y.regs Weight.dest = 20 := by
  obtain ⟨y, he, hm, hr⟩ := Weight.exec_store (w := 6) (N := 3) (b := 5) (d := 20)
    (μ := values) (fill := -19) (z := 2) true (args 2 (-19))
    rfl rfl rfl rfl rfl (by
      intro i hi
      have h : 5 ≤ 5 + i ∧ 5 + i < 8 := by omega
      simp only [args, h, true_and, ↓reduceIte, Nat.add_sub_cancel_left]) (by decide) (by decide)
    (by
      intro i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl <;> decide) (by decide)
  refine ⟨y, he, ?_, ?_, hr Weight.dest (by decide)⟩
  · rw [hm]
    rfl
  · rw [hm]
    rfl

end ComplexityTests.ThreeSumConvolution
