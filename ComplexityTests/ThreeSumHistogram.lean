/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Count

/-! # Executed histogram and residue-array regressions -/

namespace ComplexityTests.ThreeSumHistogram

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM

private def keys (i : ℕ) : ℕ := [0, 1, 0, 0].getD i 0

private def input : Data 11 :=
  (((Data.init [0, 1, 0, 0]).set Histogram.src 1).set Histogram.dst 10).set Histogram.len 4
    |>.set Histogram.bins 3

/-- Clearing ignores the old contents, including nonzero words in the output block. -/
example : (Code.eval 8 4 Histogram.program (input.write 10 77)).map
    (fun yn => (yn.1.mem 10, yn.1.mem 11, yn.1.mem 12, yn.1.regs Histogram.total, yn.2)) =
      some (3, 1, 0, 6, 68) := by decide

/-- Read the same result through the generic charged theorem, checking both frames. -/
example : ∃ y, ExecWithin 8 Histogram.program input y 68 ∧
    y.mem 10 = 3 ∧ y.mem 11 = 1 ∧ y.regs Histogram.total = 6 ∧
    y.mem 0 = 4 ∧ y.mem 13 = 0 := by
  obtain ⟨y, hy, hm, ht, _⟩ := Histogram.exec (w := 8) input keys
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by
      intro i hi
      change i < 4 at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide)
    (by
      intro i hi
      change i < 4 at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide)
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; decide
  · rw [hm]; decide
  · rw [ht]; decide
  · rw [hm]; decide
  · rw [hm]; decide

/-- Empty inputs and empty histograms pay only setup and two failed loop tests. -/
example : (Code.eval 8 0 Histogram.program
    ((input.set Histogram.len 0).set Histogram.bins 0)).map
      (fun yn => (yn.1.regs Histogram.total, yn.2)) = some (0, 9) := by decide

/-- A singleton has no collision; two equal keys at different positions create two. -/
example : Histogram.pairs (fun _ => 0) 0 = 0 ∧
    Histogram.pairs (fun _ => 0) 1 = 0 ∧ Histogram.pairs (fun _ => 0) 2 = 2 := by decide

/-- Different keys create no collision. -/
example : Histogram.pairs id 4 = 0 := by decide

private def values (i : ℕ) : ℤ := [-5, -2, 1, 4].getD i 0

private def signedInput : Data 16 :=
  (((Data.init ([-5, -2, 1, 4].map encode)).set ThreeSum.ChanHe.Residues.src 1).set
    ThreeSum.ChanHe.Residues.dst 10).set ThreeSum.ChanHe.Residues.len 4
    |>.set ThreeSum.ChanHe.Residues.modulus (encode 3)

/-- Negative dividends use Euclidean residues, and the outputs are decoded unsigned keys. -/
example : (Code.eval 8 4 ThreeSum.ChanHe.Residues.program signedInput).map
    (fun yn => (List.range 4).map fun i => yn.1.mem (10 + i)) = some [1, 1, 1, 1] := by decide

/-- The signed-array contract has satisfiable hypotheses on the executed negative input. -/
example : ∃ y, ExecWithin 8 ThreeSum.ChanHe.Residues.program signedInput y 96 ∧
    y.mem 10 = 1 ∧ y.mem 13 = 1 ∧ y.mem 1 = encode (-5) ∧ y.mem 14 = 0 := by
  obtain ⟨y, hy, hm, _⟩ := ThreeSum.ChanHe.Residues.exec (w := 6) (M := 3)
    signedInput values (by decide) (by decide) rfl
    (by
      intro i hi
      change i < 4 at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide)
    (by
      intro i hi
      change i < 4 at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide)
  refine ⟨y, hy, ?_, ?_, ?_, ?_⟩ <;> rw [hm] <;> decide

/-- The existing mathematical collision count agrees with the histogram's counter. -/
example : Cslib.Algorithms.ThreeSum.ChanHe.coll {-5, -2, 1, 4} 3 = 12 ∧
    Histogram.pairs (fun i => (values i % 3).toNat) 4 = 12 := by decide

private def countInput : Data 28 :=
  (((((Data.init ([-5, -2, 1, 4].map encode)).set ThreeSum.ChanHe.Count.src 1).set
    ThreeSum.ChanHe.Count.scratch 10).set ThreeSum.ChanHe.Count.len 4).set
    ThreeSum.ChanHe.Count.modulus (encode 3)).set ThreeSum.ChanHe.Count.dst 20

-- Evaluating the three renamed loops unfolds over 150 native instructions and their register maps.
set_option maxRecDepth 4096 in
/-- Execute the composed signed-input program and check its unsigned count and both arrays. -/
example : (Code.eval 8 4 ThreeSum.ChanHe.Count.program countInput).map
    (fun yn => [yn.1.mem 1, yn.1.mem 10, yn.1.mem 13, yn.1.mem 20, yn.1.mem 21,
      yn.1.mem 22, yn.1.regs ThreeSum.ChanHe.Count.total]) =
        some [encode (-5), 1, 1, 0, 4, 0, 12] := by decide

/-- The full composed contract is admissible for the same negative-input example. -/
example : ∃ y, ExecWithin 8 ThreeSum.ChanHe.Count.program countInput y 169 ∧
    y.regs ThreeSum.ChanHe.Count.total = 12 ∧ y.mem 21 = 4 ∧ y.mem 1 = encode (-5) ∧
      ∀ i, ((9 ≤ i.val ∧ i.val ≤ 12) ∨ i = ThreeSum.ChanHe.Count.dst) →
        y.regs i = countInput.regs i := by
  obtain ⟨y, hy, hm, ht, hframe⟩ := ThreeSum.ChanHe.Count.exec (w := 6) (M := 3)
    countInput values (by decide) (by decide) rfl
    (by
      intro i hi
      change i < 4 at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by
      intro i hi
      change i < 4 at hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide)
  refine ⟨y, hy, ?_, ?_, ?_, hframe⟩
  · rw [ht]; decide
  · rw [hm]; decide
  · rw [hm]; decide

-- The three complete program evaluations unfold the renamed loops and register maps.
set_option maxRecDepth 4096 in
/-- The composed program handles lengths zero, one and two, including an unused modulus block. -/
example : ((Code.eval 8 3 ThreeSum.ChanHe.Count.program
      (countInput.set ThreeSum.ChanHe.Count.len 0)).map
        (fun yn => yn.1.regs ThreeSum.ChanHe.Count.total)) = some 0 ∧
    ((Code.eval 8 3 ThreeSum.ChanHe.Count.program
      (countInput.set ThreeSum.ChanHe.Count.len 1)).map
        (fun yn => yn.1.regs ThreeSum.ChanHe.Count.total)) = some 0 ∧
    ((Code.eval 8 3 ThreeSum.ChanHe.Count.program
      (countInput.set ThreeSum.ChanHe.Count.len 2)).map
        (fun yn => yn.1.regs ThreeSum.ChanHe.Count.total)) = some 2 := by decide

/-- Equal integer values violate the set-enumeration premise, even at different positions. -/
example : ¬Set.InjOn (fun _ : ℕ => (-1 : ℤ)) (↑(Finset.range 2) : Set ℕ) := by
  intro h
  have := h (by decide : 0 ∈ (↑(Finset.range 2) : Set ℕ))
    (by decide : 1 ∈ (↑(Finset.range 2) : Set ℕ)) rfl
  omega

end ComplexityTests.ThreeSumHistogram
