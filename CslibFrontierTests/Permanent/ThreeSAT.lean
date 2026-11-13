/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of the #3SAT-to-permanent reduction)

import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT

/-! Concrete formulas, gadget minors and the rejection guard of Goldreich's Proposition 6.21. -/

open Cslib.Complexity Cslib.Complexity.PermanentThreeSAT Cslib.Complexity.PermanentGadget Matrix

/-- The clause gadget passes one literal track with weight `12`. -/
example : permOnList gadget (keptRows {0}) (keptCols {0}) = 12 := by
  rw [gadget_minor]; decide

/-- Mismatched literal tracks cancel. -/
example : permOnList gadget (keptRows {0}) (keptCols {1}) = 0 := by
  rw [gadget_minor]; decide

/-- The gadget alone, with no track passing, has permanent `0`. -/
example : permOnList gadget (keptRows ∅) (keptCols ∅) = 0 := by
  rw [gadget_minor]; decide

/-- One variable and one clause `x₀`: nine vertices, permanent `12 · 1`. -/
example : (cnfToPermanentTable [[(0, true)]]).length = 9 := by decide

example : IntPermanent (cnfToPermanentTable [[(0, true)]]) = 12 := by
  rw [intPermanent_cnfToPermanentTable]; decide

/-- The contradictory formula `x₀ ∧ ¬x₀` has permanent `0`, with two clause gadgets. -/
example : IntPermanent (cnfToPermanentTable [[(0, true)], [(0, false)]]) = 0 := by
  rw [intPermanent_cnfToPermanentTable]; decide

/-- The track from the auxiliary vertex of `x₀` enters the first occurrence of `x₀`, and the
negative track, without occurrences, is a self-loop. -/
example : matrixEntry [[(0, true)]] 0 1 = 1 ∧ matrixEntry [[(0, true)]] 0 0 = 1 := by decide

/-- An empty clause or a clause of four literals is rejected to the zero matrix. -/
example : cnfToPermanentTable [[]] = [[0]] := by decide

example : cnfToPermanentTable [[(0, true), (1, true), (2, true), (3, true)]] = [[0]] := by decide

/-- Every entry of a concrete matrix lies in `{-1, 0, 1, 2, 3}`, even with a repeated literal. -/
example : ∀ row ∈ cnfToPermanentTable [[(0, true), (0, true), (1, false)]], ∀ x ∈ row,
    x ∈ ({-1, 0, 1, 2, 3} : Finset ℤ) :=
  mem_entries_cnfToPermanentTable _
