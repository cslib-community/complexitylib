/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Int.Rectangular
meta import CslibFrontier.Computability.PolyTime.Int.Rectangular
import CslibFrontier.Foundations.LinearAlgebra.Elimination
meta import CslibFrontier.Foundations.LinearAlgebra.Elimination
import Mathlib.Tactic.NormNum

/-! Executed binary rectangular selection, consistency and rational recovery. -/

public section

open Cslib.LinearSystem Cslib.Circuits.Rational Matrix

-- Duplicate and zero rows are discarded, and original indices are preserved.
set_option linter.hashCommand false in
#guard gramRowBasis 2 [[0, 0], [1, 1], [2, 2], [0, 1]] = [3, 1]

-- A singular square can be consistent: the new test accepts it.
set_option linter.hashCommand false in
#guard rectangularConsistent 2 [[1, 1], [1, 1]] [1, 1]

set_option linter.hashCommand false in
#guard !rectangularConsistent 2 [[1, 1], [1, 1]] [1, 2]

-- The full-column-rank branch checks both consistency and Boolean coordinates.
set_option linter.hashCommand false in
#guard rectangularBoolean 2 [[1, 0], [0, -1], [1, -1]] [1, -1, 0] &&
  !rectangularBoolean 2 [[2, 0], [0, 1], [2, 1]] [1, 1, 2]

-- On deficient inputs this candidate test is deliberately not a feasibility solver:
-- x+y=1 has Boolean solutions, but its recovered minimum-norm point is (1/2,1/2).
set_option linter.hashCommand false in
#guard !rectangularBoolean 2 [[1, 1]] [1]

-- Tall, wide, rational-only, zero-width and empty systems.
set_option linter.hashCommand false in
#guard rectangularCertificate 2 [[1, 1], [2, 2]] [1, 2] = (2, [1, 1])

set_option linter.hashCommand false in
#guard rectangularConsistent 3 [[2, 0, 0], [0, -3, 0], [2, -3, 0]] [1, 1, 2]

set_option linter.hashCommand false in
#guard !rectangularConsistent 3 [[2, 0, 0], [0, -3, 0], [2, -3, 0]] [1, 1, 3]

set_option linter.hashCommand false in
#guard rectangularCertificate 3 [] [] = (1, [0, 0, 0])

set_option linter.hashCommand false in
#guard rectangularConsistent 0 [[], [999]] [0, 0] &&
  !rectangularConsistent 0 [[]] [1]

-- Ragged rows use zero padding; excess columns/RHS are ignored.
set_option linter.hashCommand false in
#guard rectangularConsistent 2 [[1], [0, 1, 999], []] [1, 2, 0, 888]

-- Large binary magnitudes and many dependent rows do not cause unary-value loops.
set_option linter.hashCommand false in
#guard rectangularConsistent 3 [[(2 : ℤ)^128, 0, 0], [0, -(2 : ℤ)^128, 0],
  [(2 : ℤ)^128, -(2 : ℤ)^128, 0]] [(2 : ℤ)^128, -(2 : ℤ)^128, 0]

set_option linter.hashCommand false in
#guard gramRowBasis 40 (List.replicate 80 (List.replicate 40 1)) = [0]

-- Check all two-column signed rows and RHS in {-1,0,1,2}. For every input,
-- compare to the existing independently proved rational elimination kernel.
set_option linter.hashCommand false in
#guard ([-1, 0, 1] : List ℤ).all fun a => [-1, 0, 1].all fun b =>
  [-1, 0, 1].all fun c => [-1, 0, 1].all fun d =>
    ([-1, 0, 1, 2] : List ℤ).all fun u => [-1, 0, 1, 2].all fun v =>
      let A := [[a, b], [c, d]]
      let rhs := [u, v]
      rectangularConsistent 2 A rhs ==
        (eliminateCached (List.finRange 2) (List.finRange 2)
          (fun i j => (Cslib.rowEntry A i j : ℚ)) (fun i => (rhs.getD i 0 : ℚ))).consistent

/-- A dependent rectangular input is accepted and yields an actual rational solution. -/
theorem rectangularBinary_dependent_solution : ∃ x : Fin 2 → ℚ,
    ∀ i : Fin 2, (fun j : Fin 2 => (Cslib.rowEntry [[1, 1], [2, 2]] i j : ℚ)) ⬝ᵥ x =
      ([1, 2] : List ℤ).getD i 0 :=
  (rectangularConsistent_correct 2 [[1, 1], [2, 2]] [1, 2]).mp (by decide)

/-- Contradictory extra rows are rejected, even though selected rows are solvable. -/
theorem rectangularBinary_inconsistent : ¬ ∃ x : Fin 2 → ℚ,
    ∀ i : Fin 2, (fun j : Fin 2 => (Cslib.rowEntry [[1, 1], [2, 2]] i j : ℚ)) ⬝ᵥ x =
      ([1, 3] : List ℤ).getD i 0 := by
  intro h
  have he := (rectangularConsistent_correct 2 [[1, 1], [2, 2]] [1, 3]).mpr h
  contradiction

/-- The selected count is the actual rank, rather than a supplied rank parameter. -/
theorem rectangularBinary_rank : Module.finrank ℚ
    (Submodule.span ℚ (Set.range (fun i : Fin 3 =>
      fun j : Fin 2 => (Cslib.rowEntry [[1, 1], [2, 2], [0, 1]] i j : ℚ)))) = 2 := by
  exact (gramRowBasis_rank 2 [[1, 1], [2, 2], [0, 1]]).symm.trans (by decide)

/-- The full-column-rank branch supplies an actual Boolean solution for a tall system. -/
theorem rectangularBinary_full_rank_boolean : ∃ x : Fin 2 → Bool,
    ∀ i : Fin 3, (∑ j : Fin 2,
      Cslib.rowEntry [[1, 0], [0, -1], [1, -1]] i j *
        (if x j then (1 : ℤ) else 0)) = ([1, -1, 0] : List ℤ).getD i 0 :=
  (rectangularBoolean_correct 2 [[1, 0], [0, -1], [1, -1]] [1, -1, 0] (by decide)).mp
    (by decide)
