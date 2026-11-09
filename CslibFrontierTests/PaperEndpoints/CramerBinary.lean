/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Int.Cramer
meta import CslibFrontier.Computability.PolyTime.Int.Cramer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Executed binary Cramer certificates and exact Boolean feasibility. -/

public section

open Cslib.LinearSystem Cslib.Circuits.Rational Matrix

-- These runtime regressions deliberately execute the binary-certified program.
set_option linter.hashCommand false in
#guard cramerCertificate [[2, 1], [1, -1]] [3, 0] = (-3, [-3, -3])

set_option linter.hashCommand false in
#guard cramerBoolean [[2, 1], [1, -1]] [3, 0]

set_option linter.hashCommand false in
#guard !cramerBoolean [[2, 1], [1, -1]] [1, 0]

-- Singular input can have Boolean solutions, but belongs to the other branch.
set_option linter.hashCommand false in
#guard !cramerBoolean [[1, 1], [1, 1]] [1, 1]

set_option linter.hashCommand false in
#guard cramerCertificate [] [] = (1, []) && cramerBoolean [] []

-- Signs and large binary values do not trigger unary enumeration of magnitudes.
set_option linter.hashCommand false in
#guard cramerBoolean [[(2 : ℤ)^128, 0], [0, -(2 : ℤ)^128]] [(2 : ℤ)^128, -(2 : ℤ)^128]

-- Input normalization is part of the public semantics.
set_option linter.hashCommand false in
#guard cramerCertificate [[1, 999]] [1, 888] = (1, [1])

set_option linter.hashCommand false in
#guard !cramerBoolean [[]] []

-- Exhaustively compare all nonsingular signed two-variable systems with RHS in
-- {-1,0,1,2} against direct Boolean checking (81 matrices times 16 RHS vectors).
set_option linter.hashCommand false in
#guard ([-1, 0, 1] : List ℤ).all fun a => [-1, 0, 1].all fun b =>
  [-1, 0, 1].all fun c => [-1, 0, 1].all fun d =>
    ([-1, 0, 1, 2] : List ℤ).all fun u => [-1, 0, 1, 2].all fun v =>
      let A := [[a, b], [c, d]]
      detRows A == 0 ||
        (cramerBoolean A [u, v] == ([0, 1] : List ℤ).any fun x =>
          [0, 1].any fun y => a*x+b*y == u && c*x+d*y == v)

/-- The nonsingular Boolean test yields an actual solution of the input equations. -/
theorem cramerBinary_checked_solution : ∃ x : Fin 2 → Bool,
    ∀ i : Fin 2, (∑ j : Fin 2,
      rowEntry [[2, 1], [1, -1]] i j * (if x j then (1 : ℤ) else 0)) =
        ([3, 0] : List ℤ).getD i 0 := by
  exact (cramerBoolean_correct [[2, 1], [1, -1]] [3, 0] (by decide)).mp (by decide)

/-- A rational-only solution is rejected: the equations force both coordinates to 1/3. -/
theorem cramerBinary_checked_rejection : ¬ ∃ x : Fin 2 → Bool,
    ∀ i : Fin 2, (∑ j : Fin 2,
      rowEntry [[2, 1], [1, -1]] i j * (if x j then (1 : ℤ) else 0)) =
        ([1, 0] : List ℤ).getD i 0 := by
  intro h
  have he := (cramerBoolean_correct [[2, 1], [1, -1]] [1, 0] (by decide)).mpr h
  contradiction
