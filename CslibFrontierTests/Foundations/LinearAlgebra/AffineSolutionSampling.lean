/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.LinearAlgebra.AffineSolutionSampling
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Tests for affine solution sampling and retries

The map `(x₀, x₁) ↦ x₀ + x₁` over `ZMod 2` is surjective and underdetermined. A
nonzero shift changes the solver's canonical solution while preserving the target. The retry client
first presents a zero map, which must fail despite its zero target being consistent, then the sum
map, which succeeds. The returned pair retains the successful attempt tag; two zero-map attempts
exercise bounded all-attempts failure.
-/

public section

namespace Cslib.LinearAlgebra.AffineSolutionSamplingTests

open Cslib.LinearAlgebra

abbrev F := ZMod 2
abbrev Input := Fin 2 → F
abbrev Output := Fin 1 → F

/-- The underdetermined map `(x₀, x₁) ↦ x₀ + x₁`. -/
def sumMap : Input →ₗ[F] Output where
  toFun x := fun _ ↦ x 0 + x 1
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- A canonical solver for `sumMap`, setting its second coordinate to zero. -/
def sumSolver : AffineSolutionSolver sumMap where
  solve y := some fun i ↦ if i = 0 then y 0 else 0
  map_eq_of_solve_eq_some := by
    intro y x h
    rw [Option.some.injEq] at h
    subst x
    funext i
    fin_cases i
    simp [sumMap]
  solve_eq_none_iff_not_surjective y := by
    simp only [Option.some_ne_none, false_iff, not_not]
    intro z
    refine ⟨(fun i ↦ if i = 0 then z 0 else 0), ?_⟩
    funext i
    fin_cases i
    simp [sumMap]

/-- A nonsurjective zero map, used to exercise mandatory failure on a consistent target. -/
def zeroMap : Input →ₗ[F] Output := 0

/-- The source-shaped solver contract for `zeroMap`: every target is rejected because the map is
not surjective. -/
def zeroSolver : AffineSolutionSolver zeroMap where
  solve _ := none
  map_eq_of_solve_eq_some := by simp
  solve_eq_none_iff_not_surjective _ := by
    constructor
    · intro _ hsurj
      obtain ⟨x, hx⟩ := hsurj fun _ ↦ 1
      have hx0 := congrFun hx 0
      simpa [zeroMap] using hx0
    · intro _
      rfl

/-- A nonzero shift for the underdetermined system. -/
def shift : Input := ![1, 1]

/-- The target used by the successful attempt. -/
def oneTarget : Output := fun _ ↦ 1

/-- Shifting changes the canonical solution from `(1, 0)` to `(0, 1)`. -/
example : sumSolver.sampleSolution oneTarget shift = some ![0, 1] := by
  decide +kernel

/-- The shifted result still solves the original affine system. -/
example : sumMap ![0, 1] = oneTarget := by
  decide +kernel

inductive Attempt where
  | rankDeficient
  | fullRank
  deriving DecidableEq

/-- Each attempt carries its own linear system. -/
def system : Attempt → Input →ₗ[F] Output
  | .rankDeficient => zeroMap
  | .fullRank => sumMap

/-- Solver contracts for the two attempt systems. -/
def solver : (a : Attempt) → AffineSolutionSolver (system a)
  | .rankDeficient => zeroSolver
  | .fullRank => sumSolver

/-- Targets remain explicit per attempt; the rank-deficient attempt is consistent but must fail. -/
def target : Attempt → Output
  | .rankDeficient => 0
  | .fullRank => oneTarget

/-- Randomness remains explicit per attempt. -/
def randomness : Attempt → Input
  | .rankDeficient => ![1, 0]
  | .fullRank => shift

/-- Retry skips the consistent but rank-deficient system, returns the next solution, and retains
the successful attempt tag. -/
example : retrySampleSolution [.rankDeficient, .fullRank]
    system solver target randomness = some (.fullRank, ![0, 1]) := by
  decide +kernel

/-- A bounded list with no surjective system reports failure. -/
example : retrySampleSolution [.rankDeficient, .rankDeficient]
    system solver target randomness = none := by
  decide +kernel

end Cslib.LinearAlgebra.AffineSolutionSamplingTests
