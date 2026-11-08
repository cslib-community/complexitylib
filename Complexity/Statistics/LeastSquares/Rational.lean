/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Simple
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Basic.Real.Basic

/-!
# Exact rational certificates for real simple regression

The weighted mass, scatter numerators and OLS slope commute with the rational
embedding into the reals. These bridges let exact finite certificates establish
claims about the actual real regression, rather than a different rational model.
-/

public section

namespace Cslib.LeastSquares.Simple

variable {ι : Type*} [Fintype ι]

/-- Rational retention indicators, before embedding into the real regression. -/
@[expose] def keep [DecidableEq ι] (s : Finset ι) (i : ι) : ℚ := if i ∈ s then 1 else 0

/-- Embed a rational vector into the reals. -/
@[expose] def realVector (v : ι → ℚ) (i : ι) : ℝ := v i

/-- The retained mass is preserved by the rational embedding. -/
theorem mass_realVector (w : ι → ℚ) : mass (realVector w) = ((mass w : ℚ) : ℝ) := by
  simp [mass, realVector]

/-- Cross-scatter certificates transfer from rational to real weights and observations. -/
theorem crossNumerator_realVector (x y w : ι → ℚ) :
    crossNumerator (realVector x) (realVector y) (realVector w) =
      ((crossNumerator x y w : ℚ) : ℝ) := by
  simp [crossNumerator, mass, realVector]

/-- Regressor-scatter certificates transfer from rational to real weights and observations. -/
theorem xNumerator_realVector (x w : ι → ℚ) :
    xNumerator (realVector x) (realVector w) = ((xNumerator x w : ℚ) : ℝ) := by
  simp [xNumerator, crossNumerator, mass, realVector]

/-- The exact rational slope is the actual real least-squares slope. -/
theorem slope_realVector (x y w : ι → ℚ) :
    slope (realVector x) (realVector y) (realVector w) = ((slope x y w : ℚ) : ℝ) := by
  simp [slope, crossNumerator_realVector, xNumerator_realVector]

/-- Integral retention has mass equal to retained cardinality. -/
theorem mass_keep [DecidableEq ι] (s : Finset ι) : mass (keep s) = s.card := by
  simp [mass, keep]

end Cslib.LeastSquares.Simple
