/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted simple regression with an intercept

The centered numerator formulas for weighted ordinary least squares, used in
[XuGaoHu2027], equations (1) and (2). Multiplication by retained mass avoids
rational divisions when checking exact certificates. `normal_equations` verifies
both intercept and slope normal equations; a positive `xNumerator` is the
nondegeneracy condition. Zero denominators are not feasible regressions.
-/

public section

namespace Cslib.LeastSquares.Simple

open scoped BigOperators

variable {ι 𝕜 : Type*} [Fintype ι] [Field 𝕜]

/-- Total retained weight. -/
@[expose] def mass (w : ι → 𝕜) : 𝕜 := ∑ i, w i

/-- Mass times centered cross-scatter. -/
@[expose] def crossNumerator (x y w : ι → 𝕜) : 𝕜 :=
  mass w * (∑ i, w i * x i * y i) - (∑ i, w i * x i) * (∑ i, w i * y i)

/-- Mass times centered regressor scatter. -/
@[expose] def xNumerator (x w : ι → 𝕜) : 𝕜 := crossNumerator x x w

/-- Weighted OLS slope, used only when the regressor scatter is positive. -/
@[expose] def slope (x y w : ι → 𝕜) : 𝕜 := crossNumerator x y w / xNumerator x w

/-- Weighted OLS intercept, used only for positive mass and regressor scatter. -/
@[expose] def intercept (x y w : ι → 𝕜) : 𝕜 :=
  ((∑ i, w i * y i) - slope x y w * (∑ i, w i * x i)) / mass w

/-- The formulas solve both weighted normal equations, including the intercept equation. -/
theorem normal_equations (x y w : ι → 𝕜) (hm : mass w ≠ 0)
    (hv : xNumerator x w ≠ 0) :
    mass w * intercept x y w + (∑ i, w i * x i) * slope x y w = ∑ i, w i * y i ∧
    (∑ i, w i * x i) * intercept x y w +
      (∑ i, w i * x i * x i) * slope x y w = ∑ i, w i * x i * y i := by
  dsimp only [intercept, slope, xNumerator, crossNumerator] at *
  simp only [mul_assoc, ← pow_two] at *
  constructor <;> field_simp [hm, hv] <;> ring

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- For a nondegenerate design the inequality target is exactly the scatter sign test. -/
theorem slope_nonpos_iff (x y w : ι → 𝕜) (hv : 0 < xNumerator x w) :
    slope x y w ≤ 0 ↔ crossNumerator x y w ≤ 0 :=
  (div_le_iff₀ hv).trans (by simp)

end Cslib.LeastSquares.Simple
