/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A least-squares optimum that is not a lifted-plane range

Theorem 5.4 of [XuGaoHu2027] (PDF p. 12, printed p. 10) concerns six explicit
rational observations and retained subsets of cardinality four. `scatter` is precisely
$F(S)=\sum xy-(\sum x)(\sum y)/|S|$, the centered cross-scatter, not a
positive definite covariance determinant. `planeValue` evaluates an arbitrary real
plane on the saddle lift $(x,y,xy)$, including its constant term.

The finite comparisons and general-position certificates use kernel computation.
The nonseparation result quantifies over all real plane coefficients and follows from
the source's exact affine dependence. No floating-point computation is used.
This endpoint does not assert the paper's general rounding or audit algorithms.

## Main definitions

* `point`, `retained`, `scatter`: the exact rational instance and centered cross-scatter.
* `planeValue`, `IsRange`: real affine-plane evaluation and its selected finite range.

## Main results

* `nonrange_optimum`: the explicit unique optimum is not selected by any lifted plane.

## References

* [XuGaoHu2027], Theorem 5.4, PDF p. 12 (printed p. 10).
-/

public section

namespace Cslib.LeastSquares.NonRange

/-- The six observations in the order used in the source. -/
@[expose] def point (i : Fin 6) : ℚ × ℚ :=
  ![(-163/100, 34/100), (77/100, -64/100), (-37/100, 40/100),
    (85/100, -28/100), (-74/100, 231/100), (235/100, -70/100)] i

/-- The centered cross-scatter of a retained set. -/
@[expose] def scatter (s : Finset (Fin 6)) : ℚ :=
  (∑ i ∈ s, (point i).1 * (point i).2) -
    (∑ i ∈ s, (point i).1) * (∑ i ∈ s, (point i).2) / s.card

/-- The proposed unique minimizer (indices here are zero based). -/
@[expose] def retained : Finset (Fin 6) := {1, 2, 4, 5}

/-- Oriented volume of four saddle lifts; nonzero means affine independence. -/
@[expose] def volume (i j k l : Fin 6) : ℚ :=
  let x := fun t => (point t).1 - (point i).1
  let y := fun t => (point t).2 - (point i).2
  let z := fun t => (point t).1 * (point t).2 - (point i).1 * (point i).2
  x j * (y k * z l - z k * y l) - y j * (x k * z l - z k * x l) +
    z j * (x k * y l - y k * x l)

/-- Distinct regressors, and all fifteen four-lift determinants are nonzero. -/
theorem general_position :
    (∀ i j, (point i).1 = (point j).1 → i = j) ∧
    (∀ i j k l, i < j → j < k → k < l → volume i j k l ≠ 0) := by
  decide +kernel

/-- Exhaustive comparison of the fifteen retained four-sets, with the exact runner-up gap. -/
theorem unique_minimum :
    retained.card = 4 ∧ scatter retained = -37469/8000 ∧
    (∀ s : Finset (Fin 6), s.card = 4 → s ≠ retained →
      -185881/40000 ≤ scatter s) ∧
    (∃ s : Finset (Fin 6), s.card = 4 ∧ s ≠ retained ∧ scatter s = -185881/40000) := by
  decide +kernel

/-- Evaluation of an arbitrary real affine plane on a saddle lift. -/
@[expose] noncomputable def planeValue (c : Fin 4 → ℝ) (i : Fin 6) : ℝ :=
  c 0 * ((point i).1 : ℝ) * ((point i).2 : ℝ) +
    c 1 * ((point i).1 : ℝ) + c 2 * ((point i).2 : ℝ) + c 3

/-- Membership in a strict lifted-plane range, allowing boundary points outside the range. -/
@[expose] def IsRange (s : Finset (Fin 6)) : Prop :=
  ∃ c : Fin 4 → ℝ, ∀ i, i ∈ s ↔ planeValue c i < 0

/-- The source's affine dependence, including the homogeneous coordinate. -/
theorem affine_dependence (c : Fin 4 → ℝ) :
    -33151858 * planeValue c 0 + 62875533 * planeValue c 1 +
    63139684 * planeValue c 2 - 92961567 * planeValue c 3 +
    98208 * planeValue c 4 = 0 := by
  norm_num [planeValue, point]
  ring

/-- No real plane cuts out the unique minimizing retained set. -/
theorem not_range : ¬ IsRange retained := by
  rintro ⟨c, hc⟩
  have h0 : 0 ≤ planeValue c 0 := le_of_not_gt fun h => by
    have := (hc 0).mpr h
    norm_num [retained] at this
  have h3 : 0 ≤ planeValue c 3 := le_of_not_gt fun h => by
    have := (hc 3).mpr h
    norm_num [retained] at this
  have h1 : planeValue c 1 < 0 := (hc 1).mp (by decide)
  have h2 : planeValue c 2 < 0 := (hc 2).mp (by decide)
  have h4 : planeValue c 4 < 0 := (hc 4).mp (by decide)
  have := affine_dependence c
  linarith

/-- The complete selected endpoint: general position and a unique, non-range optimum. -/
theorem nonrange_optimum :
    (∀ i j, (point i).1 = (point j).1 → i = j) ∧
    (∀ i j k l, i < j → j < k → k < l → volume i j k l ≠ 0) ∧
    retained.card = 4 ∧
    (∀ s : Finset (Fin 6), s.card = 4 → s ≠ retained → scatter retained < scatter s) ∧
    ¬ IsRange retained := by
  refine ⟨general_position.1, general_position.2, unique_minimum.1, ?_, not_range⟩
  intro s hs hne
  have := unique_minimum.2.2.1 s hs hne
  rw [unique_minimum.2.1]
  linarith

end Cslib.LeastSquares.NonRange
