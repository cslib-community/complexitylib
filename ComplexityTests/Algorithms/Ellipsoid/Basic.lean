/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Ellipsoid.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Tests for ellipsoids and the central-cut ellipsoid method

The unit ellipsoid is the unit ball, contains its center and misses `(2, 0)`. Ellipsoids with
positive definite shape have positive finite volume, so the volume bounds are not vacuous. In
dimension one a central cut of `[-1, 1]` is bisection: shape `1 / 4`, center `-1 / 2`. The ball
`{x | (x - z) ⬝ᵥ (x - z) ≤ r ^ 2}` has a strong separation oracle cutting with normal `x - z`; it
answers `none` at the center and cuts at a point outside, and the ball sandwich theorem with it
finds a point of any unit disk `B(z, 1)` with `z ⬝ᵥ z ≤ 1` within `9` steps from the disk of radius
`2` about the origin.
-/

@[expose] public section

namespace Cslib.Algorithms.EllipsoidTests

open Matrix Cslib.Algorithms.Ellipsoid MeasureTheory

/-! ### The geometric step -/

/-- The center lies in its ellipsoid. -/
example : (0 : Fin 2 → ℝ) ∈ ellipsoid (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 :=
  center_mem_ellipsoid _ _

/-- The unit ellipsoid is the closed unit ball. -/
example : ellipsoid (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 = {x | x ⬝ᵥ x ≤ 1} := by
  simpa using ellipsoid_sq_smul_one (ι := Fin 2) one_ne_zero 0

/-- A point outside the unit ball is not in the unit ellipsoid. -/
example : (![2, 0] : Fin 2 → ℝ) ∉ ellipsoid (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 := by
  rw [mem_ellipsoid]
  simp [dotProduct, Fin.sum_univ_two]
  norm_num

/-- Ellipsoids with positive definite shape have positive finite volume, so the volume bounds are
not vacuous. -/
example : 0 < volume (ellipsoid (1 : Matrix (Fin 3) (Fin 3) ℝ) 0) ∧
    volume (ellipsoid (1 : Matrix (Fin 3) (Fin 3) ℝ) 0) < ⊤ :=
  ⟨volume_ellipsoid_pos PosDef.one 0, volume_ellipsoid_lt_top PosDef.one 0⟩

/-- In dimension one a central cut halves the interval: the shape is divided by `4`. -/
example : centralCutShape (1 : Matrix (Fin 1) (Fin 1) ℝ) ![1] = (1 / 4 : ℝ) • 1 :=
  centralCutShape_of_card_eq_one PosDef.one (by simp) rfl

/-- In dimension one, cutting `[-1, 1]` with normal `1` keeps `[-1, 0]`, centered at `-1 / 2`. -/
example : centralCutCenter (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 ![1] = ![-1 / 2] := by
  ext i
  fin_cases i
  simp [centralCutCenter, centralCutDir, dotProduct]
  norm_num

/-- The volume shrinks under a central cut in the plane. -/
example : volume (ellipsoid (centralCutShape (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0])
      (centralCutCenter 1 0 ![1, 0])) <
    ENNReal.ofReal (Real.exp (-1 / (2 * ((Fintype.card (Fin 2) : ℝ) + 1)))) *
      volume (ellipsoid (1 : Matrix (Fin 2) (Fin 2) ℝ) 0) :=
  volume_ellipsoid_centralCut_lt PosDef.one (by simp) 0

/-! ### A strong separation oracle for a ball -/

/-- The separation oracle for the ball `{x | (x - z) ⬝ᵥ (x - z) ≤ r ^ 2}`: cut with normal
`x - z` at points outside. -/
noncomputable def ballSep {ι : Type*} [Fintype ι] (z : ι → ℝ) (r : ℝ) (x : ι → ℝ) :
    Option (ι → ℝ) :=
  open Classical in if (x - z) ⬝ᵥ (x - z) ≤ r ^ 2 then none else some (x - z)

theorem isStrongSeparationOracle_ballSep {ι : Type*} [Fintype ι] (z : ι → ℝ) (r : ℝ) :
    IsStrongSeparationOracle {x | (x - z) ⬝ᵥ (x - z) ≤ r ^ 2} (ballSep z r) where
  mem_of_eq_none {x} h := by
    unfold ballSep at h
    split_ifs at h with hx
    exact hx
  ne_zero_of_eq_some {x a} h := by
    unfold ballSep at h
    split_ifs at h with hx
    cases h
    intro h0
    rw [h0, zero_dotProduct] at hx
    exact hx (sq_nonneg r)
  separates {x a} h y hy := by
    unfold ballSep at h
    split_ifs at h with hx
    cases h
    rw [Set.mem_ofPred_eq] at hy
    have key (u w : ι → ℝ) (h : w ⬝ᵥ w < u ⬝ᵥ u) : u ⬝ᵥ w < u ⬝ᵥ u := by
      have hnn := dotProduct_star_self_nonneg (u - w)
      simp only [star_trivial, sub_dotProduct, dotProduct_sub, dotProduct_comm w u] at hnn
      linarith
    have := key (x - z) (y - z) (by linarith [not_le.mp hx])
    have hyx : (x - z) ⬝ᵥ y = (x - z) ⬝ᵥ (y - z) + (x - z) ⬝ᵥ z := by
      rw [dotProduct_sub]; ring
    have hxx : (x - z) ⬝ᵥ x = (x - z) ⬝ᵥ (x - z) + (x - z) ⬝ᵥ z := by
      rw [dotProduct_sub]; ring
    rw [hyx, hxx]
    linarith

/-- The oracle answers `none` at the center of the ball. -/
example : ballSep (0 : Fin 2 → ℝ) 1 0 = none := by
  simp [ballSep]

/-- At a point outside the ball the oracle cuts, and the method moves the center. -/
example : run (ballSep (![3] : Fin 1 → ℝ) 1) 1 0 1 =
    ⟨centralCutShape 1 (0 - ![3]), centralCutCenter 1 0 (0 - ![3])⟩ := by
  rw [run_succ, run_zero, step_of_eq_some]
  simp [ballSep, dotProduct]
  norm_num

/-- The iteration bound is not vacuous: started from the ball of radius `2` about the origin, the
method finds a point of any unit ball `B(z, 1)` with `z ⬝ᵥ z ≤ 1` in the plane within `9` steps,
since `2 · 2 · 3 · ln 2 < 9`. -/
example (z : Fin 2 → ℝ) (hz : z ⬝ᵥ z ≤ 1) :
    (run (ballSep z 1) ((2 ^ 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 9).center ∈
      {x | (x - z) ⬝ᵥ (x - z) ≤ 1 ^ 2} := by
  refine center_mem_of_ball_subset (isStrongSeparationOracle_ballSep z 1) one_pos two_pos
    subset_rfl (fun x hx => ?_) ?_
  · rw [Set.mem_ofPred_eq] at hx ⊢
    have hnn := dotProduct_star_self_nonneg ((x - z) - z)
    simp only [star_trivial, sub_dotProduct, dotProduct_sub, sub_zero] at hnn hx ⊢
    rw [dotProduct_comm z x] at hnn hx
    nlinarith
  · simp only [Fintype.card_fin, div_one]
    have := Real.log_two_lt_d9
    push_cast
    linarith

end Cslib.Algorithms.EllipsoidTests
