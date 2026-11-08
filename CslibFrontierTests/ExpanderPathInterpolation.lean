/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Expander.PathInterpolation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Clients of path elimination

The clients specialize elimination to a three-edge path with angle π/6 and to a four-edge
affine path, and give a finite perturbation budget. The final example constructs a nonzero
Dirichlet mode at a resonant angle, checking that the nonresonance hypothesis matters.
-/

namespace ComplexityTests.ExpanderPathInterpolation

open Cslib.ExpanderPath

-- At total angle π/2, the endpoint correction has coefficient exactly one half.
example (x : ℕ → ℝ) (a b : ℝ) (hx : Recurrence 3 (Real.cos (Real.pi / 6)) x)
    (hzero : x 0 = a) (hlength : x 3 = b) :
    x 1 = (Real.sqrt 3 / 2) * a + b / 2 := by
  have hangle : (3 : ℝ) * (Real.pi / 6) = Real.pi / 2 := by ring
  have hSin : Real.sin ((3 : ℝ) * (Real.pi / 6)) ≠ 0 := by
    rw [hangle, Real.sin_pi_div_two]
    norm_num
  have h := hx.first_eq hSin
  rw [hzero, hlength] at h
  norm_num only [Nat.cast_ofNat, hangle, Real.sin_pi_div_two, Real.cos_pi_div_two,
    Real.sin_pi_div_six, Real.cos_pi_div_six] at h
  linarith

-- The parameter-one endpoint has an affine, rather than a sine-quotient, formula.
example (x : ℕ → ℝ) (a b : ℝ) (hx : Recurrence 4 1 x)
    (hzero : x 0 = a) (hlength : x 4 = b) :
    x 1 = (3 * a + b) / 4 ∧ x 2 = (a + b) / 2 := by
  constructor
  · have h := hx.first_eq_of_one (by decide)
    rw [hzero, hlength] at h
    norm_num at h
    linarith
  · have h := hx.eq_affine (by decide) 2 (by decide)
    rw [hzero, hlength] at h
    norm_num at h
    linarith

-- A length-ten path with θ = 1/10 has a concrete symbolic perturbation budget.
example :
    2 * (Real.sin (1 / 10) / Real.sin 1) + 3 * (1 - Real.cos (1 / 10)) ≤
      1 / (5 * Real.sin 1) + 3 / 200 := by
  have h := perturbationBudget_le (L := 10) (θ := 1 / 10) (τ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.two_le_pi])
  norm_num at h
  convert h using 1
  ring

-- At a Dirichlet resonance, zero endpoints do not force the interior value to vanish.
example : ∃ x : ℕ → ℝ,
    Recurrence 2 (Real.cos (Real.pi / 2)) x ∧ x 0 = 0 ∧ x 2 = 0 ∧ x 1 ≠ 0 ∧
      Real.sin ((2 : ℝ) * (Real.pi / 2)) = 0 := by
  refine ⟨fun j => if j = 1 then 1 else 0, ?_, by norm_num, by norm_num,
    by norm_num, ?_⟩
  · intro j hj
    have hjzero : j = 0 := by omega
    subst j
    norm_num [Real.cos_pi_div_two]
  · have hangle : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
    rw [hangle, Real.sin_pi]

end ComplexityTests.ExpanderPathInterpolation
