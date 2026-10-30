/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Frontier.TensorNetwork.IntegralCoordinates
import Complexity.Foundations.NumberTheory.Padics.RatValuation

/-!
# Tests for the integral local coordinates of the Cauchy kernel

With `L = 2` slots the grid is `{-2, -1, 0, 1}`, `C'(0) = -2` and `α = 4`. The kernel at `1` is
`-(T + 2) (T + 1) T / 2`, whose leading coefficient `-1/2` is not `2`-integral; in the local
coordinate `T = 1 + 4 z` it becomes `2`-integral (Lemma D.4).
-/

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.IntegralCoordinates

open Cslib.Circuits.Frontier Polynomial
open scoped WithZero

/-- The grid of two slots. -/
theorem cauchyGrid_two : cauchyGrid 2 = {-2, -1, 0, 1} := by decide

/-- The leading coefficient of the kernel is `C'(0)⁻¹ = -1/2`. -/
theorem coeff_cauchyKernel_two_one : (cauchyKernel 2 1).coeff 3 = -1 / 2 := by
  have hmem : (1 : ℤ) ∈ cauchyGrid 2 := by decide
  have hdeg := natDegree_cauchyKernel hmem
  have hlead : (cauchyKernel 2 1).leadingCoeff =
      ((Lagrange.nodal ((cauchyGrid 2).erase 0) (Int.cast : ℤ → ℚ)).eval 0)⁻¹ := by
    rw [cauchyKernel, leadingCoeff_mul, leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff,
      mul_one]
  rw [leadingCoeff, hdeg] at hlead
  rw [show 3 = 2 * 2 - 1 from rfl, hlead, Lagrange.eval_nodal, cauchyGrid_two]
  rw [show ({-2, -1, 0, 1} : Finset ℤ).erase 0 = {-2, -1, 1} by decide]
  simp only [Finset.prod_insert (by decide : (-2 : ℤ) ∉ ({-1, 1} : Finset ℤ)),
    Finset.prod_insert (by decide : (-1 : ℤ) ∉ ({1} : Finset ℤ)), Finset.prod_singleton]
  norm_num

theorem padicValRat_two : padicValRat 2 (2 : ℚ) = 1 := by
  exact_mod_cast padicValRat.self (p := 2) one_lt_two

/-- **The kernel itself is not `2`-integral**: its leading coefficient `-1/2` has a `2` in the
denominator. -/
example : cauchyKernel 2 1 ∉ lifts (Rat.padicValuation 2).integer.subtype := by
  rw [lifts_iff_coeff_lifts]
  intro h
  obtain ⟨c, hc⟩ := h 3
  have hle := c.2
  rw [Valuation.mem_integer_iff] at hle
  change Rat.padicValuation 2 (c : ℚ) ≤ 1 at hle
  have hv : Rat.padicValuation 2 (-1 / 2 : ℚ) = WithZero.exp 1 := by
    rw [neg_div, Valuation.map_neg]
    simp [Rat.padicValuation, padicValRat_two]
  rw [show (c : ℚ) = -1 / 2 by rw [← coeff_cauchyKernel_two_one]; exact hc, hv,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  exact absurd hle (by norm_num)

/-- **In the local coordinate `T = 1 + 4 z` it is `2`-integral** (Lemma D.4, with `a = 1`). -/
example :
    (cauchyKernel 2 1).comp (C 1 + C 4 * X) ∈ lifts (Rat.padicValuation 2).integer.subtype := by
  have h := cauchyKernel_comp_mem_lifts (a := 1) (t := 1) (d := 1) (by decide) (by decide)
  norm_num at h
  exact h

/-- Away from its own node the kernel in local coordinates is divisible by `2`. -/
example : ∃ P ∈ lifts (Rat.padicValuation 2).integer.subtype,
    (cauchyKernel 2 0).comp (C 1 + C 4 * X) = C 2 * P := by
  have h := exists_cauchyKernel_comp_eq_two_mul (a := 1) (t := 1) (d := 0) (by decide)
    (by decide) (by decide)
  norm_num at h
  exact h

/-! ### Reduction modulo `2 ^ p` -/

/-- `1 / 3 ≡ 3 (mod 8)`, since `3 * 3 = 9 ≡ 1`. -/
example (h : Rat.padicValuation 2 ((3 : ℚ)⁻¹) ≤ 1) :
    Rat.padicIntegerToZModPow 2 3 ⟨(3 : ℚ)⁻¹, h⟩ = 3 := by
  have h3 := Rat.padicIntegerToZModPow_mul_den 2 3 ⟨(3 : ℚ)⁻¹, h⟩
  have hden : ((3 : ℚ)⁻¹).den = 3 := by simp
  have hnum : ((3 : ℚ)⁻¹).num = 1 := by simp
  simp only [hden, hnum, Nat.cast_ofNat, Int.cast_one] at h3
  have h9 : (3 * 3 : ZMod (2 ^ 3)) = 1 := by decide
  calc Rat.padicIntegerToZModPow 2 3 ⟨(3 : ℚ)⁻¹, h⟩
      = Rat.padicIntegerToZModPow 2 3 ⟨(3 : ℚ)⁻¹, h⟩ * (3 * 3) := by rw [h9, mul_one]
    _ = 3 := by rw [← mul_assoc, h3, one_mul]

/-! ### The deformed contraction -/

/-- A row vertex `0` and a column vertex `1` joined by one edge, with integer tensors. -/
def oneEdge : TensorNetwork ℚ Bool (Fin 2) (Fin 1) where
  src _ := 0
  tgt _ := 1
  tensor v x := if v = 0 then (if x 0 then 2 else 1) else (if x 0 then 5 else 3)
  tensor_congr v x y h := by rw [h 0 (by fin_cases v <;> simp)]

/-- With one slot (`a = 0`, `α = 2`), `F(-1 + 2 z)` has `2`-integral coefficients. -/
example :
    ((oneEdge.map Polynomial.C).deformedContraction (fun v => v = 0)
        ((cauchyMatrix (2 ^ 0) (fun _ : Fin 1 => ()) (fun _ => 0)).map
          (Polynomial.mapRingHom (algebraMap ℚ ℚ)))).comp
      (C ((-1 : ℤ) : ℚ) + C (2 ^ (0 + 1)) * X) ∈
      liftsRing (Rat.padicValuation 2).integer.subtype :=
  TensorNetwork.deformedContraction_cauchyMatrix_comp_mem_liftsRing _ _ (fun _ => by norm_num)
    (by decide) _ (fun c hc => hc) fun v x => by
      simp only [oneEdge]
      split_ifs <;> exact (Rat.padicValuation_le_one_iff.mpr (by decide))

end ComplexityTests.Computability.Circuit.Frontier.TensorNetwork.IntegralCoordinates
