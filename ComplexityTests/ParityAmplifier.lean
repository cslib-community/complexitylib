/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Polynomial.ParityAmplifier
import Mathlib.Data.Rat.Defs

/-! Concrete witnesses and worked examples for
`Complexity.Foundations.Data.Polynomial.ParityAmplifier` (Lemmas 5.1, 5.2, and B.1 of the
subexponential `#k-SAT` manuscript). -/

namespace ComplexityTests.ParityAmplifier

open Finset Polynomial

/-! ### 1. Explicit formulas and the manuscript's `ℓ = 2` decomposition (p. 37) -/

/-- `p_2(X) = (1 - X) + (2X - 1)(X^2 - X)`, matching `p_2(Y) = 1 - 3Y^2 + 2Y^3` on p. 37. -/
theorem parityAmplifier_two_decomp :
    parityAmplifier 2 = (1 - X) + hPoly * (2 * X - 1) := by
  rw [parityAmplifier_two, hPoly]
  ring

/-- The quotient and remainder of `p_2(X)` on division by `h(X) = X^2 - X` are `2X - 1` and
`1 - X`. -/
theorem div_mod_parityAmplifier_two :
    parityAmplifier 2 /ₘ hPoly = 2 * X - 1 ∧ parityAmplifier 2 %ₘ hPoly = 1 - X := by
  apply div_modByMonic_unique (2 * X - 1) (1 - X) monic_hPoly
  refine ⟨parityAmplifier_two_decomp.symm, ?_⟩
  rw [degree_eq_natDegree monic_hPoly.ne_zero, natDegree_hPoly]
  refine (degree_sub_le 1 X).trans_lt ?_
  rw [degree_one, degree_X]
  decide

/-- First base-`h` digit of `p_2`: `e_0(X) = 1 - X`. -/
theorem parityBaseDigit_two_zero : parityBaseDigit 2 0 = 1 - X :=
  div_mod_parityAmplifier_two.2

/-- Second base-`h` digit of `p_2`: `e_1(X) = 2 * X - 1`. -/
theorem parityBaseDigit_two_one : parityBaseDigit 2 1 = 2 * X - 1 := by
  change (parityAmplifier 2 /ₘ hPoly) %ₘ hPoly = 2 * X - 1
  rw [div_mod_parityAmplifier_two.1, (modByMonic_eq_self_iff monic_hPoly).mpr]
  rw [degree_eq_natDegree monic_hPoly.ne_zero, natDegree_hPoly]
  refine degree_le_natDegree.trans_lt ?_
  rw [Nat.cast_lt]
  have h1 : (2 * X - 1 : ℤ[X]).natDegree ≤ max (2 * X : ℤ[X]).natDegree (1 : ℤ[X]).natDegree :=
    natDegree_sub_le (2 * X) 1
  have h2 : (2 * X : ℤ[X]).natDegree ≤ (2 : ℤ[X]).natDegree + (X : ℤ[X]).natDegree :=
    natDegree_mul_le
  rw [natDegree_ofNat, natDegree_X] at h2
  rw [natDegree_one] at h1
  omega

/-! ### 2. Concrete parity amplification congruences (Lemma 5.1) -/

example : (parityAmplifier 3).eval 6 ≡ 1 [ZMOD (2 : ℤ) ^ 3] :=
  parityAmplifier_eval_modEq_one_of_even (by decide) ⟨3, by ring⟩

example : (parityAmplifier 3).eval (-4) ≡ 1 [ZMOD (2 : ℤ) ^ 3] :=
  parityAmplifier_eval_modEq_one_of_even (by decide) ⟨-2, by ring⟩

example : (parityAmplifier 3).eval 5 ≡ 0 [ZMOD (2 : ℤ) ^ 3] :=
  parityAmplifier_eval_modEq_zero_of_odd 3 ⟨2, by ring⟩

example : (parityAmplifier 3).eval (-3) ≡ 0 [ZMOD (2 : ℤ) ^ 3] :=
  parityAmplifier_eval_modEq_zero_of_odd 3 ⟨-2, by ring⟩

/-! ### 3. Coefficient norm bounds (Lemma B.1) -/

example : coeffNorm1 (parityAmplifier 3) ≤ 512 :=
  coeffNorm1_parityAmplifier_le 3

example (j k : ℕ) : ((parityBaseDigit 3 j).coeff k).natAbs ≤ 6 ^ j * 512 :=
  natAbs_coeff_parityBaseDigit_le 3 j k

example (j : ℕ) : coeffNorm1 (parityBaseDigit 3 j) ≤ 2 * (6 ^ j * 512) :=
  coeffNorm1_parityBaseDigit_le 3 j

/-! ### 4. Shared-`V` truncation and multivariate degree bound (Lemma 5.2) -/

/-- Empty equation set: the truncated sum is `1 ≡ 1 (mod 2 ^ ℓ)`. -/
example :
    sumCoeffsBelow 2 (∏ i ∈ (∅ : Finset (Fin 0)), parityFactor 2 (![] i)) ≡
      1 [ZMOD (2 : ℤ) ^ 2] := by
  simpa only [prod_empty] using
    sumCoeffsBelow_prod_parityFactor_modEq (∅ : Finset (Fin 0)) (by decide : 1 ≤ 2) ![]

/-- Two equations with both values even (`y = ![4, -2]`): truncated product is `≡ 1 (mod 4)`. -/
example :
    sumCoeffsBelow 2 (∏ i : Fin 2, parityFactor 2 (![(4 : ℤ), -2] i)) ≡
      1 [ZMOD (2 : ℤ) ^ 2] := by
  have h := sumCoeffsBelow_prod_parityFactor_modEq (univ : Finset (Fin 2)) (by decide : 1 ≤ 2)
    ![(4 : ℤ), -2]
  have hrhs : (∏ i : Fin 2, if Even (![(4 : ℤ), -2] i) then (1 : ℤ) else 0) = 1 := by
    rw [Fin.prod_univ_two]
    have h0 : Even (![(4 : ℤ), -2] 0) := ⟨2, by decide⟩
    have h1 : Even (![(4 : ℤ), -2] 1) := ⟨-1, by decide⟩
    simp only [h0, h1, ↓reduceIte, mul_one]
  rwa [hrhs] at h

/-- Two equations with one odd value (`y = ![4, 3]`): truncated product is `≡ 0 (mod 4)`. -/
example :
    sumCoeffsBelow 2 (∏ i : Fin 2, parityFactor 2 (![(4 : ℤ), 3] i)) ≡
      0 [ZMOD (2 : ℤ) ^ 2] := by
  have h := sumCoeffsBelow_prod_parityFactor_modEq (univ : Finset (Fin 2)) (by decide : 1 ≤ 2)
    ![(4 : ℤ), 3]
  have hrhs : (∏ i : Fin 2, if Even (![(4 : ℤ), 3] i) then (1 : ℤ) else 0) = 0 := by
    rw [Fin.prod_univ_two]
    have h1 : ¬Even (![(4 : ℤ), 3] 1) := by decide
    simp only [h1, ↓reduceIte, mul_zero]
  rwa [hrhs] at h

/-- Manuscript p. 37 worked degree bound: for `ℓ = 2` and two linear equations (`d = 1`, `#I = 2`)
over `ℚ`, the truncated sum `S_2(B_0(V) B_1(V))` has total degree at most `1 * (2 + 2 * 1) = 4`. -/
example :
    (sumCoeffsBelow 2
      (∏ i ∈ (univ : Finset (Fin 2)),
        parityFactor 2 (MvPolynomial.X i : MvPolynomial (Fin 2) ℚ))).totalDegree ≤ 4 := by
  have h := totalDegree_sumCoeffsBelow_prod_parityFactor_le
    (I := (univ : Finset (Fin 2))) 2
    (y := fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) ℚ)) (d := 1)
    (fun i _ => by rw [MvPolynomial.totalDegree_X])
  simpa only [card_univ, Fintype.card_fin] using h

end ComplexityTests.ParityAmplifier
