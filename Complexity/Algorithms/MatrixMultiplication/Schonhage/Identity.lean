/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Alphabets
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.LinearCombination

/-!
# Schönhage's ten-term polynomial identity

The ten products of linear forms equal the wanted inner/outer product polynomial plus
an explicit error polynomial. This is an identity over integers in 24 formal variables.
The error term is retained; it cannot be discarded for unrestricted inputs.

## Main definitions

* `TriPoly`, `formL`, `formR`, `formO`: the polynomial interpretation of the forms.
* `G`, `E`: the wanted polynomial and the error polynomial.

## Main results

* `identity`: the complete ten-term polynomial identity, including its error.

## References

Part of [AlmanWilliams2026, Section 2]. Direct mathematical adaptation of
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Definitions are selectively extracted from that pin's `PaperStatements.lean`; no machine
semantics or running-time statement is imported. The docstrings below explain the local
declarations in our own words.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- All 24 variables of the identity: the left, the right and the output variables.
-/
abbrev Var : Type := LeftVar ⊕ RightVar ⊕ OutVar

/-- The polynomials in which Schönhage's identity is an identity.
-/
abbrev TriPoly : Type := MvPolynomial Var ℤ

/-- A left variable, as a polynomial.
-/
noncomputable def polyL (s : LeftVar) : TriPoly := MvPolynomial.X (Sum.inl s)
/-- A right variable, as a polynomial.
-/
noncomputable def polyR (t : RightVar) : TriPoly := MvPolynomial.X (Sum.inr (Sum.inl t))
/-- An output variable, as a polynomial.
-/
noncomputable def polyO (z : OutVar) : TriPoly := MvPolynomial.X (Sum.inr (Sum.inr z))

/-- A linear form in the left variables, as a polynomial.
-/
noncomputable def formL (f : LeftVar → ℤ) : TriPoly := ∑ s, MvPolynomial.C (f s) * polyL s
/-- A linear form in the right variables, as a polynomial.
-/
noncomputable def formR (f : RightVar → ℤ) : TriPoly := ∑ t, MvPolynomial.C (f t) * polyR t
/-- A linear form in the output variables, as a polynomial.
-/
noncomputable def formO (f : OutVar → ℤ) : TriPoly := ∑ z, MvPolynomial.C (f z) * polyO z

/-- The target polynomial combines the nine outer `x`-`y` products with the four `p`-`q` products
attached to the inner coordinate.
-/
noncomputable def G : TriPoly :=
  (∑ i : Fin 3, ∑ j : Fin 3, polyL (.x i) * polyR (.y j) * polyO (.z i j))
    + (∑ i : Fin 2, ∑ j : Fin 2, polyL (.p i j) * polyR (.q i j)) * polyO .z0

/-- The error polynomial collects the additional outer-coordinate terms involving `pHat` or
`qHat`. It has no inner-coordinate summand.
-/
noncomputable def E : TriPoly :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (polyL (.x i) * formR (qHat i j) + formL (pHat i j) * polyR (.y j)
      + formL (pHat i j) * formR (qHat i j)) * polyO (.z i j)

/-- A sum over the ten terms, split into the `P_ij` and `P₀`.
-/
private theorem sum_term {A : Type*} [AddCommMonoid A] (f : Term → A) :
    ∑ lam, f lam = ∑ i, ∑ j, f (.P i j) + f .P0 := by
  rw [← Term.equiv.symm.sum_comp f, Fintype.sum_option, Fintype.sum_prod_type, add_comm]
  rfl

/-! ### Linear forms as polynomials -/

/-- `formL` is the linear map that sends the form consisting of the single variable `s` to the
polynomial `s`.
-/
theorem formL_eq_linearCombination (f : LeftVar → ℤ) :
    formL f = Fintype.linearCombination ℤ polyL f := by
  simp only [formL, Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]

/-- `formR` is the linear map that sends the form consisting of the single variable `t` to the
polynomial `t`.
-/
theorem formR_eq_linearCombination (f : RightVar → ℤ) :
    formR f = Fintype.linearCombination ℤ polyR f := by
  simp only [formR, Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]

/-- `formO` is the linear map that sends the form consisting of the single variable `z` to the
polynomial `z`.
-/
theorem formO_eq_linearCombination (f : OutVar → ℤ) :
    formO f = Fintype.linearCombination ℤ polyO f := by
  simp only [formO, Fintype.linearCombination_apply, MvPolynomial.smul_eq_C_mul]

/-- The form consisting of a single left variable is that variable.
-/
theorem formL_single (s : LeftVar) : formL (Pi.single s 1) = polyL s := by
  simp [formL_eq_linearCombination]

/-- The form consisting of a single right variable is that variable.
-/
theorem formR_single (t : RightVar) : formR (Pi.single t 1) = polyR t := by
  simp [formR_eq_linearCombination]

/-- The form consisting of a single output variable is that variable.
-/
theorem formO_single (z : OutVar) : formO (Pi.single z 1) = polyO z := by
  simp [formO_eq_linearCombination]

/-- Interpret an indexed left coefficient form as the sum of its `x` variable and its extended `p`
form.
-/
theorem formL_phi_P (i j : Fin 3) : formL (phi (.P i j)) = polyL (.x i) + formL (pHat i j) := by
  simp [phi, xForm, formL_eq_linearCombination]

/-- Interpret an indexed right coefficient form as the sum of its `y` variable and its extended
`q` form.
-/
theorem formR_psi_P (i j : Fin 3) : formR (psi (.P i j)) = polyR (.y j) + formR (qHat i j) := by
  simp [psi, yForm, formR_eq_linearCombination]

/-- Interpret an indexed output form as the sum of the corresponding outer variable and the inner
variable.
-/
theorem formO_chi_P (i j : Fin 3) : formO (chi (.P i j)) = polyO (.z i j) + polyO .z0 := by
  simp [chi, zForm, z0Form, formO_eq_linearCombination]

/-- The distinguished left form is the negative sum of the three `x` polynomials. -/
theorem formL_phi_P0 : formL (phi .P0) = -(polyL (.x 0) + polyL (.x 1) + polyL (.x 2)) := by
  simp [phi, xForm, formL_eq_linearCombination]

/-- The distinguished right form is the sum of the three `y` polynomials. -/
theorem formR_psi_P0 : formR (psi .P0) = polyR (.y 0) + polyR (.y 1) + polyR (.y 2) := by
  simp [psi, yForm, formR_eq_linearCombination]

/-- The distinguished output form denotes the inner polynomial variable alone. -/
theorem formO_chi_P0 : formO (chi .P0) = polyO .z0 :=
  formO_single .z0

/-! ### Lemma 6 -/

/-- Summing `pHat` over the row index gives the zero coefficient function. -/
theorem pHat_column_sum (j : Fin 3) : ∑ i, pHat i j = 0 := by
  fin_cases j <;> simp [Fin.sum_univ_three, pHat]

/-- Summing `qHat` over the column index gives the zero coefficient function. -/
theorem qHat_row_sum (i : Fin 3) : ∑ j, qHat i j = 0 := by
  fin_cases i <;> simp [Fin.sum_univ_three, qHat]

/-- The product sum for the extended arrays reduces to the four products from their original
two-by-two arrays.
-/
theorem sum_pHat_mul_qHat :
    ∑ i : Fin 3, ∑ j : Fin 3, formL (pHat i j) * formR (qHat i j)
      = ∑ i : Fin 2, ∑ j : Fin 2, polyL (.p i j) * polyR (.q i j) := by
  simp [Fin.sum_univ_three, Fin.sum_univ_two, pHat, qHat, pForm, qForm,
    formL_eq_linearCombination, formR_eq_linearCombination]

/-- The ten products of the coefficient forms equal the wanted polynomial `G` plus the explicit
error polynomial `E`.
-/
theorem identity : ∑ lam, formL (phi lam) * formR (psi lam) * formO (chi lam) = G + E := by
  -- The column sums of p̂ and the row sums of q̂, as identities of polynomials.
  have hcol : ∀ j, ∑ i, formL (pHat i j) = 0 := fun j => by
    simp only [formL_eq_linearCombination, ← map_sum, pHat_column_sum, map_zero]
  have hrow : ∀ i, ∑ j, formR (qHat i j) = 0 := fun i => by
    simp only [formR_eq_linearCombination, ← map_sum, qHat_row_sum, map_zero]
  simp only [Fin.sum_univ_three] at hcol hrow
  -- Write out the ten terms, and write the inner product in G as ∑ p̂_ij q̂_ij.
  simp only [sum_term, formL_phi_P, formR_psi_P, formO_chi_P, formL_phi_P0, formR_psi_P0,
    formO_chi_P0, G, E, ← sum_pHat_mul_qHat, Fin.sum_univ_three]
  -- The coefficients of the z_ij agree term by term.  In the coefficient of z₀ the products x_i y_j
  -- cancel, and the cross terms are ∑_i x_i ∑_j q̂_ij + ∑_j y_j ∑_i p̂_ij = 0.
  linear_combination polyO .z0 * (polyL (.x 0) * hrow 0 + polyL (.x 1) * hrow 1
    + polyL (.x 2) * hrow 2 + polyR (.y 0) * hcol 0 + polyR (.y 1) * hcol 1 + polyR (.y 2) * hcol 2)

end Cslib.Algorithms.MatrixMultiplication.Schonhage
