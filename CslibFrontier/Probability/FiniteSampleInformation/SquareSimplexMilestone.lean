/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareDeterminantDoubleContact

/-!
# Compiled square-simplex milestone

This file joins the analytic row-cone theorem to polynomial evaluation and
records the exact lifting step from a dehomogenized determinant-square factor
to the desired global identity modulo the simplex equation.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareSimplexMilestone.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace SquarePolynomial

open GeneralAsymmetricC1

/-- The coordinate eliminated in the affine simplex chart: the top entry of
the last column. -/
@[expose] def simplexStar {n : ℕ} (hn : 2 ≤ n) : Var n :=
  (⟨0, by omega⟩, ⟨n - 1, by omega⟩)

/-- The bottom-right coordinate, used as the separate determinant pivot. -/
def determinantPivot {n : ℕ} (hn : 2 ≤ n) : Var n :=
  (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩)

lemma determinantPivot_ne_simplexStar {n : ℕ} (hn : 2 ≤ n) :
    determinantPivot hn ≠ simplexStar hn := by
  intro h
  have hfirst := congrArg (fun z : Var n => z.1.val) h
  simp [determinantPivot, simplexStar] at hfirst
  omega

/-- The generic polynomial instance of row-cone vanishing. -/
theorem polynomial_row_cone_vanishing {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat n n} (hU : Simplex U) {r : Fin n}
    {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U r a =
      ∑ i ∈ Finset.univ.erase r, lambda i * U i a) :
    peval P U = 0 := by
  let : NeZero n := ⟨by omega⟩
  exact row_cone_vanishing hn (peval_contDiff P) hDPI hRKO hU hlambda hrow

/-- At a positive row-cone point, every mass-zero directional derivative of
polynomial evaluation vanishes. -/
theorem polynomial_row_cone_tangent_derivative_zero {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat n n} (hU : Simplex U) (hpos : ∀ i a, 0 < U i a)
    {r : Fin n} {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U r a =
      ∑ i ∈ Finset.univ.erase r, lambda i * U i a)
    {V : Mat n n} (hmassV : mass V = 0) :
    (fderiv ℝ (peval P) U) V = 0 := by
  let : NeZero n := ⟨by omega⟩
  exact row_cone_tangent_derivative_zero hn (peval_contDiff P) hDPI hRKO
    hU hpos hlambda hrow hmassV

/-- Once determinant-square divisibility has been established in the affine
simplex coordinates, the original-coordinate conclusion follows formally. -/
theorem square_identity_of_dehom_factor {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (Qbar : MvPolynomial (Free (simplexStar hn)) ℝ)
    (hfactor : dehomSimplex (R := ℝ) (simplexStar hn) P =
      dehomSimplex (R := ℝ) (simplexStar hn) (detPoly n) ^ 2 * Qbar) :
    ∃ Q K : Poly n,
      P = detPoly n ^ 2 * Q +
        (tauPoly (R := ℝ) (simplexStar hn) - 1) * K := by
  exact lift_dehom_square_factor (R := ℝ) (simplexStar hn) P (detPoly n) Qbar hfactor

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
