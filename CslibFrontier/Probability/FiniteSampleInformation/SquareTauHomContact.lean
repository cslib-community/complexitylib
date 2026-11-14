/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquarePositiveDeterminantGraph

/-!
# Contact of the tau-homogenization on the simplex

The homogenized polynomial is compared with the original polynomial only on
mass-one points and along mass-zero tangent directions.  No global DPI claim
is made for the homogenization.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareTauHomContact.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators Topology

namespace SquarePolynomial

open GeneralAsymmetricC1

lemma peval_tauPoly_eq_mass {n : ℕ} (star : Var n) (U : Mat n n) :
    peval (tauPoly (R := ℝ) star) U = mass U := by
  rw [tauPoly_eq_sum_X]
  simp only [peval, MvPolynomial.eval_sum, MvPolynomial.eval_X]
  rw [Fintype.sum_prod_type]
  rfl

lemma tauHom_eval_eq_on_simplex {n : ℕ} (star : Var n)
    (P : Poly n) {U : Mat n n} (hU : mass U = 1) :
    peval (tauHomogenize (R := ℝ) star P) U = peval P U := by
  apply eval_tauHomogenize_of_eval_tau_eq_one
  exact (peval_tauPoly_eq_mass star U).trans hU

lemma tauHom_sub_original {n : ℕ} (star : Var n) (P : Poly n) :
    ∃ K : Poly n,
      tauHomogenize (R := ℝ) star P - P =
        (tauPoly (R := ℝ) star - 1) * K :=
  tauHomogenize_sub_mem_simplex_kernel (R := ℝ) star P

lemma tauHom_row_cone_value_zero {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat n n} (hU : Simplex U) {r : Fin n}
    {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U r a =
      ∑ i ∈ Finset.univ.erase r, lambda i * U i a) :
    peval (tauHomogenize (R := ℝ) (simplexStar hn) P) U = 0 := by
  rw [tauHom_eval_eq_on_simplex (simplexStar hn) P hU.2]
  exact polynomial_row_cone_vanishing hn P hDPI hRKO hU hlambda hrow

/-- The derivative bridge is deliberately restricted to mass-zero tangent
directions at mass-one points. -/
lemma tauHom_tangent_derivative_eq {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) {U V : Mat n n}
    (hU : mass U = 1) (hV : mass V = 0) :
    (fderiv ℝ (peval (tauHomogenize (R := ℝ) (simplexStar hn) P)) U) V =
      (fderiv ℝ (peval P) U) V := by
  let : NeZero n := ⟨by omega⟩
  let H : Poly n := tauHomogenize (R := ℝ) (simplexStar hn) P
  obtain ⟨K, hK⟩ := tauHom_sub_original (simplexStar hn) P
  have hpoly : H = P +
      (tauPoly (R := ℝ) (simplexStar hn) - 1) * K := by
    dsimp [H]
    rw [sub_eq_iff_eq_add] at hK
    exact hK.trans (add_comm _ _)
  have hmassline (t : ℝ) : mass (U + t • V) = 1 := by
    simp [hU, hV]
  have hline :
      (fun t : ℝ => peval H (U + t • V)) =
        fun t : ℝ => peval P (U + t • V) := by
    funext t
    rw [hpoly]
    rw [show peval (P +
        (tauPoly (R := ℝ) (simplexStar hn) - 1) * K) (U + t • V) =
      peval P (U + t • V) +
        (peval (tauPoly (R := ℝ) (simplexStar hn)) (U + t • V) - 1) *
          peval K (U + t • V) by
      simp [peval]]
    rw [peval_tauPoly_eq_mass, hmassline]
    ring
  have hdH := GeneralAsymmetricC1.hasDerivAt_affine
    (U := U) (V := V)
    ((peval_contDiff H).differentiable (by norm_num) U)
  have hdP := GeneralAsymmetricC1.hasDerivAt_affine
    (U := U) (V := V)
    ((peval_contDiff P).differentiable (by norm_num) U)
  rw [hline] at hdH
  exact hdH.unique hdP

lemma tauHom_row_cone_tangent_derivative_zero
    {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat n n} (hU : Simplex U) (hpos : ∀ i a, 0 < U i a)
    {r : Fin n} {lambda : Fin n → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U r a =
      ∑ i ∈ Finset.univ.erase r, lambda i * U i a)
    {V : Mat n n} (hV : mass V = 0) :
    (fderiv ℝ (peval
      (tauHomogenize (R := ℝ) (simplexStar hn) P)) U) V = 0 := by
  rw [tauHom_tangent_derivative_eq hn P hU.2 hV]
  exact polynomial_row_cone_tangent_derivative_zero hn P hDPI hRKO
    hU hpos hlambda hrow hV

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
