/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteSampleInformation.Payments
public import CslibFrontier.Probability.FiniteSampleInformation.DimensionChanging

/-!
# Finite-sample information rigidity

[Kong2027], Theorem B / Theorem 4.1 and Proposition 4.4
(PDF pp. 4, 11–14). Rows are the processed alphabet. The hypotheses are
one-sided fixed-alphabet DPI and vanishing on independent joint laws. The ideal
is the square of the maximal-minor ideal, modulo the total-mass equation.
Nonzero means nonzero somewhere on the closed probability simplex.

The imported analytic endpoints are Theorem A / Theorems 3.3 and 3.5
(PDF pp. 3, 9–10), with an ambient C¹ extension across the boundary, and
Theorem 5.1 (PDF p. 15). `dimensionChanging_collapse` is Corollary 5.3
(PDF p. 16). The sample and task bridges live in `Estimation` and `Payments`.
The Section 7 restricted-deviation payment remains in `PeerPrediction.Quadratic`.
-/

public section
noncomputable section
namespace Cslib.FiniteSampleInformation
open GeneralAsymmetricC1 WidePolynomial

/-- Theorem 4.1's ideal membership in the entire non-tall range, including
square matrices. No determinantal cancellation hypothesis is assumed. -/
theorem determinantal_rigidity {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m)
    (P : WidePoly n m) (hDPI : PolynomialDPI P) (hIZ : PolynomialRKO P) :
    P ∈ maximalMinorIdeal n m ^ 2 ⊔
      Ideal.span (Set.singleton (tauPolyWide (by omega) (by omega) - 1)) := by
  cases n with
  | zero => omega
  | succ k =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ m by omega)
    exact wide_simplex_maximalMinor_sq_core (by omega) (by omega) P hDPI hIZ

/-- Theorem 4.1's sharp degree lower bound for a nonzero simplex functional. -/
theorem polynomial_degree_lower_bound {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m)
    (P : WidePoly n m) (hDPI : PolynomialDPI P) (hIZ : PolynomialRKO P)
    (hNonzero : ∃ U : Mat n m, Simplex U ∧ peval P U ≠ 0) :
    2 * n ≤ P.totalDegree := by
  rcases lt_or_eq_of_le hnm with hlt | heq
  · exact wide_simplex_totalDegree_lower_bound hn hlt P hDPI hIZ hNonzero
  · subst m
    exact SquarePolynomial.square_simplex_totalDegree_lower_bound hn P hDPI hIZ hNonzero

/-- Proposition 4.4's nontriviality is witnessed on the simplex, rather than
merely as a nonzero ambient polynomial. -/
theorem gramDetPoly_nonzero_on_simplex {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    ∃ U : Mat n m, Simplex U ∧ peval (GramDependence.gramDetPoly n m) U ≠ 0 := by
  refine ⟨diagonalLaw hnm, diagonalLaw_simplex (by omega) hnm, ?_⟩
  rw [GramDependence.peval_gramDetPoly]
  exact (diagonalLaw_gramDet_pos (by omega) hnm).ne'

/-- Theorem 4.1 and Proposition 2.4: every unbiased nonzero independence-zero
DPI functional requires at least `2n` samples in the non-tall range. -/
theorem sample_lower_bound {n m d : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m)
    (M : Payment n m d) (hDPI : TruthfulAlice M)
    (hIZ : IndependenceZeroPayment M) (hNonzero : NontrivialPayment M) : 2 * n ≤ d := by
  have hprops := paymentPolynomial_properties M hDPI hIZ
  apply (polynomial_degree_lower_bound hn hnm (paymentPolynomial M)
    hprops.2.1 hprops.2.2 ?_).trans hprops.1
  obtain ⟨U, hU, hMU⟩ := hNonzero
  exact ⟨U, hU, by simpa only [eval_paymentPolynomial] using hMU⟩

/-- The degree/sample lower bound is attained for every non-tall alphabet pair. -/
theorem exists_sharp_rectangular_payment {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    ∃ M : Payment n m (2 * n), TruthfulAlice M ∧ IndependenceZeroPayment M ∧
      NontrivialPayment M ∧ ∀ U, Simplex U →
        expectedPayment M U = GramDependence.gramDet U := by
  obtain ⟨M, hM⟩ := exists_payment_of_polynomial (GramDependence.gramDetPoly n m)
    (le_of_eq (GramDependence.gramDetPoly_totalDegree hnm))
  have hexpect (U : Mat n m) (hU : Simplex U) :
      expectedPayment M U = GramDependence.gramDet U :=
    (hM U hU).trans (GramDependence.peval_gramDetPoly U)
  refine ⟨M, ?_, ?_, ?_, hexpect⟩
  · intro T U hT hU
    rw [hexpect _ (stochastic_mul_simplex hT hU), hexpect U hU]
    exact GramDependence.gramDet_dpi T U hT hU
  · intro x y hU
    rw [hexpect _ hU]
    exact GramDependence.gramDet_rko hn x y hU
  · refine ⟨diagonalLaw hnm, diagonalLaw_simplex (by omega) hnm, ?_⟩
    rw [hexpect _ (diagonalLaw_simplex (by omega) hnm)]
    exact (diagonalLaw_gramDet_pos (by omega) hnm).ne'

/-- In particular, no nonzero family of polynomial dependence measures can
satisfy dimension-changing DPI. Polynomiality supplies boundary regularity. -/
theorem dimensionChanging_polynomial_collapse
    (P : (n m : ℕ) → WidePoly n m)
    (hDPI : DimensionChangingDPI (fun n m => peval (P n m)))
    (hIZ : ∀ n m, 2 ≤ n → 2 ≤ m → PolynomialRKO (P n m))
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) {U : Mat n m} (hU : Simplex U) :
    peval (P n m) U = 0 := by
  apply dimensionChanging_collapse hDPI ?_ hIZ hn hm hU
  intro k l _ _ V _
  exact (AsymmetricPolynomial.peval_contDiff (P k l)).contDiffAt

end Cslib.FiniteSampleInformation
