/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareTauHomContact

/-!
# Double contact on the positive determinant graph

The row-cone contact theorem is first applied to the mass-one normalization of
the graph.  Homogeneity then transports both the value and the pivot
directional derivative back to the unnormalized graph.  The tangent direction
used at the normalized point is explicitly `unit 0 0 - U`, whose mass is zero.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareDoubleContactOnBox.lean` at commit
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

lemma eval_smul_of_isHomogeneous
    {σ : Type*}
    {P : MvPolynomial σ ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : ℝ) (x : σ → ℝ) :
    MvPolynomial.eval (fun i => c * x i) P =
      c ^ d * MvPolynomial.eval x P := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [MvPolynomial.eval_add, ihp, ihq, mul_add]
  | monomial e r he =>
      rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      simp only [mul_pow, Finsupp.prod_mul]
      have hdegree : e.degree = d := by
        rw [Finsupp.degree_eq_weight_one]
        exact he
      rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum,
        ← Finsupp.degree_apply, hdegree]
      ring

lemma peval_smul_of_isHomogeneous {n d : ℕ}
    {P : Poly n} (hP : P.IsHomogeneous d)
    (c : ℝ) (U : Mat n n) :
    peval P (c • U) = c ^ d * peval P U := by
  unfold peval
  simpa [Pi.smul_apply, smul_eq_mul] using
    eval_smul_of_isHomogeneous hP c (fun ia => U ia.1 ia.2)

/-- Extend the row-cone coefficients by a zero distinguished coefficient. -/
def fullGraphRowCoeffs (m : ℕ) (y : DetCoeffVar m → ℝ) :
    Fin (m + 1) → ℝ :=
  Fin.cases 0 (graphRowCoeffs m y)

lemma fullGraphRowCoeffs_nonnegative {m : ℕ}
    {y : DetCoeffVar m → ℝ}
    (hcoeff : ∀ i, 0 < graphRowCoeffs m y i) :
    ∀ i, 0 ≤ fullGraphRowCoeffs m y i := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [fullGraphRowCoeffs]
  · exact (hcoeff i).le

lemma normalizedGraphMatrix_row_relation_erase {m : ℕ}
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    ∀ a, normalizedGraphMatrix m y 0 a =
      ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
        fullGraphRowCoeffs m y i * normalizedGraphMatrix m y i a := by
  intro a
  have hrow := normalizedGraphMatrix_row_relation m ha a
  calc
    normalizedGraphMatrix m y 0 a =
        ∑ i : Fin m, graphRowCoeffs m y i *
          normalizedGraphMatrix m y i.succ a := hrow
    _ = ∑ i : Fin (m + 1), fullGraphRowCoeffs m y i *
          normalizedGraphMatrix m y i a := by
      rw [Fin.sum_univ_succ]
      simp [fullGraphRowCoeffs]
    _ = ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
          fullGraphRowCoeffs m y i *
            normalizedGraphMatrix m y i a := by
      symm
      apply Finset.sum_erase
      simp [fullGraphRowCoeffs]

lemma homogeneous_radial_derivative_zero {n d : ℕ}
    {P : Poly n} (hP : P.IsHomogeneous d)
    {U : Mat n n} (hzero : peval P U = 0) :
    (fderiv ℝ (peval P) U) U = 0 := by
  have hline : (fun t : ℝ => peval P (U + t • U)) = fun _ => 0 := by
    funext t
    have hmatrix : U + t • U = (1 + t) • U := by
      ext i j
      simp [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hmatrix, peval_smul_of_isHomogeneous hP, hzero, mul_zero]
  have hd := GeneralAsymmetricC1.hasDerivAt_affine
    (U := U) (V := U)
    ((peval_contDiff P).differentiable (by norm_num) U)
  rw [hline] at hd
  exact hd.unique (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))

lemma homogeneous_derivative_zero_of_inv_smul {n d : ℕ}
    {P : Poly n} (hP : P.IsHomogeneous d)
    {S E : Mat n n} {s : ℝ} (hs : s ≠ 0)
    (hzero :
      (fderiv ℝ (peval P) (s⁻¹ • S)) E = 0) :
    (fderiv ℝ (peval P) S) E = 0 := by
  let U : Mat n n := s⁻¹ • S
  have hline : (fun t : ℝ => peval P (S + t • E)) =
      fun t : ℝ => s ^ d * peval P (U + (t / s) • E) := by
    funext t
    have hmatrix : S + t • E = s • (U + (t / s) • E) := by
      ext i j
      dsimp [U]
      field_simp
    rw [hmatrix, peval_smul_of_isHomogeneous hP]
  have hdU := GeneralAsymmetricC1.hasDerivAt_affine
    (U := U) (V := E)
    ((peval_contDiff P).differentiable (by norm_num) U)
  have hzeroU : (fderiv ℝ (peval P) U) E = 0 := hzero
  rw [hzeroU] at hdU
  have hdiv : HasDerivAt (fun t : ℝ => t / s) (1 / s) 0 :=
    (hasDerivAt_id (x := (0 : ℝ))).div_const s
  have hdU' : HasDerivAt (fun t : ℝ => peval P (U + t • E)) 0
      ((0 : ℝ) / s) := by
    simpa using hdU
  have hcomp := hdU'.comp 0 hdiv
  have hscaled := HasDerivAt.const_mul (s ^ d) hcomp
  have hscaled' : HasDerivAt
      (fun t : ℝ => s ^ d * peval P (U + (t / s) • E)) 0 0 := by
    simpa [Function.comp_def] using hscaled
  have hdS := GeneralAsymmetricC1.hasDerivAt_affine
    (U := S) (V := E)
    ((peval_contDiff P).differentiable (by norm_num) S)
  rw [hline] at hdS
  exact hdS.unique hscaled'

lemma tauHom_normalized_graph_value_zero
    {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P)
    {y : DetCoeffVar m → ℝ}
    (ha : graphLeadingValue m y ≠ 0)
    (hpos : ∀ i j, 0 < graphMatrix m y i j)
    (hcoeff : ∀ i, 0 < graphRowCoeffs m y i) :
    peval (tauHomogenize (R := ℝ)
      (simplexStar (by omega : 2 ≤ m + 1)) P)
      (normalizedGraphMatrix m y) = 0 := by
  let hn : 2 ≤ m + 1 := by omega
  let U : Mat (m + 1) (m + 1) := normalizedGraphMatrix m y
  have hU : Simplex U := by
    exact ⟨fun i j => (normalizedGraphMatrix_pos m hpos i j).le,
      normalizedGraphMatrix_mass_one m hpos⟩
  exact tauHom_row_cone_value_zero hn P hDPI hRKO hU
    (fullGraphRowCoeffs_nonnegative hcoeff)
    (normalizedGraphMatrix_row_relation_erase ha)

lemma tauHom_normalized_graph_pivot_derivative_zero
    {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P)
    {y : DetCoeffVar m → ℝ}
    (ha : graphLeadingValue m y ≠ 0)
    (hpos : ∀ i j, 0 < graphMatrix m y i j)
    (hcoeff : ∀ i, 0 < graphRowCoeffs m y i) :
    (fderiv ℝ (peval
      (tauHomogenize (R := ℝ) (simplexStar (by omega : 2 ≤ m + 1)) P))
      (normalizedGraphMatrix m y))
      (unit (0 : Fin (m + 1)) (0 : Fin (m + 1))) = 0 := by
  let : NeZero (m + 1) := ⟨by omega⟩
  let hn : 2 ≤ m + 1 := by omega
  let U : Mat (m + 1) (m + 1) := normalizedGraphMatrix m y
  let E : Mat (m + 1) (m + 1) := unit 0 0
  let V : Mat (m + 1) (m + 1) := E - U
  let H : Poly (m + 1) :=
    tauHomogenize (R := ℝ) (simplexStar hn) P
  have hU : Simplex U := by
    exact ⟨fun i j => (normalizedGraphMatrix_pos m hpos i j).le,
      normalizedGraphMatrix_mass_one m hpos⟩
  have hlambda : ∀ i, 0 ≤ fullGraphRowCoeffs m y i :=
    fullGraphRowCoeffs_nonnegative hcoeff
  have hrow : ∀ a, U 0 a =
      ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
        fullGraphRowCoeffs m y i * U i a :=
    normalizedGraphMatrix_row_relation_erase ha
  have hvalue : peval H U = 0 := by
    exact tauHom_normalized_graph_value_zero hm P hDPI hRKO
      ha hpos hcoeff
  have hmassV : mass V = 0 := by
    change (∑ i, ∑ a, (E i a - U i a)) = 0
    simp only [Finset.sum_sub_distrib]
    change mass E - mass U = 0
    rw [hU.2]
    simp [E]
  have htangent : (fderiv ℝ (peval H) U) V = 0 := by
    exact tauHom_row_cone_tangent_derivative_zero hn P hDPI hRKO hU
      (normalizedGraphMatrix_pos m hpos) hlambda hrow hmassV
  have hradial : (fderiv ℝ (peval H) U) U = 0 := by
    exact homogeneous_radial_derivative_zero
      (tauHomogenize_isHomogeneous (simplexStar hn) P) hvalue
  have hE : E = V + U := by
    dsimp [V]
    abel
  change (fderiv ℝ (peval H) U) E = 0
  rw [hE, map_add, htangent, hradial, add_zero]

lemma tauHom_graph_value_zero
    {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P)
    {y : DetCoeffVar m → ℝ}
    (ha : graphLeadingValue m y ≠ 0)
    (hpos : ∀ i j, 0 < graphMatrix m y i j)
    (hcoeff : ∀ i, 0 < graphRowCoeffs m y i) :
    peval (tauHomogenize (R := ℝ)
      (simplexStar (by omega : 2 ≤ m + 1)) P) (graphMatrix m y) = 0 := by
  let hn : 2 ≤ m + 1 := by omega
  let H : Poly (m + 1) :=
    tauHomogenize (R := ℝ) (simplexStar hn) P
  let S : Mat (m + 1) (m + 1) :=
    fun i j => graphMatrix m y i j
  let s : ℝ := graphMass m y
  have hs : s ≠ 0 := (graphMass_pos m hpos).ne'
  have hnormalized : s⁻¹ • S = normalizedGraphMatrix m y := by
    rfl
  have hvalue := tauHom_normalized_graph_value_zero hm P hDPI hRKO
    ha hpos hcoeff
  change peval H S = 0
  have hscale := peval_smul_of_isHomogeneous
    (tauHomogenize_isHomogeneous (simplexStar hn) P)
    s (s⁻¹ • S)
  have hrecover : s • (s⁻¹ • S) = S := by
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  rw [hrecover, hnormalized, hvalue, mul_zero] at hscale
  exact hscale

lemma tauHom_graph_pivot_derivative_zero
    {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P)
    {y : DetCoeffVar m → ℝ}
    (ha : graphLeadingValue m y ≠ 0)
    (hpos : ∀ i j, 0 < graphMatrix m y i j)
    (hcoeff : ∀ i, 0 < graphRowCoeffs m y i) :
    (fderiv ℝ (peval
      (tauHomogenize (R := ℝ) (simplexStar
        (by omega : 2 ≤ m + 1)) P)) (graphMatrix m y))
      (unit (0 : Fin (m + 1)) (0 : Fin (m + 1))) = 0 := by
  let : NeZero (m + 1) := ⟨by omega⟩
  let hn : 2 ≤ m + 1 := by omega
  let H : Poly (m + 1) :=
    tauHomogenize (R := ℝ) (simplexStar hn) P
  let S : Mat (m + 1) (m + 1) :=
    fun i j => graphMatrix m y i j
  let E : Mat (m + 1) (m + 1) := unit 0 0
  let s : ℝ := graphMass m y
  have hs : s ≠ 0 := (graphMass_pos m hpos).ne'
  have hnormalized : s⁻¹ • S = normalizedGraphMatrix m y := by
    rfl
  have hzero := tauHom_normalized_graph_pivot_derivative_zero
    hm P hDPI hRKO ha hpos hcoeff
  change (fderiv ℝ (peval H) S) E = 0
  apply homogeneous_derivative_zero_of_inv_smul
    (tauHomogenize_isHomogeneous (simplexStar hn) P) hs
  rw [hnormalized]
  exact hzero

/-- The tau-homogenized polynomial in the distinguished pivot coordinate. -/
@[expose] def tauHomPivotPolynomial {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (y : DetCoeffVar m → ℝ) : Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval y)
    (toNested (R := ℝ) (pivotZero m)
      (tauHomogenize (R := ℝ)
        (simplexStar (by omega : 2 ≤ m + 1)) P))

lemma graphMatrix_add_pivot_unit {m : ℕ}
    (y : DetCoeffVar m → ℝ) (t : ℝ) :
    (fun i j => graphMatrix m y i j) +
        t • unit (0 : Fin (m + 1)) (0 : Fin (m + 1)) =
      fun i j => insertDistinguished (pivotZero m)
        (graphRoot m y + t) y (i, j) := by
  ext i j
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp [graphMatrix, insertDistinguished, unit]
    · simp [graphMatrix, insertDistinguished, unit, hj]
  · simp [graphMatrix, insertDistinguished, unit, hi]

lemma tauHomPivotPolynomial_value_zero
    {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P)
    {y : DetCoeffVar m → ℝ}
    (ha : graphLeadingValue m y ≠ 0)
    (hpos : ∀ i j, 0 < graphMatrix m y i j)
    (hcoeff : ∀ i, 0 < graphRowCoeffs m y i) :
    Polynomial.eval (graphRoot m y) (tauHomPivotPolynomial hm P y) = 0 := by
  rw [tauHomPivotPolynomial, toNested_map_eval]
  simpa [peval, graphMatrix] using
    tauHom_graph_value_zero hm P hDPI hRKO ha hpos hcoeff

lemma tauHomPivotPolynomial_derivative_zero
    {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P)
    {y : DetCoeffVar m → ℝ}
    (ha : graphLeadingValue m y ≠ 0)
    (hpos : ∀ i j, 0 < graphMatrix m y i j)
    (hcoeff : ∀ i, 0 < graphRowCoeffs m y i) :
    Polynomial.eval (graphRoot m y)
      (Polynomial.derivative (tauHomPivotPolynomial hm P y)) = 0 := by
  let : NeZero (m + 1) := ⟨by omega⟩
  let hn : 2 ≤ m + 1 := by omega
  let H : Poly (m + 1) :=
    tauHomogenize (R := ℝ) (simplexStar hn) P
  let S : Mat (m + 1) (m + 1) :=
    fun i j => graphMatrix m y i j
  let E : Mat (m + 1) (m + 1) := unit 0 0
  let p : Polynomial ℝ := tauHomPivotPolynomial hm P y
  have hline : (fun t : ℝ => peval H (S + t • E)) =
      fun t : ℝ => Polynomial.eval (graphRoot m y + t) p := by
    funext t
    rw [graphMatrix_add_pivot_unit]
    exact (toNested_map_eval (R := ℝ) (pivotZero m) H
      (graphRoot m y + t) y).symm
  have hdGraph := GeneralAsymmetricC1.hasDerivAt_affine
    (U := S) (V := E)
    ((peval_contDiff H).differentiable (by norm_num) S)
  have hzero := tauHom_graph_pivot_derivative_zero
    hm P hDPI hRKO ha hpos hcoeff
  change (fderiv ℝ (peval H) S) E = 0 at hzero
  rw [hzero, hline] at hdGraph
  have htranslate : HasDerivAt (fun t : ℝ => graphRoot m y + t) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add (graphRoot m y)
  have hdAtTranslated : HasDerivAt (fun x : ℝ => Polynomial.eval x p)
      (Polynomial.eval (graphRoot m y) (Polynomial.derivative p))
      (graphRoot m y + 0) := by
    simpa using Polynomial.hasDerivAt p (graphRoot m y)
  have hdPoly := hdAtTranslated.comp 0 htranslate
  have hdPoly' : HasDerivAt
      (fun t : ℝ => Polynomial.eval (graphRoot m y + t) p)
      (Polynomial.eval (graphRoot m y) (Polynomial.derivative p)) 0 := by
    simpa [Function.comp_def] using hdPoly
  change Polynomial.eval (graphRoot m y) (Polynomial.derivative p) = 0
  exact hdPoly'.unique hdGraph

theorem tauHomPivotPolynomial_double_contact_on_box
    {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P) :
    ∃ l u : DetCoeffVar m → ℝ,
      (∀ q, l q < u q) ∧
      ∀ y : DetCoeffVar m → ℝ,
        (∀ q, y q ∈ Set.Ioo (l q) (u q)) →
        graphLeadingValue m y ≠ 0 ∧
        Polynomial.eval (graphRoot m y) (tauHomPivotPolynomial hm P y) = 0 ∧
        Polynomial.eval (graphRoot m y)
          (Polynomial.derivative (tauHomPivotPolynomial hm P y)) = 0 := by
  obtain ⟨l, u, hlu, hbox⟩ := exists_positive_determinant_graph_box m hm
  refine ⟨l, u, hlu, ?_⟩
  intro y hy
  obtain ⟨ha, hpos, hcoeff⟩ := hbox y hy
  exact ⟨ha,
    tauHomPivotPolynomial_value_zero hm P hDPI hRKO ha hpos hcoeff,
    tauHomPivotPolynomial_derivative_zero hm P hDPI hRKO ha hpos hcoeff⟩

end SquarePolynomial

end

end Cslib.FiniteSampleInformation
