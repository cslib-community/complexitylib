/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.FrobeniusDependence
public import CslibFrontier.Probability.FiniteSampleInformation.ConstantCompensation

/-!
# The copositivity reduction for DPI recognition

This file formalizes the mathematical reduction underlying coNP-hardness.
The complexity-theoretic wrapper (arithmetic-circuit encodings, polynomial-time
reductions, and the external coNP-completeness theorem for rational
copositivity) is not currently available in mathlib.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`CopositiveDPIRecognition.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators
open Set Filter

namespace CopositiveDPIRecognition

open GeneralAsymmetricC1
open FrobeniusDependence
open SquarePolynomial

/-- The quadratic form associated with a real matrix. -/
def quadraticForm {n : ℕ} (A : Mat n n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

/-- Nonnegative vectors of total mass one. -/
def VectorSimplex {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- The usual copositivity condition on the nonnegative orthant. -/
def Copositive {n : ℕ} (A : Mat n n) : Prop :=
  ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → 0 ≤ quadraticForm A x

/-- Copositivity restricted to the probability simplex. -/
def SimplexCopositive {n : ℕ} (A : Mat n n) : Prop :=
  ∀ x : Fin n → ℝ, VectorSimplex x → 0 ≤ quadraticForm A x

lemma quadraticForm_smul {n : ℕ} (A : Mat n n) (c : ℝ)
    (x : Fin n → ℝ) :
    quadraticForm A (c • x) = c ^ 2 * quadraticForm A x := by
  unfold quadraticForm
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma sum_eq_zero_of_nonneg {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 0) : x = 0 := by
  funext i
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => hx i)).mp hsum
  exact hall i (Finset.mem_univ i)

/-- Homogeneity reduces copositivity to the probability simplex. -/
theorem copositive_iff_simplexCopositive {n : ℕ} (A : Mat n n) :
    Copositive A ↔ SimplexCopositive A := by
  constructor
  · intro h x hx
    exact h x hx.1
  · intro h x hx
    let s := ∑ i, x i
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => hx i
    by_cases hs : s = 0
    · have hxzero := sum_eq_zero_of_nonneg hx hs
      subst x
      simp [quadraticForm]
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      let y : Fin n → ℝ := fun i => x i / s
      have hy : VectorSimplex y := by
        constructor
        · intro i
          exact div_nonneg (hx i) hs0
        · change (∑ i, x i / s) = 1
          rw [← Finset.sum_div]
          change s / s = 1
          exact div_self hs
      have hqy := h y hy
      have hxy : x = s • y := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, y]
        field_simp [hs]
      rw [hxy, quadraticForm_smul]
      exact mul_nonneg (sq_nonneg _) hqy

/-- The polynomial family used in the recognition reduction. -/
def recognitionFunctional {n : ℕ} (A : Mat n n) (U : Mat n n) : ℝ :=
  Matrix.det (Matrix.of U) ^ 2 * quadraticForm A (columnMarginal U)

/-- The column marginal as a multivariate polynomial. -/
def columnMarginalPoly (n : ℕ) (a : Fin n) : Poly n :=
  ∑ i : Fin n, MvPolynomial.X (i, a)

lemma peval_columnMarginalPoly {n : ℕ} (a : Fin n) (U : Mat n n) :
    peval (columnMarginalPoly n a) U = columnMarginal U a := by
  simp [columnMarginalPoly, peval, columnMarginal]

/-- The explicit multivariate polynomial representing `recognitionFunctional`. -/
def recognitionPoly {n : ℕ} (A : Mat n n) : Poly n :=
  detPoly n ^ 2 *
    ∑ i : Fin n, ∑ j : Fin n,
      MvPolynomial.C (A i j) * columnMarginalPoly n i *
        columnMarginalPoly n j

lemma peval_recognitionPoly {n : ℕ} (A : Mat n n) (U : Mat n n) :
    peval (recognitionPoly A) U = recognitionFunctional A U := by
  simp only [recognitionPoly, peval, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_sum,
    MvPolynomial.eval_C]
  change peval (detPoly n) U ^ 2 *
      (∑ i, ∑ j, A i j * peval (columnMarginalPoly n i) U *
        peval (columnMarginalPoly n j) U) = recognitionFunctional A U
  rw [peval_detPoly]
  simp_rw [peval_columnMarginalPoly]
  unfold recognitionFunctional quadraticForm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- View the entries of a rational input matrix as real numbers. -/
def rationalMatrixToReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Mat n n :=
  fun i j => (A i j : ℝ)

/-- For a rational input matrix, all coefficients used by the reduction are
rational casts.  The missing arithmetic-circuit layer is only an encoding of
this explicit expression. -/
def rationalRecognitionPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Poly n :=
  recognitionPoly (rationalMatrixToReal A)

lemma columnMarginal_simplex {n m : ℕ} {U : Mat n m} (hU : Simplex U) :
    VectorSimplex (columnMarginal U) := by
  constructor
  · intro a
    exact Finset.sum_nonneg fun i _ => hU.1 i a
  · exact simplex_columnMarginal_sum hU

lemma recognitionFunctional_mul {n : ℕ} (A : Mat n n)
    {T U : Mat n n} (hT : ColumnStochastic T) :
    recognitionFunctional A (T * U) =
      detContraction T * recognitionFunctional A U := by
  unfold recognitionFunctional detContraction
  rw [SquarePolynomial.det_mat_mul, columnMarginal_mul hT]
  ring

lemma recognitionFunctional_dpi_of_simplexCopositive {n : ℕ}
    (A : Mat n n) (hA : SimplexCopositive A) :
    DPI (recognitionFunctional A) := by
  intro T U hT hU
  rw [recognitionFunctional_mul A hT]
  have hd0 : 0 ≤ detContraction T := detContraction_nonneg T
  have hd1 : detContraction T ≤ 1 := detContraction_le_one T hT
  have hFU : 0 ≤ recognitionFunctional A U := by
    exact mul_nonneg (sq_nonneg _)
      (hA (columnMarginal U) (columnMarginal_simplex hU))
  exact mul_le_of_le_one_left hFU hd1

/-- The uniform mass vector on a finite alphabet. -/
def uniformVector (n : ℕ) : Fin n → ℝ :=
  fun _ => 1 / (n : ℝ)

/-- Mix a vector with the uniform mass vector. -/
def positivePerturbation {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun i => (1 - t) * x i + t * uniformVector n i

lemma positivePerturbation_simplex {n : ℕ} (hn : 1 ≤ n)
    {x : Fin n → ℝ} (hx : VectorSimplex x) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    VectorSimplex (positivePerturbation x t) := by
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hx.1 i))
      (mul_nonneg ht0 (by
        exact div_nonneg (by norm_num) (Nat.cast_nonneg n)))
  · simp only [positivePerturbation, uniformVector, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hncast : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    field_simp
    ring

lemma positivePerturbation_pos {n : ℕ} (hn : 1 ≤ n)
    {x : Fin n → ℝ} (hx : VectorSimplex x) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (i : Fin n) :
    0 < positivePerturbation x t i := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hfirst : 0 ≤ (1 - t) * x i :=
    mul_nonneg (sub_nonneg.mpr ht1) (hx.1 i)
  have hsecond : 0 < t * uniformVector n i :=
    mul_pos ht0 (one_div_pos.mpr hnpos)
  exact add_pos_of_nonneg_of_pos hfirst hsecond

lemma continuous_quadraticForm_positivePerturbation {n : ℕ}
    (A : Mat n n) (x : Fin n → ℝ) :
    Continuous (fun t : ℝ => quadraticForm A (positivePerturbation x t)) := by
  unfold quadraticForm positivePerturbation uniformVector
  fun_prop

/-- A negative simplex witness can be moved into the strictly positive
relative interior without losing negativity. -/
lemma exists_positive_simplex_witness_of_negative {n : ℕ} (hn : 1 ≤ n)
    (A : Mat n n) {x : Fin n → ℝ} (hx : VectorSimplex x)
    (hneg : quadraticForm A x < 0) :
    ∃ y : Fin n → ℝ, VectorSimplex y ∧ (∀ i, 0 < y i) ∧
      quadraticForm A y < 0 := by
  have hcont : ContinuousAt
      (fun t : ℝ => quadraticForm A (positivePerturbation x t)) 0 :=
    (continuous_quadraticForm_positivePerturbation A x).continuousAt
  have hzero : positivePerturbation x 0 = x := by
    funext i
    simp [positivePerturbation]
  have hev : ∀ᶠ t : ℝ in nhds 0,
      quadraticForm A (positivePerturbation x t) < 0 := by
    have hneg0 : quadraticForm A (positivePerturbation x 0) < 0 := by
      simpa [hzero] using hneg
    exact hcont.eventually_lt
      (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0) hneg0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let t := min ε 1 / 2
  have ht0 : 0 < t := by
    dsimp [t]
    positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    have := min_le_right ε 1
    linarith
  have htdist : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    dsimp [t]
    have := min_le_left ε 1
    linarith
  refine ⟨positivePerturbation x t,
    positivePerturbation_simplex hn hx ht0.le ht1,
    fun i => positivePerturbation_pos hn hx ht0 ht1 i,
    hball htdist⟩

/-- A diagonal joint table with the prescribed diagonal masses. -/
def diagonalJoint {n : ℕ} (x : Fin n → ℝ) : Mat n n :=
  fun i j => if i = j then x i else 0

lemma diagonalJoint_eq_matrix_diagonal {n : ℕ} (x : Fin n → ℝ) :
    Matrix.of (diagonalJoint x) = Matrix.diagonal x := by
  ext i j
  simp [diagonalJoint, Matrix.diagonal_apply]

lemma diagonalJoint_simplex {n : ℕ} {x : Fin n → ℝ}
    (hx : VectorSimplex x) : Simplex (diagonalJoint x) := by
  constructor
  · intro i j
    simp only [diagonalJoint]
    split_ifs
    · exact hx.1 i
    · exact le_rfl
  · simp [mass, diagonalJoint, hx.2]

lemma diagonalJoint_columnMarginal {n : ℕ} (x : Fin n → ℝ) :
    columnMarginal (diagonalJoint x) = x := by
  funext j
  simp [columnMarginal, diagonalJoint]

lemma diagonalJoint_det_pos {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) :
    0 < Matrix.det (Matrix.of (diagonalJoint x)) := by
  rw [diagonalJoint_eq_matrix_diagonal, Matrix.det_diagonal]
  exact Finset.prod_pos fun i _ => hx i

/-- The channel that replaces every input by a uniformly random state. -/
def uniformErasure (n : ℕ) : Mat n n :=
  fun _ _ => 1 / (n : ℝ)

lemma uniformErasure_columnStochastic {n : ℕ} (hn : 1 ≤ n) :
    ColumnStochastic (uniformErasure n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  constructor
  · intro i j
    exact one_div_nonneg.mpr hnpos.le
  · intro j
    simp only [uniformErasure, one_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp

lemma uniformErasure_det_zero {n : ℕ} (hn : 2 ≤ n) :
    Matrix.det (Matrix.of (uniformErasure n)) = 0 := by
  let u : Fin n → ℝ := fun _ => 1 / (n : ℝ)
  let one : Fin n → ℝ := fun _ => 1
  have heq : Matrix.of (uniformErasure n) = Matrix.vecMulVec u one := by
    ext i j
    simp [uniformErasure, u, one, Matrix.vecMulVec]
  rw [heq]
  have : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa using (lt_of_lt_of_le Nat.one_lt_two hn))
  exact Matrix.det_vecMulVec u one

lemma simplexCopositive_of_recognitionFunctional_dpi {n : ℕ} (hn : 2 ≤ n)
    (A : Mat n n) (hDPI : DPI (recognitionFunctional A)) :
    SimplexCopositive A := by
  intro x hx
  by_contra hnot
  have hneg : quadraticForm A x < 0 := lt_of_not_ge hnot
  have hn1 : 1 ≤ n := le_trans (by omega : 1 ≤ 2) hn
  obtain ⟨y, hy, hypos, hqy⟩ :=
    exists_positive_simplex_witness_of_negative hn1 A hx hneg
  let U := diagonalJoint y
  let T := uniformErasure n
  have hU : Simplex U := diagonalJoint_simplex hy
  have hT : ColumnStochastic T := uniformErasure_columnStochastic hn1
  have hdetU : 0 < Matrix.det (Matrix.of U) := diagonalJoint_det_pos hypos
  have hFUneg : recognitionFunctional A U < 0 := by
    unfold recognitionFunctional
    rw [diagonalJoint_columnMarginal]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hdetU) hqy
  have hdetT : Matrix.det (Matrix.of T) = 0 := uniformErasure_det_zero hn
  have hzero : recognitionFunctional A (T * U) = 0 := by
    rw [recognitionFunctional_mul A hT]
    simp [detContraction, hdetT]
  have hle := hDPI T U hT hU
  rw [hzero] at hle
  linarith

/-- Exact semantic reduction: recognizing DPI for the restricted polynomial
family is equivalent to copositivity. -/
theorem recognitionFunctional_dpi_iff_copositive {n : ℕ} (hn : 2 ≤ n)
    (A : Mat n n) :
    DPI (recognitionFunctional A) ↔ Copositive A := by
  rw [copositive_iff_simplexCopositive]
  exact ⟨simplexCopositive_of_recognitionFunctional_dpi hn A,
    recognitionFunctional_dpi_of_simplexCopositive A⟩

theorem recognitionPoly_dpi_iff_copositive {n : ℕ} (hn : 2 ≤ n)
    (A : Mat n n) :
    PolynomialDPI (recognitionPoly A) ↔ Copositive A := by
  change DPI (peval (recognitionPoly A)) ↔ Copositive A
  have heq : peval (recognitionPoly A) = recognitionFunctional A := by
    funext U
    exact peval_recognitionPoly A U
  rw [heq]
  exact recognitionFunctional_dpi_iff_copositive hn A

/-- The same equivalence for the paper's rational input matrices.  Symmetry is
not needed for the semantic equivalence, so this is slightly stronger than the
restricted family used in the hardness statement. -/
theorem rationalRecognitionPoly_dpi_iff_copositive {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    PolynomialDPI (rationalRecognitionPoly A) ↔
      Copositive (rationalMatrixToReal A) := by
  exact recognitionPoly_dpi_iff_copositive hn (rationalMatrixToReal A)

lemma recognitionFunctional_rowSymmetric {n : ℕ} (A : Mat n n) :
    ∀ (σ : Equiv.Perm (Fin n)) (U : Mat n n),
      recognitionFunctional A
        ((fun i j => σ.permMatrix ℝ i j : Mat n n) * U) =
      recognitionFunctional A U := by
  intro σ U
  have hQ := SquarePolynomial.permMatrix_columnStochastic σ
  rw [recognitionFunctional_mul A hQ]
  have hd : detContraction
      (fun i j => (σ.permMatrix ℝ i j : ℝ)) = 1 := by
    unfold detContraction
    change Matrix.det (σ.permMatrix ℝ) ^ 2 = 1
    rw [Matrix.det_permutation]
    have habs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, Equiv.Perm.sign_abs]
      norm_num
    nlinarith [sq_abs (((Equiv.Perm.sign σ : ℤ) : ℝ))]
  rw [hd, one_mul]

lemma recognitionFunctional_rko {n : ℕ} (hn : 2 ≤ n) (A : Mat n n) :
    RKO (recognitionFunctional A) := by
  have : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa using (lt_of_lt_of_le Nat.one_lt_two hn))
  intro x y hU
  unfold recognitionFunctional
  change Matrix.det (Matrix.vecMulVec x y) ^ 2 * _ = 0
  rw [Matrix.det_vecMulVec x y]
  simp

theorem recognitionPoly_rowSymmetricOnSimplex {n : ℕ} (A : Mat n n) :
    RowSymmetricOnSimplex (recognitionPoly A) := by
  intro σ U hU
  rw [peval_recognitionPoly, peval_recognitionPoly]
  exact recognitionFunctional_rowSymmetric A σ U

theorem recognitionPoly_rko {n : ℕ} (hn : 2 ≤ n) (A : Mat n n) :
    PolynomialRKO (recognitionPoly A) := by
  intro x y hU
  rw [peval_recognitionPoly]
  exact recognitionFunctional_rko hn A x y hU

/-- The determinant factor gives the paper-facing rank-at-most-one vanishing
condition on the simplex. -/
theorem recognitionFunctional_rankOneVanishing {n : ℕ} (hn : 2 ≤ n)
    (A : Mat n n) : RankOneVanishing (recognitionFunctional A) :=
  (GeneralAsymmetricC1.rko_iff_rankOneVanishing _).mp
    (recognitionFunctional_rko hn A)

theorem recognitionPoly_rankOneVanishing {n : ℕ} (hn : 2 ≤ n)
    (A : Mat n n) : RankOneVanishing (peval (recognitionPoly A)) :=
  (GeneralAsymmetricC1.rko_iff_rankOneVanishing _).mp
    (recognitionPoly_rko hn A)

/-- A lightweight semantic many-one reduction, separated from any machine
encoding or running-time claim. -/
def SemanticManyOneReduction {α β : Type*}
    (P : α → Prop) (Q : β → Prop) (f : α → β) : Prop :=
  ∀ a, Q (f a) ↔ P a

theorem copositive_semantically_reduces_to_dpi (n : ℕ) (hn : 2 ≤ n) :
    SemanticManyOneReduction
      (Copositive : Mat n n → Prop)
      (fun F : Mat n n → ℝ => DPI F)
      recognitionFunctional := by
  intro A
  exact recognitionFunctional_dpi_iff_copositive hn A


end CopositiveDPIRecognition

end

end Cslib.FiniteSampleInformation
