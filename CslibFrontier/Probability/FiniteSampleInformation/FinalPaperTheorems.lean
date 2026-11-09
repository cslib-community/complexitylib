/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.GeneralAsymmetricC1
public import CslibFrontier.Probability.FiniteSampleInformation.FrobeniusDependence
public import CslibFrontier.Probability.FiniteSampleInformation.ConstantCompensation
public import CslibFrontier.Probability.FiniteSampleInformation.WideSimplexTheorem

/-!
# Paper-facing consequences for the final manuscript

This file supplies the two short boundary arguments needed to state the final
paper's zero-row and independence-faithfulness theorems exactly.  The existing
`n ≥ 3` differential proof is reused unchanged.  When `n = 2`, a simplex
matrix with a zero row is already an outer product, so rank-one vanishing
settles the remaining case directly.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`FinalPaperTheorems.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators
open Set

namespace GeneralAsymmetricC1

/-- The zero-row vanishing principle in the full paper range `n ≥ 2`.

The only new case beyond `zero_row_vanishing_of_contDiffOnSimplex` is `n = 2`.
There a matrix with a zero row has only one possibly nonzero row and is an
outer product. -/
theorem zero_row_vanishing_of_contDiffOnSimplex_ge_two
    {n m : ℕ} [NeZero m]
    (hn : 2 ≤ n) {F : Mat n m → ℝ} (hF : ContDiffOnSimplex F)
    (hDPI : DPI F) (hRKO : RKO F)
    {U : Mat n m} (hU : Simplex U) {r : Fin n}
    (hr : ∀ a, U r a = 0) :
    F U = 0 := by
  by_cases hn3 : 3 ≤ n
  · exact zero_row_vanishing_of_contDiffOnSimplex hn3 hF hDPI hRKO hU hr
  · have hn2 : n = 2 := by omega
    subst n
    fin_cases r
    · let x : Fin 2 → ℝ := rowIndicator 1
      let y : Fin m → ℝ := columnSums U
      have houter : U = outer x y := by
        ext i a
        fin_cases i
        · have hrow : U 0 a = 0 := by simpa using hr a
          simp [x, y, outer, rowIndicator, columnSums, hrow]
        · have hrow : U 0 a = 0 := by simpa using hr a
          simp [x, y, outer, rowIndicator, columnSums, hrow]
      rw [houter]
      exact hRKO x y (houter ▸ hU)
    · let x : Fin 2 → ℝ := rowIndicator 0
      let y : Fin m → ℝ := columnSums U
      have houter : U = outer x y := by
        ext i a
        fin_cases i
        · have hrow : U 1 a = 0 := by simpa using hr a
          simp [x, y, outer, rowIndicator, columnSums, hrow]
        · have hrow : U 1 a = 0 := by simpa using hr a
          simp [x, y, outer, rowIndicator, columnSums, hrow]
      rw [houter]
      exact hRKO x y (houter ▸ hU)

/-- Paper-facing zero-row theorem with exactly the manuscript's regularity
assumption: `F` is C¹ on an open neighborhood containing the simplex. -/
theorem zero_row_vanishing_openNeighborhood
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (Ω : Set (Mat n m)) (hΩ : IsOpen Ω)
    (hsimplex : ∀ U, Simplex U → U ∈ Ω)
    (F : Mat n m → ℝ) (hF : ContDiffOn ℝ 1 F Ω)
    (hDPI : DPI F) (hRankOne : RankOneVanishing F)
    {U : Mat n m} (hU : Simplex U) {r : Fin n}
    (hr : ∀ a, U r a = 0) :
    F U = 0 := by
  let : NeZero n := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  apply zero_row_vanishing_of_contDiffOnSimplex_ge_two hn
  · exact fun X hX => (hΩ.contDiffOn_iff.mp hF) (hsimplex X hX)
  · exact hDPI
  · exact (rko_iff_rankOneVanishing F).mpr hRankOne
  · exact hU
  · exact hr

/-- A functional detects independence exactly when its simplex zero set is
the rank-one locus. -/
@[expose] def IndependenceFaithful {n m : ℕ} (F : Mat n m → ℝ) : Prop :=
  ∀ U, Simplex U → (F U = 0 ↔ (Matrix.of U).rank = 1)

/-- The paper's notion of C¹-extendability: an ambient representative is C¹
on some open neighborhood of the closed simplex. -/
@[expose] def C1Extendable {n m : ℕ} (F : Mat n m → ℝ) : Prop :=
  ∃ Ω : Set (Mat n m), IsOpen Ω ∧
    (∀ U, Simplex U → U ∈ Ω) ∧ ContDiffOn ℝ 1 F Ω

end GeneralAsymmetricC1

namespace FrobeniusDependence

open GeneralAsymmetricC1

/-- On two rows, a column-stochastic matrix acts on every zero-sum column by
the scalar `T 0 0 - T 0 1`. -/
lemma mul_zeroSum_two_rows
    {m : ℕ} {T : Mat 2 2} (hT : ColumnStochastic T)
    {V : Mat 2 m} (hzero : ∀ a, ∑ i, V i a = 0) :
    T * V = (T 0 0 - T 0 1) • V := by
  ext i a
  fin_cases i
  · have hsum : V 0 a + V 1 a = 0 := by
      simpa [Fin.sum_univ_two] using hzero a
    have hva : V 1 a = -V 0 a := by linarith
    simp [mat_mul_apply, Fin.sum_univ_two, hva]
    ring
  · have hcol0 := hT.2 (0 : Fin 2)
    have hcol1 := hT.2 (1 : Fin 2)
    have hsum : V 0 a + V 1 a = 0 := by
      simpa [Fin.sum_univ_two] using hzero a
    have hva : V 1 a = -V 0 a := by linarith
    have h10 : T 1 0 = 1 - T 0 0 := by
      simp [Fin.sum_univ_two] at hcol0
      linarith
    have h11 : T 1 1 = 1 - T 0 1 := by
      simp [Fin.sum_univ_two] at hcol1
      linarith
    simp [mat_mul_apply, Fin.sum_univ_two, hva, h10, h11]
    ring

/-- Exact binary transformation rule for the Frobenius dependence measure. -/
theorem fdi_mul_two_rows
    {m : ℕ} {T : Mat 2 2} (hT : ColumnStochastic T)
    {U : Mat 2 m} (hU : Simplex U) :
    fdi (T * U) = (T 0 0 - T 0 1) ^ 2 * fdi U := by
  unfold fdi
  rw [centered_mul hT,
    mul_zeroSum_two_rows hT (centered_column_sum_zero hU)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma det_two_eq_zeroSum_factor
    {T : Mat 2 2} (hT : ColumnStochastic T) :
    Matrix.det (Matrix.of T) = T 0 0 - T 0 1 := by
  have hcol0 := hT.2 (0 : Fin 2)
  have hcol1 := hT.2 (1 : Fin 2)
  have h10 : T 1 0 = 1 - T 0 0 := by
    simp [Fin.sum_univ_two] at hcol0
    linarith
  have h11 : T 1 1 = 1 - T 0 1 := by
    simp [Fin.sum_univ_two] at hcol1
    linarith
  rw [Matrix.det_fin_two]
  change T 0 0 * T 1 1 - T 0 1 * T 1 0 = T 0 0 - T 0 1
  rw [h10, h11]
  ring

/-- The transformation rule in the determinant form displayed in the paper. -/
theorem fdi_mul_two_rows_det
    {m : ℕ} {T : Mat 2 2} (hT : ColumnStochastic T)
    {U : Mat 2 m} (hU : Simplex U) :
    fdi (T * U) = Matrix.det (Matrix.of T) ^ 2 * fdi U := by
  rw [fdi_mul_two_rows hT hU, det_two_eq_zeroSum_factor hT]

/-- Every `2 × 2` column-stochastic matrix contracts the binary zero-sum
direction. -/
lemma binary_zeroSum_factor_sq_le_one
    {T : Mat 2 2} (hT : ColumnStochastic T) :
    (T 0 0 - T 0 1) ^ 2 ≤ 1 := by
  have h00 := hT.1 (0 : Fin 2) (0 : Fin 2)
  have h01 := hT.1 (0 : Fin 2) (1 : Fin 2)
  have hc0 := hT.2 (0 : Fin 2)
  have hc1 := hT.2 (1 : Fin 2)
  simp only [Fin.isValue, Fin.sum_univ_two] at hc0 hc1
  have h00le : T 0 0 ≤ 1 := by linarith [hT.1 (1 : Fin 2) (0 : Fin 2)]
  have h01le : T 0 1 ≤ 1 := by linarith [hT.1 (1 : Fin 2) (1 : Fin 2)]
  nlinarith [sq_nonneg (T 0 0 - T 0 1 - 1),
    sq_nonneg (T 0 0 - T 0 1 + 1)]

/-- In the binary processed-alphabet case, FDI satisfies the full left DPI,
not merely the restricted-channel DPI. -/
theorem fdi_full_dpi_two_rows {m : ℕ} :
    DPI (fdi : Mat 2 m → ℝ) := by
  intro T U hT hU
  rw [fdi_mul_two_rows hT hU]
  exact mul_le_of_le_one_left (fdi_nonneg U)
    (binary_zeroSum_factor_sq_le_one hT)

/-- FDI is a polynomial, hence globally C¹. -/
theorem contDiff_fdi {n m : ℕ} :
    ContDiff ℝ 1 (fdi : Mat n m → ℝ) := by
  unfold fdi centered rowMarginal columnMarginal
  fun_prop

end FrobeniusDependence

namespace GramDependence

open GeneralAsymmetricC1

/-- The Gram-determinant dependence functional used as the binary witness in
the paper: `det (U Uᵀ)`. -/
@[expose] def gramDet {n m : ℕ} (U : Mat n m) : ℝ :=
  Matrix.det (Matrix.of U * (Matrix.of U).transpose)

/-- The Gram determinant as a multivariate polynomial in the entries of the
generic `n × m` matrix. -/
def gramDetPoly (n m : ℕ) : WidePolynomial.WidePoly n m :=
  Matrix.det
    (Matrix.mvPolynomialX (Fin n) (Fin m) ℝ *
      (Matrix.mvPolynomialX (Fin n) (Fin m) ℝ).transpose)

/-- Evaluation of the generic Gram-determinant polynomial is the
Gram-determinant functional. -/
theorem peval_gramDetPoly {n m : ℕ} (U : Mat n m) :
    WidePolynomial.peval (gramDetPoly n m) U = gramDet U := by
  unfold WidePolynomial.peval gramDetPoly gramDet
  let e : WidePolynomial.WidePoly n m →+* ℝ :=
    MvPolynomial.eval (fun ia => U ia.1 ia.2)
  change e (Matrix.det
    (Matrix.mvPolynomialX (Fin n) (Fin m) ℝ *
      (Matrix.mvPolynomialX (Fin n) (Fin m) ℝ).transpose)) = _
  rw [e.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [e, Matrix.mul_apply]

lemma genericGramEntry_isHomogeneous {n m : ℕ} (i j : Fin n) :
    (Matrix.mvPolynomialX (Fin n) (Fin m) ℝ *
      (Matrix.mvPolynomialX (Fin n) (Fin m) ℝ).transpose) i j
      |>.IsHomogeneous 2 := by
  rw [Matrix.mul_apply]
  apply MvPolynomial.IsHomogeneous.sum Finset.univ
  intro a ha
  simpa using
    (MvPolynomial.isHomogeneous_X ℝ (i, a)).mul
      (MvPolynomial.isHomogeneous_X ℝ (j, a))

/-- The generic Gram determinant is homogeneous of degree `2n`. -/
lemma gramDetPoly_isHomogeneous (n m : ℕ) :
    (gramDetPoly n m).IsHomogeneous (2 * n) := by
  rw [gramDetPoly, Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum Finset.univ
  intro σ hσ
  have hprod :
      (∏ i : Fin n,
        (Matrix.mvPolynomialX (Fin n) (Fin m) ℝ *
          (Matrix.mvPolynomialX (Fin n) (Fin m) ℝ).transpose) (σ i) i)
        |>.IsHomogeneous (∑ _i : Fin n, 2) := by
    exact MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 2)
      (fun i hi => genericGramEntry_isHomogeneous (σ i) i)
  have hdegree : (∑ _i : Fin n, 2) = 2 * n := by
    simp [Nat.mul_comm]
  rw [hdegree] at hprod
  simpa using hprod.C_mul (((Equiv.Perm.sign σ : ℤ) : ℝ))

/-- When `n ≤ m`, the generic Gram determinant is not the zero polynomial. -/
lemma gramDetPoly_ne_zero {n m : ℕ} (hnm : n ≤ m) :
    gramDetPoly n m ≠ 0 := by
  let S : Fin n ↪o Fin m := Fin.castLEOrderEmb hnm
  let U : Mat n m := fun i a => if a = S i then 1 else 0
  have hgram : Matrix.of U * (Matrix.of U).transpose =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [U, S, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  intro hzero
  have heval : WidePolynomial.peval (gramDetPoly n m) U = 0 := by
    rw [hzero]
    simp [WidePolynomial.peval]
  rw [peval_gramDetPoly, gramDet, hgram, Matrix.det_one] at heval
  norm_num at heval

/-- In the non-tall range, the Gram-determinant polynomial has exact total
degree `2n`. -/
lemma gramDetPoly_totalDegree {n m : ℕ} (hnm : n ≤ m) :
    (gramDetPoly n m).totalDegree = 2 * n :=
  (gramDetPoly_isHomogeneous n m).totalDegree (gramDetPoly_ne_zero hnm)

/-- A Gram determinant is nonnegative. -/
lemma gramDet_nonneg {n m : ℕ} (U : Mat n m) : 0 ≤ gramDet U := by
  unfold gramDet
  have hpsd : (Matrix.of U * (Matrix.of U).transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_self_mul_conjTranspose (Matrix.of U))
  exact hpsd.det_nonneg

/-- A square real matrix has nonzero determinant exactly when it has full
matrix rank. -/
lemma det_ne_zero_iff_rank_eq_height {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det ≠ 0 ↔ A.rank = n := by
  constructor
  · intro hdet
    simpa using (Matrix.linearIndependent_rows_of_det_ne_zero hdet).rank_matrix
  · intro hrank
    have hli : LinearIndependent ℝ A.row := by
      rw [Matrix.rank_eq_finrank_span_row] at hrank
      exact linearIndependent_iff_card_eq_finrank_span.mpr (by
        simpa [Set.finrank] using hrank.symm)
    have hunitA : IsUnit A := Matrix.linearIndependent_row_iff_isUnit.mp hli
    have hunitDet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunitA
    exact isUnit_iff_ne_zero.mp hunitDet

/-- The Gram determinant is nonzero exactly at matrices of full row rank. -/
lemma gramDet_ne_zero_iff_rank_eq_height {n m : ℕ} (U : Mat n m) :
    gramDet U ≠ 0 ↔ (Matrix.of U).rank = n := by
  rw [gramDet, det_ne_zero_iff_rank_eq_height,
    Matrix.rank_self_mul_transpose]

/-- Equivalently, the Gram determinant vanishes exactly below full row rank. -/
lemma gramDet_eq_zero_iff_rank_lt_height {n m : ℕ} (U : Mat n m) :
    gramDet U = 0 ↔ (Matrix.of U).rank < n := by
  have hle : (Matrix.of U).rank ≤ n := Matrix.rank_le_height (Matrix.of U)
  constructor
  · intro hzero
    have hne : (Matrix.of U).rank ≠ n := by
      intro hrank
      exact (gramDet_ne_zero_iff_rank_eq_height U).2 hrank hzero
    omega
  · intro hlt
    by_contra hne
    have hrank := (gramDet_ne_zero_iff_rank_eq_height U).1 hne
    omega

/-- On the binary simplex, vanishing of the Gram determinant is exactly rank
one, because a simplex matrix cannot have rank zero. -/
theorem gramDet_eq_zero_iff_rank_eq_one {m : ℕ} (U : Mat 2 m)
    (hU : Simplex U) :
    gramDet U = 0 ↔ (Matrix.of U).rank = 1 := by
  have hle : (Matrix.of U).rank ≤ 2 := Matrix.rank_le_height (Matrix.of U)
  have hne0 : (Matrix.of U).rank ≠ 0 :=
    FrobeniusDependence.simplex_rank_ne_zero hU
  constructor
  · intro hzero
    have hne2 : (Matrix.of U).rank ≠ 2 := by
      intro hrank
      exact (gramDet_ne_zero_iff_rank_eq_height U).2 hrank hzero
    omega
  · intro hrank
    by_contra hne
    have hrank2 := (gramDet_ne_zero_iff_rank_eq_height U).1 hne
    omega

lemma matrixOf_mul {n p m : ℕ} (T : Mat n p) (U : Mat p m) :
    Matrix.of (T * U) = Matrix.of T * Matrix.of U := by
  ext i a
  simp [mat_mul_apply, Matrix.mul_apply]

/-- Exact transformation law for the Gram determinant under left matrix
multiplication. -/
theorem gramDet_mul {n m : ℕ} (T : Mat n n) (U : Mat n m) :
    gramDet (T * U) = Matrix.det (Matrix.of T) ^ 2 * gramDet U := by
  unfold gramDet
  rw [matrixOf_mul, Matrix.transpose_mul]
  calc
    Matrix.det ((Matrix.of T * Matrix.of U) *
        ((Matrix.of U).transpose * (Matrix.of T).transpose)) =
        Matrix.det (Matrix.of T *
          ((Matrix.of U * (Matrix.of U).transpose) *
            (Matrix.of T).transpose)) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.det (Matrix.of T) ^ 2 *
          Matrix.det (Matrix.of U * (Matrix.of U).transpose) := by
          rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
          ring

/-- In every dimension, the Gram determinant satisfies left data processing
under column-stochastic processing. -/
theorem gramDet_dpi {n m : ℕ} :
    DPI (gramDet : Mat n m → ℝ) := by
  intro T U hT hU
  rw [gramDet_mul]
  exact mul_le_of_le_one_left (gramDet_nonneg U)
    (by simpa [SquarePolynomial.detContraction] using
      SquarePolynomial.detContraction_le_one T hT)

/-- For at least two rows, the Gram determinant vanishes on every rank-one
simplex matrix. -/
theorem gramDet_rko {n m : ℕ} (hn : 2 ≤ n) :
    RKO (gramDet : Mat n m → ℝ) := by
  intro x y hsimplex
  exact (gramDet_eq_zero_iff_rank_lt_height _).2
    (lt_of_le_of_lt (rank_outer_le_one x y) hn)

theorem gramDetPoly_dpi {n m : ℕ} :
    WidePolynomial.PolynomialDPI (gramDetPoly n m) := by
  intro T U hT hU
  rw [peval_gramDetPoly, peval_gramDetPoly]
  exact gramDet_dpi T U hT hU

theorem gramDetPoly_rko {n m : ℕ} (hn : 2 ≤ n) :
    WidePolynomial.PolynomialRKO (gramDetPoly n m) := by
  intro x y hsimplex
  rw [peval_gramDetPoly]
  exact gramDet_rko hn x y hsimplex

lemma tauHomogenize_eq_self_of_isHomogeneous
    {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
    (star : σ) {P : MvPolynomial σ R} {d : ℕ}
    (hP : P.IsHomogeneous d) (hPne : P ≠ 0) :
    SquarePolynomial.tauHomogenize star P = P := by
  rw [SquarePolynomial.tauHomogenize, hP.totalDegree hPne]
  simp [MvPolynomial.homogeneousComponent_of_mem hP]

lemma tauHomogenizeWide_gramDetPoly {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnm : n ≤ m) :
    WidePolynomial.tauHomogenizeWide hn hm (gramDetPoly n m) =
      gramDetPoly n m := by
  exact tauHomogenize_eq_self_of_isHomogeneous
    (WidePolynomial.wideStar hn hm) (gramDetPoly_isHomogeneous n m)
      (gramDetPoly_ne_zero hnm)

/-- In the paper's non-tall range, the generic Gram determinant belongs to
the square of the generic maximal-minor ideal. -/
theorem gramDetPoly_mem_maximalMinorIdeal_sq
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    gramDetPoly n m ∈ WidePolynomial.maximalMinorIdeal n m ^ 2 := by
  cases n with
  | zero => omega
  | succ k =>
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ m by omega)
      have hmem := WidePolynomial.tauHomogenizeWide_mem_maximalMinorIdeal_sq
        (k := k) (r := r) (by omega) (by omega) (gramDetPoly (k + 1) (k + r))
          gramDetPoly_dpi (gramDetPoly_rko (by omega))
      rw [tauHomogenizeWide_gramDetPoly (hnm := hnm)] at hmem
      exact hmem

/-- The complete Gram-determinant monotone proposition from the paper. -/
theorem gramDetPoly_paper_properties
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    gramDetPoly n m ≠ 0 ∧
      (gramDetPoly n m).totalDegree = 2 * n ∧
      WidePolynomial.PolynomialDPI (gramDetPoly n m) ∧
      WidePolynomial.PolynomialRKO (gramDetPoly n m) ∧
      gramDetPoly n m ∈ WidePolynomial.maximalMinorIdeal n m ^ 2 := by
  exact ⟨gramDetPoly_ne_zero hnm, gramDetPoly_totalDegree hnm,
    gramDetPoly_dpi, gramDetPoly_rko hn,
    gramDetPoly_mem_maximalMinorIdeal_sq hn hnm⟩

/-- The Gram determinant is a polynomial in the entries and is therefore
globally C¹. -/
theorem contDiff_gramDet {n m : ℕ} :
    ContDiff ℝ 1 (gramDet : Mat n m → ℝ) := by
  unfold gramDet
  rw [show (fun U : Mat n m =>
      Matrix.det (Matrix.of U * (Matrix.of U).transpose)) =
      (fun U : Mat n m =>
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
          ∏ i, ∑ a, U (σ i) a * U i a) by
    funext U
    rw [Matrix.det_apply]
    rfl]
  fun_prop

/-- For two processed states the Gram determinant obeys the full left DPI. -/
theorem gramDet_full_dpi_two_rows {m : ℕ} :
    DPI (gramDet : Mat 2 m → ℝ) := by
  exact gramDet_dpi

/-- The Gram determinant detects independence exactly on the binary
probability simplex. -/
theorem gramDet_independenceFaithful {m : ℕ} :
    IndependenceFaithful (gramDet : Mat 2 m → ℝ) := by
  intro U hU
  exact gramDet_eq_zero_iff_rank_eq_one U hU

end GramDependence

namespace GeneralAsymmetricC1

open FrobeniusDependence
open GramDependence

/-- A concrete dependent simplex point with a zero row, available whenever
there are at least three rows and two columns. -/
def dependentZeroRowWitness {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) : Mat n m :=
  (1 / 2 : ℝ) • unit ⟨0, by omega⟩ ⟨0, by omega⟩ +
    (1 / 2 : ℝ) • unit ⟨1, by omega⟩ ⟨1, by omega⟩

lemma dependentZeroRowWitness_simplex {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) :
    Simplex (dependentZeroRowWitness hn hm) := by
  constructor
  · intro i a
    simp only [dependentZeroRowWitness, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [unit_apply]
    split_ifs <;> norm_num
  · simp [dependentZeroRowWitness]
    norm_num

lemma dependentZeroRowWitness_row_two {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) :
    ∀ a, dependentZeroRowWitness hn hm ⟨2, by omega⟩ a = 0 := by
  intro a
  simp [dependentZeroRowWitness, unit]

lemma dependentZeroRowWitness_rank_not_le_one
    {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) :
    ¬(Matrix.of (dependentZeroRowWitness hn hm)).rank ≤ 1 := by
  intro hrank
  obtain ⟨x, y, hxy⟩ := exists_outer_of_rank_le_one
    (dependentZeroRowWitness hn hm) hrank
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let a0 : Fin m := ⟨0, by omega⟩
  let a1 : Fin m := ⟨1, by omega⟩
  have h00 := congrFun (congrFun hxy i0) a0
  have h01 := congrFun (congrFun hxy i0) a1
  have h11 := congrFun (congrFun hxy i1) a1
  have hx0 : x i0 ≠ 0 := by
    intro hx
    simp [dependentZeroRowWitness, unit, outer, i0, a0, hx] at h00
  have hy1 : y a1 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hx0
    simpa [dependentZeroRowWitness, unit, outer, i0, i1, a0, a1] using h01.symm
  simp [dependentZeroRowWitness, unit, outer, i1, a1, hy1] at h11

/-- If the processed alphabet has at least three states, no C¹-extendable
left-DPI functional can detect independence exactly. -/
theorem no_C1Extendable_independenceFaithful_dpi_of_three_le
    {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) :
    ¬∃ F : Mat n m → ℝ, C1Extendable F ∧ DPI F ∧ IndependenceFaithful F := by
  rintro ⟨F, ⟨Ω, hΩ, hsimp, hF⟩, hDPI, hfaith⟩
  let U : Mat n m := dependentZeroRowWitness hn hm
  have hU : Simplex U := dependentZeroRowWitness_simplex hn hm
  have hzero : F U = 0 :=
    zero_row_vanishing_openNeighborhood (le_trans (by norm_num) hn) hm
      Ω hΩ hsimp F hF hDPI (by
        intro X hX hle
        have hne : (Matrix.of X).rank ≠ 0 :=
          FrobeniusDependence.simplex_rank_ne_zero hX
        have hrank : (Matrix.of X).rank = 1 :=
          Nat.le_antisymm hle (Nat.one_le_iff_ne_zero.mpr hne)
        exact (hfaith X hX).2 hrank)
      hU (dependentZeroRowWitness_row_two hn hm)
  have hrank : (Matrix.of U).rank = 1 := (hfaith U hU).1 hzero
  exact dependentZeroRowWitness_rank_not_le_one hn hm hrank.le

/-- Final-paper classification: a C¹-extendable independence-faithful
functional satisfying left DPI exists exactly when the processed variable is
binary.  The Gram determinant supplies the paper's binary witness. -/
theorem exists_C1Extendable_independenceFaithful_dpi_iff
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∃ F : Mat n m → ℝ, C1Extendable F ∧ DPI F ∧ IndependenceFaithful F) ↔
      n = 2 := by
  constructor
  · intro hexists
    by_contra hn2
    have hn3 : 3 ≤ n := by omega
    exact no_C1Extendable_independenceFaithful_dpi_of_three_le hn3 hm hexists
  · intro hn2
    subst n
    refine ⟨gramDet, ?_, gramDet_full_dpi_two_rows, gramDet_independenceFaithful⟩
    · refine ⟨Set.univ, isOpen_univ, ?_, ?_⟩
      · intro U hU
        exact Set.mem_univ U
      · exact contDiff_gramDet.contDiffOn

end GeneralAsymmetricC1


end

end Cslib.FiniteSampleInformation
