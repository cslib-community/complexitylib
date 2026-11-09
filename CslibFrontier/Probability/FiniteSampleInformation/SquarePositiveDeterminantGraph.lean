/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareTauHomogenization
public import CslibFrontier.Probability.FiniteSampleInformation.SquareOpenBoxIdentity
public import CslibFrontier.Probability.FiniteSampleInformation.SquareDeterminantGauss

/-!
# A positive singular graph for the generic determinant

The top-left entry is the pivot.  The remaining entries determine a lower
right block `B`, the tail `z` of the top row, and the head `c` of the other
rows.  When `B` is invertible, `z B⁻¹` gives the coefficients expressing the
top row as a combination of the other rows.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquarePositiveDeterminantGraph.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace SquarePolynomial

section GraphCoordinates

variable (m : ℕ)

/-- The coefficient variable for an entry in the first row away from the pivot. -/
def tailVar (j : Fin m) : DetCoeffVar m :=
  ⟨((0 : Fin (m + 1)), j.succ), by
    intro h
    have := congrArg Prod.snd h
    simp at this⟩

/-- The coefficient variable for an entry in the first column away from the pivot. -/
def firstColumnVar (i : Fin m) : DetCoeffVar m :=
  ⟨(i.succ, (0 : Fin (m + 1))), by
    intro h
    have := congrArg Prod.fst h
    simp at this⟩

/-- The complementary square block in the determinant-root chart. -/
def graphMinor (y : DetCoeffVar m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => y (lowerVarEmbedding m (i, j))

/-- The first-row entries away from the distinguished pivot. -/
def graphTail (y : DetCoeffVar m → ℝ) : Fin m → ℝ :=
  fun j => y (tailVar m j)

/-- The first-column entries away from the distinguished pivot. -/
def graphFirstColumn (y : DetCoeffVar m → ℝ) : Fin m → ℝ :=
  fun i => y (firstColumnVar m i)

/-- Coefficients expressing the distinguished row in terms of the remaining rows. -/
@[expose] def graphRowCoeffs (y : DetCoeffVar m → ℝ) : Fin m → ℝ :=
  Matrix.vecMul (graphTail m y) (graphMinor m y)⁻¹

/-- The pivot value obtained from the row dependence relation. -/
def graphDependentPivot (y : DetCoeffVar m → ℝ) : ℝ :=
  graphRowCoeffs m y ⬝ᵥ graphFirstColumn m y

/-- The leading coefficient of the determinant in the distinguished pivot. -/
@[expose] def graphLeadingValue (y : DetCoeffVar m → ℝ) : ℝ :=
  MvPolynomial.eval y (detPivotLeading ℝ m)

/-- The constant coefficient of the determinant in the distinguished pivot. -/
@[expose] def graphRemainderValue (y : DetCoeffVar m → ℝ) : ℝ :=
  MvPolynomial.eval y (detPivotRemainder ℝ m)

/-- The pivot root of the affine determinant polynomial. -/
@[expose] def graphRoot (y : DetCoeffVar m → ℝ) : ℝ :=
  -graphRemainderValue m y / graphLeadingValue m y

/-- Insert the determinant root into the distinguished matrix entry. -/
@[expose] def graphMatrix (y : DetCoeffVar m → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => insertDistinguished (pivotZero m) (graphRoot m y) y (i, j)

lemma eval_genericDetPoly_insert_pivot
    (x : ℝ) (y : DetCoeffVar m → ℝ) :
    MvPolynomial.eval (insertDistinguished (pivotZero m) x y)
        (genericDetPoly ℝ (m + 1)) =
      graphLeadingValue m y * x + graphRemainderValue m y := by
  have h := toNested_map_eval (R := ℝ) (pivotZero m)
    (genericDetPoly ℝ (m + 1)) x y
  rw [genericDetPoly_pivot_nested] at h
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, graphLeadingValue,
    graphRemainderValue] using h.symm

lemma eval_genericDetPoly_graphRoot
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    MvPolynomial.eval (fun ij => (graphMatrix m y) ij.1 ij.2)
      (genericDetPoly ℝ (m + 1)) = 0 := by
  change MvPolynomial.eval
    (insertDistinguished (pivotZero m) (graphRoot m y) y)
      (genericDetPoly ℝ (m + 1)) = 0
  rw [eval_genericDetPoly_insert_pivot]
  rw [graphRoot]
  field_simp
  ring

lemma graphLeadingValue_eq_det (y : DetCoeffVar m → ℝ) :
    graphLeadingValue m y = (graphMinor m y).det := by
  rw [graphLeadingValue, detPivotLeading_eq_lowerDet, lowerDet,
    MvPolynomial.eval_rename, genericDetPoly,
    Matrix.eval_det_mvPolynomialX (Fin m) ℝ]
  rfl

/-- The positive invertible matrix `I + 𝟙𝟙ᵀ`. -/
@[expose] def positiveMinorBase : Matrix (Fin m) (Fin m) ℝ :=
  1 + Matrix.replicateCol (Fin 1) (fun _ : Fin m => (1 : ℝ)) *
    Matrix.replicateRow (Fin 1) (fun _ : Fin m => (1 : ℝ))

lemma positiveMinorBase_apply (i j : Fin m) :
    positiveMinorBase m i j = (if i = j then 1 else 0) + 1 := by
  simp [positiveMinorBase, Matrix.mul_apply, Matrix.one_apply]

lemma positiveMinorBase_pos (i j : Fin m) :
    0 < positiveMinorBase m i j := by
  rw [positiveMinorBase_apply]
  split_ifs <;> norm_num

lemma positiveMinorBase_det :
    (positiveMinorBase m).det = 1 + m := by
  change Matrix.det
      ((1 : Matrix (Fin m) (Fin m) ℝ) +
        Matrix.replicateCol (Fin 1) (fun _ : Fin m => (1 : ℝ)) *
          Matrix.replicateRow (Fin 1) (fun _ : Fin m => (1 : ℝ))) =
    1 + (m : ℝ)
  calc
    Matrix.det
        ((1 : Matrix (Fin m) (Fin m) ℝ) +
          Matrix.replicateCol (Fin 1) (fun _ : Fin m => (1 : ℝ)) *
            Matrix.replicateRow (Fin 1) (fun _ : Fin m => (1 : ℝ))) =
        1 + (fun _ : Fin m => (1 : ℝ)) ⬝ᵥ
          (fun _ : Fin m => (1 : ℝ)) :=
      Matrix.det_one_add_replicateCol_mul_replicateRow _ _
    _ = 1 + (m : ℝ) := by simp [dotProduct]

/-- A positive singular matrix whose top row is the sum of all other rows. -/
def positiveSingularBase :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j =>
    Fin.cases
      (Fin.cases (m : ℝ) (fun j' => ∑ k, positiveMinorBase m k j') j)
      (fun i' => Fin.cases 1 (fun j' => positiveMinorBase m i' j') j)
      i

/-- The explicit coefficient assignment used to obtain a positive chart neighborhood. -/
def graphBaseAssignment : DetCoeffVar m → ℝ :=
  fun q => positiveSingularBase m q.1.1 q.1.2

lemma graphMinor_base :
    graphMinor m (graphBaseAssignment m) = positiveMinorBase m := by
  ext i j
  simp [graphMinor, graphBaseAssignment, positiveSingularBase,
    lowerVarEmbedding]

lemma graphTail_base (j : Fin m) :
    graphTail m (graphBaseAssignment m) j =
      ∑ i, positiveMinorBase m i j := by
  simp [graphTail, graphBaseAssignment, positiveSingularBase, tailVar]

lemma graphFirstColumn_base (i : Fin m) :
    graphFirstColumn m (graphBaseAssignment m) i = 1 := by
  simp [graphFirstColumn, graphBaseAssignment, positiveSingularBase,
    firstColumnVar]

lemma graphLeadingValue_base :
    graphLeadingValue m (graphBaseAssignment m) = 1 + m := by
  rw [graphLeadingValue_eq_det, graphMinor_base, positiveMinorBase_det]

lemma graphLeadingValue_base_ne :
    graphLeadingValue m (graphBaseAssignment m) ≠ 0 := by
  rw [graphLeadingValue_base]
  positivity

lemma graphRowCoeffs_mul_minor
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    Matrix.vecMul (graphRowCoeffs m y) (graphMinor m y) =
      graphTail m y := by
  have hdet : (graphMinor m y).det ≠ 0 := by
    rwa [← graphLeadingValue_eq_det]
  have hunit : IsUnit (graphMinor m y).det := isUnit_iff_ne_zero.mpr hdet
  rw [graphRowCoeffs, Matrix.vecMul_vecMul,
    Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]

lemma graphRowCoeffs_base :
    graphRowCoeffs m (graphBaseAssignment m) = fun _ => 1 := by
  have hdet : (positiveMinorBase m).det ≠ 0 := by
    rw [positiveMinorBase_det]
    positivity
  have hunit : IsUnit (positiveMinorBase m).det := isUnit_iff_ne_zero.mpr hdet
  have htail : graphTail m (graphBaseAssignment m) =
      Matrix.vecMul (fun _ : Fin m => (1 : ℝ)) (positiveMinorBase m) := by
    ext j
    simp [graphTail_base, Matrix.vecMul, dotProduct]
  rw [graphRowCoeffs, graphMinor_base, htail, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one]

lemma graphDependentPivot_base :
    graphDependentPivot m (graphBaseAssignment m) = m := by
  rw [graphDependentPivot, graphRowCoeffs_base]
  simp [graphFirstColumn_base, dotProduct]

/-- The matrix obtained by imposing the distinguished row dependence. -/
def graphDependentMatrix (y : DetCoeffVar m → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => insertDistinguished (pivotZero m) (graphDependentPivot m y) y (i, j)

lemma graphDependentMatrix_row_relation
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    ∀ j, graphDependentMatrix m y 0 j =
      ∑ i : Fin m, graphRowCoeffs m y i *
        graphDependentMatrix m y i.succ j := by
  intro j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp [graphDependentMatrix, insertDistinguished, graphDependentPivot,
      graphFirstColumn, firstColumnVar, dotProduct]
  · have htail := congrFun (graphRowCoeffs_mul_minor m ha) j'
    simpa [graphDependentMatrix, insertDistinguished, graphTail, tailVar,
      graphMinor, lowerVarEmbedding, Matrix.vecMul, dotProduct] using htail.symm

lemma graphDependentMatrix_det_zero
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    (graphDependentMatrix m y).det = 0 := by
  let c : Fin (m + 1) → ℝ := Fin.cases 0 (graphRowCoeffs m y)
  have hrow : ∀ j, graphDependentMatrix m y 0 j =
      ∑ i, c i * graphDependentMatrix m y i j := by
    intro j
    rw [Fin.sum_univ_succ]
    simp [c, graphDependentMatrix_row_relation m ha]
  have hup : (graphDependentMatrix m y).updateRow 0
      (∑ i, c i • graphDependentMatrix m y i) =
      graphDependentMatrix m y := by
    ext i j
    by_cases hi : i = 0
    · subst i
      simpa only [Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] using (hrow j).symm
    · simp [hi]
  calc
    (graphDependentMatrix m y).det =
        ((graphDependentMatrix m y).updateRow 0
          (∑ i, c i • graphDependentMatrix m y i)).det :=
      congrArg Matrix.det hup.symm
    _ = c 0 • (graphDependentMatrix m y).det :=
      Matrix.det_updateRow_sum _ _ _
    _ = 0 := by simp [c]

lemma graphRoot_eq_dependentPivot
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    graphRoot m y = graphDependentPivot m y := by
  have heval := eval_genericDetPoly_insert_pivot m
    (graphDependentPivot m y) y
  have hzero : MvPolynomial.eval
      (insertDistinguished (pivotZero m) (graphDependentPivot m y) y)
        (genericDetPoly ℝ (m + 1)) = 0 := by
    rw [genericDetPoly, Matrix.eval_det_mvPolynomialX (Fin (m + 1)) ℝ]
    exact graphDependentMatrix_det_zero m ha
  rw [hzero] at heval
  rw [graphRoot]
  field_simp
  nlinarith

lemma graphMatrix_row_relation
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    ∀ j, graphMatrix m y 0 j =
      ∑ i : Fin m, graphRowCoeffs m y i * graphMatrix m y i.succ j := by
  change ∀ j,
    insertDistinguished (pivotZero m) (graphRoot m y) y (0, j) =
      ∑ i : Fin m, graphRowCoeffs m y i *
        insertDistinguished (pivotZero m) (graphRoot m y) y (i.succ, j)
  rw [graphRoot_eq_dependentPivot m ha]
  exact graphDependentMatrix_row_relation m ha

lemma graphRoot_base :
    graphRoot m (graphBaseAssignment m) = m := by
  rw [graphRoot_eq_dependentPivot m (graphLeadingValue_base_ne m),
    graphDependentPivot_base]

lemma graphMatrix_base :
    graphMatrix m (graphBaseAssignment m) = positiveSingularBase m := by
  ext i j
  by_cases h : (i, j) = pivotZero m
  · have hi := congrArg Prod.fst h
    have hj := congrArg Prod.snd h
    change i = 0 at hi
    change j = 0 at hj
    subst i
    subst j
    simp [graphMatrix, insertDistinguished, graphRoot_base,
      positiveSingularBase]
  · simp [graphMatrix, insertDistinguished, h, graphBaseAssignment]

lemma positiveSingularBase_pos (hm : 0 < m)
    (i j : Fin (m + 1)) : 0 < positiveSingularBase m i j := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [positiveSingularBase] using hm
    · simp only [positiveSingularBase, Fin.cases_zero, Fin.cases_succ]
      let k0 : Fin m := ⟨0, hm⟩
      exact Finset.sum_pos' (fun k _ => (positiveMinorBase_pos m k j').le)
        ⟨k0, Finset.mem_univ _, positiveMinorBase_pos m k0 j'⟩
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp [positiveSingularBase]
    · simpa [positiveSingularBase] using positiveMinorBase_pos m i' j'

lemma graphMatrix_base_pos (hm : 0 < m)
    (i j : Fin (m + 1)) :
    0 < graphMatrix m (graphBaseAssignment m) i j := by
  rw [graphMatrix_base]
  exact positiveSingularBase_pos m hm i j

lemma graphRowCoeffs_base_pos (i : Fin m) :
    0 < graphRowCoeffs m (graphBaseAssignment m) i := by
  rw [graphRowCoeffs_base]
  norm_num

lemma continuous_graphLeadingValue : Continuous (graphLeadingValue m) :=
  MvPolynomial.continuous_eval _

lemma continuous_graphRemainderValue : Continuous (graphRemainderValue m) :=
  MvPolynomial.continuous_eval _

lemma continuousAt_graphRoot_base :
    ContinuousAt (graphRoot m) (graphBaseAssignment m) := by
  exact continuous_graphRemainderValue m |>.continuousAt.neg.div
    (continuous_graphLeadingValue m).continuousAt (graphLeadingValue_base_ne m)

lemma continuous_graphMinor : Continuous (graphMinor m) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_apply (lowerVarEmbedding m (i, j))

lemma continuous_graphTail : Continuous (graphTail m) := by
  apply continuous_pi
  intro j
  exact continuous_apply (tailVar m j)

lemma continuousAt_graphMinor_inv_base :
    ContinuousAt (fun y => (graphMinor m y)⁻¹) (graphBaseAssignment m) := by
  have hdet : (graphMinor m (graphBaseAssignment m)).det ≠ 0 := by
    rw [graphMinor_base, positiveMinorBase_det]
    positivity
  have hinverse : ContinuousAt Ring.inverse
      (graphMinor m (graphBaseAssignment m)).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  exact (continuousAt_matrix_inv _ hinverse).comp
    (continuous_graphMinor m).continuousAt

lemma continuousAt_graphRowCoeffs_base :
    ContinuousAt (graphRowCoeffs m) (graphBaseAssignment m) := by
  rw [continuousAt_pi]
  intro i
  change ContinuousAt
    (fun y => ∑ j, graphTail m y j * (graphMinor m y)⁻¹ j i)
    (graphBaseAssignment m)
  apply tendsto_finsetSum Finset.univ
  intro j hj
  exact ((continuous_apply j).comp (continuous_graphTail m)).continuousAt.mul
    ((continuous_apply i).continuousAt.comp
      ((continuous_apply j).continuousAt.comp
        (continuousAt_graphMinor_inv_base m)))

lemma continuousAt_graphMatrix_entry_base (i j : Fin (m + 1)) :
    ContinuousAt (fun y => graphMatrix m y i j) (graphBaseAssignment m) := by
  by_cases h : (i, j) = pivotZero m
  · simpa [graphMatrix, insertDistinguished, h] using
      continuousAt_graphRoot_base m
  · simpa [graphMatrix, insertDistinguished, h] using
      (continuous_apply (⟨(i, j), h⟩ : DetCoeffVar m)).continuousAt

/-- Near the explicit base point, the determinant graph is positive and its
row-dependence coefficients are positive. -/
theorem eventually_positive_determinant_graph (hm : 0 < m) :
    ∀ᶠ y in 𝓝 (graphBaseAssignment m),
      graphLeadingValue m y ≠ 0 ∧
        (∀ i j, 0 < graphMatrix m y i j) ∧
        (∀ i, 0 < graphRowCoeffs m y i) := by
  have ha : ∀ᶠ y in 𝓝 (graphBaseAssignment m),
      graphLeadingValue m y ≠ 0 :=
    (continuous_graphLeadingValue m).continuousAt.eventually_ne
      (graphLeadingValue_base_ne m)
  have hmatrix : ∀ᶠ y in 𝓝 (graphBaseAssignment m),
      ∀ i j, 0 < graphMatrix m y i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact continuousAt_const.eventually_lt
      (continuousAt_graphMatrix_entry_base m i j)
      (graphMatrix_base_pos m hm i j)
  have hcoeff : ∀ᶠ y in 𝓝 (graphBaseAssignment m),
      ∀ i, 0 < graphRowCoeffs m y i := by
    rw [Filter.eventually_all]
    intro i
    exact continuousAt_const.eventually_lt
      ((continuous_apply i).continuousAt.comp
        (continuousAt_graphRowCoeffs_base m))
      (graphRowCoeffs_base_pos m i)
  filter_upwards [ha, hmatrix, hcoeff] with y hay hmy hcy
  exact ⟨hay, hmy, hcy⟩

/-- A literal product of open intervals contained in the positive singular
graph chart. -/
theorem exists_positive_determinant_graph_box (hm : 0 < m) :
    ∃ l u : DetCoeffVar m → ℝ,
      (∀ q, l q < u q) ∧
      ∀ y : DetCoeffVar m → ℝ,
        (∀ q, y q ∈ Set.Ioo (l q) (u q)) →
        graphLeadingValue m y ≠ 0 ∧
          (∀ i j, 0 < graphMatrix m y i j) ∧
          (∀ i, 0 < graphRowCoeffs m y i) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_positive_determinant_graph m hm)
  refine ⟨fun q => graphBaseAssignment m q - ε,
    fun q => graphBaseAssignment m q + ε, fun q => by linarith, ?_⟩
  intro y hy
  apply hball
  rw [ball_pi _ hε]
  intro q hq
  simpa [Real.ball_eq_Ioo] using hy q

lemma graphRoot_unique
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0)
    (x : ℝ) :
    MvPolynomial.eval (insertDistinguished (pivotZero m) x y)
        (genericDetPoly ℝ (m + 1)) = 0 ↔
      x = graphRoot m y := by
  rw [eval_genericDetPoly_insert_pivot]
  constructor
  · intro hx
    rw [graphRoot]
    field_simp
    nlinarith
  · rintro rfl
    rw [graphRoot]
    field_simp
    ring

lemma graphMatrix_det_zero
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    (graphMatrix m y).det = 0 := by
  have heq : graphMatrix m y = graphDependentMatrix m y := by
    ext i j
    simp only [graphMatrix, graphDependentMatrix]
    rw [graphRoot_eq_dependentPivot m ha]
  rw [heq]
  exact graphDependentMatrix_det_zero m ha

/-- The total mass of the determinant-root chart matrix. -/
@[expose] def graphMass (y : DetCoeffVar m → ℝ) : ℝ :=
  GeneralAsymmetricC1.mass (graphMatrix m y)

/-- Normalize the positive determinant-root chart matrix to total mass one. -/
@[expose] def normalizedGraphMatrix (y : DetCoeffVar m → ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => (graphMass m y)⁻¹ * graphMatrix m y i j

lemma graphMass_pos {y : DetCoeffVar m → ℝ}
    (hpos : ∀ i j, 0 < graphMatrix m y i j) :
    0 < graphMass m y := by
  let i0 : Fin (m + 1) := 0
  let j0 : Fin (m + 1) := 0
  have hinner : ∀ i, 0 < ∑ j, graphMatrix m y i j := by
    intro i
    exact Finset.sum_pos' (fun j _ => (hpos i j).le)
      ⟨j0, Finset.mem_univ _, hpos i j0⟩
  exact Finset.sum_pos' (fun i _ => (hinner i).le)
    ⟨i0, Finset.mem_univ _, hinner i0⟩

lemma normalizedGraphMatrix_pos
    {y : DetCoeffVar m → ℝ} (hpos : ∀ i j, 0 < graphMatrix m y i j)
    (i j : Fin (m + 1)) :
    0 < normalizedGraphMatrix m y i j := by
  have hmass := graphMass_pos m hpos
  exact mul_pos (inv_pos.mpr hmass) (hpos i j)

lemma normalizedGraphMatrix_mass_one
    {y : DetCoeffVar m → ℝ} (hpos : ∀ i j, 0 < graphMatrix m y i j) :
    GeneralAsymmetricC1.mass (normalizedGraphMatrix m y) = 1 := by
  have hmass := graphMass_pos m hpos
  unfold GeneralAsymmetricC1.mass normalizedGraphMatrix graphMass
  simp_rw [← Finset.mul_sum]
  exact inv_mul_cancel₀ hmass.ne'

lemma normalizedGraphMatrix_det_zero
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    (normalizedGraphMatrix m y).det = 0 := by
  have heq : normalizedGraphMatrix m y =
      (graphMass m y)⁻¹ • graphMatrix m y := by
    ext i j
    simp [normalizedGraphMatrix]
  rw [heq, Matrix.det_smul, graphMatrix_det_zero m ha, mul_zero]

lemma normalizedGraphMatrix_minor_det_ne_zero
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0)
    (hpos : ∀ i j, 0 < graphMatrix m y i j) :
    ((normalizedGraphMatrix m y).submatrix Fin.succ Fin.succ).det ≠ 0 := by
  have hmass : graphMass m y ≠ 0 := (graphMass_pos m hpos).ne'
  have hminor : (graphMinor m y).det ≠ 0 := by
    rwa [← graphLeadingValue_eq_det]
  have heq : (normalizedGraphMatrix m y).submatrix Fin.succ Fin.succ =
      (graphMass m y)⁻¹ • graphMinor m y := by
    ext i j
    simp [normalizedGraphMatrix, graphMinor, graphMatrix,
      insertDistinguished, lowerVarEmbedding]
  rw [heq, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hmass)) hminor

lemma normalizedGraphMatrix_successor_rows_linearIndependent
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0)
    (hpos : ∀ i j, 0 < graphMatrix m y i j) :
    LinearIndependent ℝ (fun i : Fin m => normalizedGraphMatrix m y i.succ) := by
  let restrictSucc :
      (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun v j => v j.succ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hminor := Matrix.linearIndependent_rows_of_det_ne_zero
    (normalizedGraphMatrix_minor_det_ne_zero m ha hpos)
  have hcomp : restrictSucc ∘
      (fun i : Fin m => normalizedGraphMatrix m y i.succ) =
      fun i => ((normalizedGraphMatrix m y).submatrix Fin.succ Fin.succ) i := by
    funext i j
    rfl
  apply LinearIndependent.of_comp restrictSucc
  rw [hcomp]
  exact hminor

lemma normalizedGraphMatrix_row_relation
    {y : DetCoeffVar m → ℝ} (ha : graphLeadingValue m y ≠ 0) :
    ∀ j, normalizedGraphMatrix m y 0 j =
      ∑ i : Fin m, graphRowCoeffs m y i *
        normalizedGraphMatrix m y i.succ j := by
  intro j
  have hrow := graphMatrix_row_relation m ha j
  change (graphMass m y)⁻¹ * graphMatrix m y 0 j =
    ∑ i : Fin m, graphRowCoeffs m y i *
      ((graphMass m y)⁻¹ * graphMatrix m y i.succ j)
  rw [hrow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Main positive-row-cone chart.  The parameter set is a Cartesian product
of nonempty real open intervals, and the normalized graph matrices have mass
one. -/
theorem exists_positive_row_cone_open_box (hm : 0 < m) :
    ∃ l u : DetCoeffVar m → ℝ,
      (∀ q, l q < u q) ∧
      ∀ y : DetCoeffVar m → ℝ,
        (∀ q, y q ∈ Set.Ioo (l q) (u q)) →
        (∀ i j, 0 < normalizedGraphMatrix m y i j) ∧
        GeneralAsymmetricC1.mass (normalizedGraphMatrix m y) = 1 ∧
        graphLeadingValue m y ≠ 0 ∧
        (∀ x : ℝ,
          MvPolynomial.eval (insertDistinguished (pivotZero m) x y)
              (genericDetPoly ℝ (m + 1)) = 0 ↔
            x = graphRoot m y) ∧
        (normalizedGraphMatrix m y).det = 0 ∧
        ((normalizedGraphMatrix m y).submatrix Fin.succ Fin.succ).det ≠ 0 ∧
        LinearIndependent ℝ
          (fun i : Fin m => normalizedGraphMatrix m y i.succ) ∧
        (∀ i, 0 < graphRowCoeffs m y i) ∧
        (∀ j, normalizedGraphMatrix m y 0 j =
          ∑ i : Fin m, graphRowCoeffs m y i *
            normalizedGraphMatrix m y i.succ j) := by
  obtain ⟨l, u, hlu, hbox⟩ := exists_positive_determinant_graph_box m hm
  refine ⟨l, u, hlu, ?_⟩
  intro y hy
  obtain ⟨ha, hpos, hcoeff⟩ := hbox y hy
  exact ⟨normalizedGraphMatrix_pos m hpos,
    normalizedGraphMatrix_mass_one m hpos, ha,
    graphRoot_unique m ha, normalizedGraphMatrix_det_zero m ha,
    normalizedGraphMatrix_minor_det_ne_zero m ha hpos,
    normalizedGraphMatrix_successor_rows_linearIndependent m ha hpos,
    hcoeff, normalizedGraphMatrix_row_relation m ha⟩

end GraphCoordinates

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
