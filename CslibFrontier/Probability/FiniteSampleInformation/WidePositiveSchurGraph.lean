/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.WideTauHomConeContact
public import CslibFrontier.Probability.FiniteSampleInformation.MaximalMinorSchurChart

/-!
# A positive Schur graph on a literal open box

The base variables are the entries of `A`, `B`, and `c` in

```
U = [ A  B ]
    [ c  d ].
```

On the fixed chart `det A ≠ 0`, put `λ = c A⁻¹` and `d = λ B`.  The
resulting matrix is positive near an explicit point and its last row is a
positive linear combination of its first rows.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`WidePositiveSchurGraph.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace WidePolynomial

variable {k r : ℕ}

open GeneralAsymmetricC1

/-- Variables in the fixed Schur base: `A`, then `B`, then `c`. -/
abbrev SchurBaseVar (k r : ℕ) :=
  (Fin k × Fin k) ⊕ ((Fin k × Fin r) ⊕ Fin k)

/-- The top-left pivot block of a rectangular Schur chart. -/
@[expose] def schurA {k r : ℕ} (y : SchurBaseVar k r → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => y (Sum.inl (i, j))

/-- The top-right block of a rectangular Schur chart. -/
@[expose] def schurB {k r : ℕ} (y : SchurBaseVar k r → ℝ) :
    Matrix (Fin k) (Fin r) ℝ :=
  fun i β => y (Sum.inr (Sum.inl (i, β)))

/-- The bottom-left row of a rectangular Schur chart. -/
@[expose] def schurC {k r : ℕ} (y : SchurBaseVar k r → ℝ) : Fin k → ℝ :=
  fun i => y (Sum.inr (Sum.inr i))

/-- The determinant of the pivot block of a rectangular Schur chart. -/
@[expose] def schurDelta {k r : ℕ} (y : SchurBaseVar k r → ℝ) : ℝ :=
  Matrix.det (schurA y)

/-- The coefficients expressing the bottom-left row in the pivot-row basis. -/
@[expose] def schurLambda {k r : ℕ} (y : SchurBaseVar k r → ℝ) : Fin k → ℝ :=
  Matrix.vecMul (schurC y) (schurA y)⁻¹

/-- The bottom-right entries imposed by the Schur-complement equations. -/
@[expose] def schurRho {k r : ℕ} (y : SchurBaseVar k r → ℝ) : Fin r → ℝ :=
  Matrix.vecMul (schurLambda y) (schurB y)

/-- The rank-deficient Schur graph `d = c A⁻¹ B`. -/
@[expose] def positiveSchurGraph {k r : ℕ} (y : SchurBaseVar k r → ℝ) :
    Mat (k + 1) (k + r) :=
  fun i a =>
    match finSumFinEquiv.symm i, finSumFinEquiv.symm a with
    | Sum.inl i', Sum.inl j => schurA y i' j
    | Sum.inl i', Sum.inr β => schurB y i' β
    | Sum.inr _, Sum.inl j => schurC y j
    | Sum.inr _, Sum.inr β => schurRho y β

@[simp]
lemma positiveSchurGraph_pivot (y : SchurBaseVar k r → ℝ)
    (i j : Fin k) :
    positiveSchurGraph y i.castSucc (Fin.castAdd r j) = schurA y i j := by
  simp [positiveSchurGraph]

@[simp]
lemma positiveSchurGraph_top_free (y : SchurBaseVar k r → ℝ)
    (i : Fin k) (β : Fin r) :
    positiveSchurGraph y i.castSucc (Fin.natAdd k β) = schurB y i β := by
  simp [positiveSchurGraph]

@[simp]
lemma positiveSchurGraph_bottom_pivot (y : SchurBaseVar k r → ℝ)
    (j : Fin k) :
    positiveSchurGraph y (Fin.last k) (Fin.castAdd r j) = schurC y j := by
  simp [positiveSchurGraph]

@[simp]
lemma positiveSchurGraph_bottom_free (y : SchurBaseVar k r → ℝ)
    (β : Fin r) :
    positiveSchurGraph y (Fin.last k) (Fin.natAdd k β) = schurRho y β := by
  simp [positiveSchurGraph]

lemma pivotBlock_positiveSchurGraph (y : SchurBaseVar k r → ℝ) :
    pivotBlock (positiveSchurGraph y) = schurA y := by
  ext i j
  simp [pivotBlock, pivotRow, pivotColumn]

lemma schurLambda_mul_A {y : SchurBaseVar k r → ℝ}
    (hδ : schurDelta y ≠ 0) :
    Matrix.vecMul (schurLambda y) (schurA y) = schurC y := by
  have hunit : IsUnit (schurA y).det := isUnit_iff_ne_zero.mpr hδ
  rw [schurLambda, Matrix.vecMul_vecMul,
    Matrix.nonsing_inv_mul _ hunit, Matrix.vecMul_one]

lemma positiveSchurGraph_row_relation {y : SchurBaseVar k r → ℝ}
    (hδ : schurDelta y ≠ 0) :
    ∀ a, positiveSchurGraph y (Fin.last k) a =
      ∑ i : Fin k, schurLambda y i * positiveSchurGraph y i.castSucc a := by
  intro a
  rw [← finSumFinEquiv.apply_symm_apply a]
  cases finSumFinEquiv.symm a with
  | inl j =>
      have h := congrFun (schurLambda_mul_A hδ) j
      simpa [Matrix.vecMul, dotProduct] using h.symm
  | inr β =>
      simp [schurRho, Matrix.vecMul, dotProduct]

lemma eval_schurMinor_positiveSchurGraph
    {y : SchurBaseVar k r → ℝ} (hδ : schurDelta y ≠ 0) (β : Fin r) :
    MvPolynomial.eval
      (fun ia => positiveSchurGraph y ia.1 ia.2) (schurMinor k r β) = 0 := by
  rw [eval_schurMinor]
  let c : Fin (k + 1) → ℝ := Fin.snoc (schurLambda y) 0
  have hrow : ∀ j, schurBorderedMatrix (positiveSchurGraph y) β (Fin.last k) j =
      ∑ i, c i * schurBorderedMatrix (positiveSchurGraph y) β i j := by
    intro j
    rw [Fin.sum_univ_castSucc]
    simp only [c, Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero,
      schurBorderedMatrix]
    exact positiveSchurGraph_row_relation hδ (schurColumn k r β j)
  have hup : (schurBorderedMatrix (positiveSchurGraph y) β).updateRow
      (Fin.last k) (∑ i, c i • schurBorderedMatrix (positiveSchurGraph y) β i) =
      schurBorderedMatrix (positiveSchurGraph y) β := by
    ext i j
    by_cases hi : i = Fin.last k
    · subst i
      simpa only [Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] using (hrow j).symm
    · simp [Matrix.updateRow_ne hi]
  calc
    Matrix.det (schurBorderedMatrix (positiveSchurGraph y) β) =
        Matrix.det ((schurBorderedMatrix (positiveSchurGraph y) β).updateRow
          (Fin.last k) (∑ i, c i •
            schurBorderedMatrix (positiveSchurGraph y) β i)) :=
      congrArg Matrix.det hup.symm
    _ = c (Fin.last k) •
        Matrix.det (schurBorderedMatrix (positiveSchurGraph y) β) :=
      Matrix.det_updateRow_sum _ _ _
    _ = 0 := by simp [c]

/-! ## Explicit positive base point -/

/-- An explicit positive base point of the rectangular Schur chart. -/
def schurGraphBase (k r : ℕ) : SchurBaseVar k r → ℝ
  | Sum.inl (i, j) => SquarePolynomial.positiveMinorBase k i j
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr j) =>
      ∑ i : Fin k, SquarePolynomial.positiveMinorBase k i j

@[simp]
lemma schurA_base : schurA (schurGraphBase k r) =
    SquarePolynomial.positiveMinorBase k := by
  ext i j
  rfl

@[simp]
lemma schurB_base : schurB (schurGraphBase k r) =
    (fun _ _ => 1 : Matrix (Fin k) (Fin r) ℝ) := by
  rfl

@[simp]
lemma schurC_base (j : Fin k) :
    schurC (schurGraphBase k r) j =
      ∑ i : Fin k, SquarePolynomial.positiveMinorBase k i j := by
  rfl

lemma schurDelta_base : schurDelta (schurGraphBase k r) = 1 + k := by
  rw [schurDelta, schurA_base, SquarePolynomial.positiveMinorBase_det]

lemma schurDelta_base_ne : schurDelta (schurGraphBase k r) ≠ 0 := by
  rw [schurDelta_base]
  positivity

lemma schurLambda_base : schurLambda (schurGraphBase k r) = fun _ => 1 := by
  have hdet : (SquarePolynomial.positiveMinorBase k).det ≠ 0 := by
    rw [SquarePolynomial.positiveMinorBase_det]
    positivity
  have hunit : IsUnit (SquarePolynomial.positiveMinorBase k).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hc : schurC (schurGraphBase k r) =
      Matrix.vecMul (fun _ : Fin k => (1 : ℝ))
        (SquarePolynomial.positiveMinorBase k) := by
    ext j
    simp [schurC_base, Matrix.vecMul, dotProduct]
  rw [schurLambda, schurA_base, hc, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one]

lemma schurRho_base (β : Fin r) :
    schurRho (schurGraphBase k r) β = k := by
  simp [schurRho, schurLambda_base, schurB_base, Matrix.vecMul, dotProduct]

lemma positiveSchurGraph_base_pos (hk : 0 < k)
    (i : Fin (k + 1)) (a : Fin (k + r)) :
    0 < positiveSchurGraph (schurGraphBase k r) i a := by
  rw [← finSumFinEquiv.apply_symm_apply i,
    ← finSumFinEquiv.apply_symm_apply a]
  cases finSumFinEquiv.symm i with
  | inl i =>
      cases finSumFinEquiv.symm a with
      | inl j =>
          simpa [positiveSchurGraph, schurA_base] using
            SquarePolynomial.positiveMinorBase_pos k i j
      | inr β => simp [positiveSchurGraph, schurB_base]
  | inr i =>
      fin_cases i
      cases finSumFinEquiv.symm a with
      | inl j =>
          simp only [positiveSchurGraph, schurC_base]
          simp only [Equiv.symm_apply_apply]
          let i0 : Fin k := ⟨0, hk⟩
          exact Finset.sum_pos' (fun q _ =>
              (SquarePolynomial.positiveMinorBase_pos k q j).le)
            ⟨i0, Finset.mem_univ _,
              SquarePolynomial.positiveMinorBase_pos k i0 j⟩
      | inr β =>
          simp [positiveSchurGraph, schurRho_base, hk]

lemma schurLambda_base_pos (i : Fin k) :
    0 < schurLambda (schurGraphBase k r) i := by
  rw [schurLambda_base]
  norm_num

/-! ## Continuity and the open box -/

lemma continuous_schurA (k r : ℕ) : Continuous (schurA (k := k) (r := r)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_apply (Sum.inl (i, j))

lemma continuous_schurB (k r : ℕ) : Continuous (schurB (k := k) (r := r)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro β
  exact continuous_apply (Sum.inr (Sum.inl (i, β)))

lemma continuous_schurC (k r : ℕ) : Continuous (schurC (k := k) (r := r)) := by
  apply continuous_pi
  intro i
  exact continuous_apply (Sum.inr (Sum.inr i))

lemma continuous_schurDelta (k r : ℕ) :
    Continuous (schurDelta (k := k) (r := r)) := by
  change Continuous (fun y => Matrix.det (schurA y))
  exact (continuous_schurA k r).matrix_det

lemma continuousAt_schurA_inv_base (k r : ℕ) :
    ContinuousAt (fun y : SchurBaseVar k r → ℝ => (schurA y)⁻¹)
      (schurGraphBase k r) := by
  have hdet : (schurA (schurGraphBase k r)).det ≠ 0 := by
    change schurDelta (schurGraphBase k r) ≠ 0
    exact schurDelta_base_ne
  have hinverse : ContinuousAt Ring.inverse
      (schurA (schurGraphBase k r)).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  exact (continuousAt_matrix_inv _ hinverse).comp
    (continuous_schurA k r).continuousAt

lemma continuousAt_schurLambda_base (k r : ℕ) :
    ContinuousAt (schurLambda (k := k) (r := r)) (schurGraphBase k r) := by
  rw [continuousAt_pi]
  intro i
  change ContinuousAt
    (fun y => ∑ j, schurC y j * (schurA y)⁻¹ j i) (schurGraphBase k r)
  apply tendsto_finsetSum Finset.univ
  intro j hj
  exact ((continuous_apply j).comp (continuous_schurC k r)).continuousAt.mul
    ((continuous_apply i).continuousAt.comp
      ((continuous_apply j).continuousAt.comp
        (continuousAt_schurA_inv_base k r)))

lemma continuousAt_schurRho_base (k r : ℕ) :
    ContinuousAt (schurRho (k := k) (r := r)) (schurGraphBase k r) := by
  rw [continuousAt_pi]
  intro β
  change ContinuousAt
    (fun y => ∑ i, schurLambda y i * schurB y i β) (schurGraphBase k r)
  apply tendsto_finsetSum Finset.univ
  intro i hi
  exact ((continuous_apply i).continuousAt.comp
      (continuousAt_schurLambda_base k r)).mul
    ((continuous_apply β).comp
      ((continuous_apply i).comp (continuous_schurB k r))).continuousAt

lemma continuousAt_positiveSchurGraph_entry_base (k r : ℕ)
    (i : Fin (k + 1)) (a : Fin (k + r)) :
    ContinuousAt (fun y => positiveSchurGraph y i a) (schurGraphBase k r) := by
  rw [← finSumFinEquiv.apply_symm_apply i,
    ← finSumFinEquiv.apply_symm_apply a]
  cases finSumFinEquiv.symm i with
  | inl i =>
      cases finSumFinEquiv.symm a with
      | inl j =>
          simpa [positiveSchurGraph, schurA] using
            (continuous_apply (Sum.inl (i, j)) :
              Continuous (fun y : SchurBaseVar k r → ℝ => y (Sum.inl (i, j)))).continuousAt
      | inr β =>
          simpa [positiveSchurGraph, schurB] using
            (continuous_apply (Sum.inr (Sum.inl (i, β))) :
              Continuous (fun y : SchurBaseVar k r → ℝ =>
                y (Sum.inr (Sum.inl (i, β))))).continuousAt
  | inr q =>
      fin_cases q
      cases finSumFinEquiv.symm a with
      | inl j =>
          simpa [positiveSchurGraph, schurC] using
            (continuous_apply (Sum.inr (Sum.inr j)) :
              Continuous (fun y : SchurBaseVar k r → ℝ =>
                y (Sum.inr (Sum.inr j)))).continuousAt
      | inr β =>
          simp only [positiveSchurGraph, Equiv.symm_apply_apply]
          exact (continuous_apply β).continuousAt.comp
            (continuousAt_schurRho_base k r)

theorem eventually_positive_schur_graph (hk : 0 < k) :
    ∀ᶠ y in nhds (schurGraphBase k r),
      schurDelta y ≠ 0 ∧
        (∀ i a, 0 < positiveSchurGraph y i a) ∧
        (∀ i, 0 < schurLambda y i) := by
  have hδ : ∀ᶠ y in nhds (schurGraphBase k r), schurDelta y ≠ 0 :=
    (continuous_schurDelta k r).continuousAt.eventually_ne schurDelta_base_ne
  have hmatrix : ∀ᶠ y in nhds (schurGraphBase k r),
      ∀ i a, 0 < positiveSchurGraph y i a := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro a
    exact continuousAt_const.eventually_lt
      (continuousAt_positiveSchurGraph_entry_base k r i a)
      (positiveSchurGraph_base_pos hk i a)
  have hlambda : ∀ᶠ y in nhds (schurGraphBase k r),
      ∀ i, 0 < schurLambda y i := by
    rw [Filter.eventually_all]
    intro i
    exact continuousAt_const.eventually_lt
      ((continuous_apply i).continuousAt.comp
        (continuousAt_schurLambda_base k r))
      (schurLambda_base_pos i)
  filter_upwards [hδ, hmatrix, hlambda] with y hδy hUy hlambday
  exact ⟨hδy, hUy, hlambday⟩

/-- A literal Cartesian product of nonempty intervals contained in the
positive Schur graph chart. -/
theorem exists_positive_schur_graph_open_box (hk : 0 < k) :
    ∃ l u : SchurBaseVar k r → ℝ,
      (∀ q, l q < u q) ∧
      ∀ y : SchurBaseVar k r → ℝ,
        (∀ q, y q ∈ Set.Ioo (l q) (u q)) →
        schurDelta y ≠ 0 ∧
          (∀ i a, 0 < positiveSchurGraph y i a) ∧
          (∀ i, 0 < schurLambda y i) ∧
          (∀ a, positiveSchurGraph y (Fin.last k) a =
            ∑ i : Fin k, schurLambda y i *
              positiveSchurGraph y i.castSucc a) ∧
          (∀ β, MvPolynomial.eval
            (fun ia => positiveSchurGraph y ia.1 ia.2) (schurMinor k r β) = 0) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_positive_schur_graph (k := k) (r := r) hk)
  refine ⟨fun q => schurGraphBase k r q - ε,
    fun q => schurGraphBase k r q + ε, fun q => by linarith, ?_⟩
  intro y hy
  obtain ⟨hδ, hpos, hlambda⟩ := hball (by
    rw [ball_pi _ hε]
    intro q hq
    simpa [Real.ball_eq_Ioo] using hy q)
  exact ⟨hδ, hpos, hlambda, positiveSchurGraph_row_relation hδ,
    eval_schurMinor_positiveSchurGraph hδ⟩


end WidePolynomial

end

end Cslib.FiniteSampleInformation
