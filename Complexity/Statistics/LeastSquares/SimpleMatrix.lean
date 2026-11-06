/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FractionalGeometry
public import Complexity.Statistics.LeastSquares.Stability
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Simple regression in the generic inverse-matrix model

The scalar sign audit of [XuGaoHu2027], Section 5, is the two-column
inverse-matrix audit of Sections 2–3. The regressor is column zero and the
intercept is column one. Positive mass and regressor scatter are derived from
positive definiteness, and conversely. Distinct regressor values imply the
actual design-row general-position condition. Consequently the generic
attainment, sparsification and rounding theorems apply to scalar feasibility.
-/

public section

namespace Cslib.LeastSquares.Simple

open Matrix Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The actual two-column design, in slope/intercept order. -/
@[expose] def design (x : ι → ℝ) (i : ι) : Fin 2 → ℝ := ![x i, 1]

/-- The linear functional selecting the slope. -/
@[expose] def slopeTarget : Fin 2 → ℝ := ![1, 0]

/-- The Gram determinant is exactly the scalar regressor numerator. -/
theorem det_gram (x w : ι → ℝ) :
    (weightedGram 0 Finset.univ (design x) w).det = xNumerator x w := by
  simp only [Matrix.det_fin_two, weightedGram, zero_add, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, vecMulVec, Matrix.of_apply, design, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, one_mul, xNumerator, crossNumerator, mass, ← mul_assoc]
  rw [mul_comm (∑ i, w i * x i * x i)]

/-- Nonnegative weights give a positive semidefinite actual design. -/
theorem gram_posSemidef (x w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (weightedGram 0 Finset.univ (design x) w).PosSemidef := by
  simp only [weightedGram, zero_add]
  apply posSemidef_sum
  intro i _
  have hp : (vecMulVec (design x i) (design x i)).PosSemidef := by
    simpa using posSemidef_vecMulVec_self_star (design x i)
  exact hp.smul (hw i)

/-- Scalar nonsingularity agrees with the matrix condition. In particular,
positive mass is forced by the intercept column, not supplied by convention. -/
theorem gram_posDef_iff (x w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (weightedGram 0 Finset.univ (design x) w).PosDef ↔
      0 < mass w ∧ 0 < xNumerator x w := by
  constructor
  · intro h
    refine ⟨?_, by simpa only [det_gram] using h.det_pos⟩
    have hd : 0 < weightedGram 0 Finset.univ (design x) w 1 1 := h.diag_pos
    simpa [weightedGram, Matrix.sum_apply, vecMulVec, design, mass] using hd
  · rintro ⟨_, hv⟩
    exact (gram_posSemidef x w hw).posDef_iff_det_ne_zero.mpr
      (by rw [det_gram]; exact ne_of_gt hv)

/-- Both scalar normal equations are the actual matrix normal equation. -/
theorem normal_matrix (x y w : ι → ℝ) (hm : mass w ≠ 0)
    (hv : xNumerator x w ≠ 0) :
    weightedGram 0 Finset.univ (design x) w *ᵥ
      ![slope x y w, intercept x y w] =
        weightedResponse 0 Finset.univ (design x) y w := by
  obtain ⟨h₁, h₂⟩ := normal_equations x y w hm hv
  ext j
  fin_cases j <;>
    simp [weightedGram, weightedResponse, Matrix.sum_apply, mulVec, dotProduct,
      Fin.sum_univ_two, vecMulVec, design, mass, mul_comm,
      mul_left_comm] at * <;> nlinarith

/-- The scalar estimator equals the actual inverse, including its intercept. -/
theorem inverse_estimate (x y w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : 0 < mass w) (hv : 0 < xNumerator x w) :
    weightedEstimate 0 0 Finset.univ (design x) y w =
      ![slope x y w, intercept x y w] := by
  have hG := (gram_posDef_iff x w hw).mpr ⟨hm, hv⟩
  apply hG.mulVec_injective
  rw [weightedEstimate, mulVec_mulVec,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG.isUnit), one_mulVec]
  exact (normal_matrix x y w (ne_of_gt hm) (ne_of_gt hv)).symm

/-- Scalar sign feasibility is precisely generic inverse-matrix feasibility. -/
theorem signFeasible_iff (x y w : ι → ℝ) :
    SignFeasible x y w ↔ Feasible (design x) y slopeTarget 0 w := by
  constructor
  · rintro ⟨hb, hm, hv, hc⟩
    refine ⟨hb, (gram_posDef_iff x w (fun i => (hb i).1)).mpr ⟨hm, hv⟩, ?_⟩
    rw [inverse_estimate x y w (fun i => (hb i).1) hm hv]
    simpa [slopeTarget, dotProduct, Fin.sum_univ_two] using
      (slope_nonpos_iff x y w hv).mpr hc
  · rintro ⟨hb, hG, hs⟩
    obtain ⟨hm, hv⟩ := (gram_posDef_iff x w (fun i => (hb i).1)).mp hG
    refine ⟨hb, hm, hv, (slope_nonpos_iff x y w hv).mp ?_⟩
    rw [inverse_estimate x y w (fun i => (hb i).1) hm hv] at hs
    simpa [slopeTarget, dotProduct, Fin.sum_univ_two] using hs

omit [Fintype ι] in
/-- Distinct regressor values suffice for the generic design-row hypothesis. -/
theorem design_generalPosition (x : ι → ℝ) (hx : Function.Injective x) :
    GeneralPosition (design x) := by
  classical
  intro s hs
  have hc : Fintype.card s = 2 := by simpa using hs
  let e := Fintype.equivFinOfCardEq hc
  apply (linearIndependent_equiv e.symm).mp
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have := congrFun h 1
    norm_num [design] at this
  · intro a ha
    have h1 : a = 1 := by simpa [design] using congrFun ha 1
    have h0 : x (e.symm 1) = x (e.symm 0) := by
      simpa [design, h1] using congrFun ha 0
    have he := hx h0
    have hi : e.symm 1 = e.symm 0 := Subtype.ext he
    have := e.symm.injective hi
    norm_num at this

open Classical in
/-- Attained sparse scalar optima, derived from the actual OLS model. A feasible
point of mass above one suffices; neither an optimizer nor a sparse input is
assumed. The optimum is global over all nonsingular scalar box weights. -/
theorem exists_sparse_massOptimal (x y w : ι → ℝ) (hx : Function.Injective x)
    (hw : SignFeasible x y w) (hm : 1 < mass w) :
    ∃ u, MassOptimal x y u ∧
      fractionalStability (design x) y slopeTarget 0 = Fintype.card ι - mass u ∧
      (Finset.univ.filter fun i => 0 < u i ∧ u i < 1).card ≤ 2 := by
  obtain ⟨u, hu, hf, hc⟩ := fractionalStability_attained_sparse (design x)
    (design_generalPosition x hx) y slopeTarget 0 w ((signFeasible_iff x y w).mp hw)
    (by norm_num; exact hm)
  refine ⟨u, ⟨(signFeasible_iff x y u).mpr hu, ?_⟩, hf, by simpa using hc⟩
  intro v hv
  have h := fractionalStability_le (design x) y slopeTarget 0 v
    ((signFeasible_iff x y v).mp hv)
  rw [hf] at h
  change _ - mass u ≤ _ - mass v at h
  linarith

open Classical in
/-- Generic rounding returns an actual nonsingular scalar subset and loses
strictly less than two units of mass, from arbitrary feasible scalar weights. -/
theorem exists_round_sign_subset (x y w : ι → ℝ) (hx : Function.Injective x)
    (hw : SignFeasible x y w) (hm : 4 ≤ mass w) :
    ∃ s : Finset ι, SignFeasible x y (fun i => if i ∈ s then 1 else 0) ∧
      mass w - (s.card : ℝ) < 2 := by
  classical
  obtain ⟨s, hs, hl⟩ := exists_round_subset (design x) (design_generalPosition x hx)
    y slopeTarget 0 w ((signFeasible_iff x y w).mp hw) (by norm_num; exact hm)
  exact ⟨s, (signFeasible_iff x y _).mpr hs, by simpa [mass] using hl⟩

open Classical in
/-- Proposition 5.3 with existence and sparsity discharged: under distinct
regressors and feasible retained mass at least four there is an attained global
optimum, with at most two fractional observations, on its own hyperbolic
threshold. Any fractional pair is weakly anti-monotone. -/
theorem exists_sparse_self_centered (x y w : ι → ℝ) (hx : Function.Injective x)
    (hw : SignFeasible x y w) (hm : 4 ≤ mass w)
    (hfull : 0 < crossNumerator x y (fun _ => 1)) :
    ∃ u, MassOptimal x y u ∧
      (Finset.univ.filter fun i => 0 < u i ∧ u i < 1).card ≤ 2 ∧
      crossNumerator x y u = 0 ∧ ∃ τ : ℝ,
      (∀ i, 0 < u i → centeredScore x y u i ≤ τ) ∧
      (∀ i, u i < 1 → τ ≤ centeredScore x y u i) ∧
      (∀ i, 0 < u i ∧ u i < 1 → centeredScore x y u i = τ) ∧
      (0 < τ ∨ ∀ i, 0 < u i → centeredScore x y u i = 0) ∧
      (∀ i j, i ≠ j → 0 < u i ∧ u i < 1 → 0 < u j ∧ u j < 1 →
        (x i - x j) * (y i - y j) ≤ 0) := by
  obtain ⟨u, hu, _, hc⟩ := exists_sparse_massOptimal x y w hx hw (by linarith)
  obtain ⟨hz, τ, ha, hb, he, ht⟩ := hu.self_centered x y u hfull
  exact ⟨u, hu, hc, hz, τ, ha, hb, he, ht, hu.fractional_pair x y u hfull⟩

end Cslib.LeastSquares.Simple
