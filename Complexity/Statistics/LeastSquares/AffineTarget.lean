/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.ExternalSolver
import Mathlib.Tactic

/-!
# Reducing affine least-squares targets to a zero coefficient

For a nonzero pivot `e j`, change coefficients by `β = b₀ + Bγ`, where
`b₀ = (θ / e j) uⱼ`, `Bⱼ = uⱼ / e j` and
`Bₗ = uₗ - (e l / e j) uⱼ` for `l ≠ j`. Then `e ⬝ᵥ β - θ = γ j`.
The transformed observations have identical residuals, including at singular
weights. This is an original adapter for the external decision contract in
[MoitraRohatgi2023], arXiv v2, Definition 1.1/Theorem 1.2 (PDF p. 3),
Section 3 (p. 6) and Appendix A (pp. 13–14), used by [XuGaoHu2027],
Corollary 3.4(iii), PDF p. 7. It preserves the full inequality feasible set,
not just coefficient-zero solutions. Exact-real optimum output is separate
from the threshold-decision and integer-bracket interface.

## Main results

* `residual`: residual agreement under the explicit coefficient change.
* `normal_iff`: correspondence of normal equations without nonsingularity.
* `gram_congruence`: the weighted Gram congruence for every real weight vector.
* `generalPosition_iff`: preservation of every dimension-sized row independence condition.
* `feasible_iff`: equality of the entire inequality feasible sets.
* `bracket_start`: general affine-target correctness of the external decision scan.
-/

public noncomputable section

namespace Cslib.LeastSquares.AffineTarget

open Matrix Set

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

/-- The sparse change of a design row. Its pivot entry is `a j / e j`. -/
@[expose] def row (e : d → ℝ) (j : d) (a : d → ℝ) : d → ℝ :=
  a - (a j / e j) • e + Pi.single j (a j / e j)

/-- Inverse row change, without division. -/
@[expose] def unrow (e : d → ℝ) (j : d) (a : d → ℝ) : d → ℝ :=
  a + a j • e - Pi.single j (a j)

/-- Linear coefficient change `Bγ`; the shift is added separately. -/
@[expose] def coeff (e : d → ℝ) (j : d) (γ : d → ℝ) : d → ℝ :=
  γ + Pi.single j ((γ j - e ⬝ᵥ γ) / e j)

/-- Inverse linear coefficient change. -/
@[expose] def uncoeff (e : d → ℝ) (j : d) (β : d → ℝ) : d → ℝ :=
  β + Pi.single j (e ⬝ᵥ β - β j)

/-- Coefficient origin mapping the affine boundary to zero. -/
@[expose] def origin (e : d → ℝ) (j : d) (θ : ℝ) : d → ℝ := Pi.single j (θ / e j)

/-- Shifted response; the design row is changed by `row`. -/
@[expose] def response (e : d → ℝ) (j : d) (θ : ℝ) (x : ι → d → ℝ)
    (y : ι → ℝ) : ι → ℝ := fun i => y i - θ * (x i j / e j)

omit [Fintype d] in
theorem unrow_row (e : d → ℝ) (j : d) (hj : e j ≠ 0) (a : d → ℝ) :
    unrow e j (row e j a) = a := by
  ext k
  by_cases hk : k = j
  · subst k; simp [row, unrow, hj]
  · simp [row, unrow, hk, hj]

omit [Fintype d] in
theorem row_unrow (e : d → ℝ) (j : d) (hj : e j ≠ 0) (a : d → ℝ) :
    row e j (unrow e j a) = a := by
  ext k
  by_cases hk : k = j
  · subst k; simp [row, unrow, hj]
  · simp [row, unrow, hk, hj]

/-- The design-row change is a linear equivalence, so it preserves row independence. -/
@[expose] def rowEquiv (e : d → ℝ) (j : d) (hj : e j ≠ 0) : (d → ℝ) ≃ₗ[ℝ] (d → ℝ) where
  toFun := row e j
  invFun := unrow e j
  left_inv := unrow_row e j hj
  right_inv := row_unrow e j hj
  map_add' a b := by
    ext k
    simp only [row, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, add_div]
    split_ifs <;> ring
  map_smul' r a := by
    ext k
    simp only [row, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, RingHom.id_apply]
    split_ifs <;> ring

theorem row_dot (e : d → ℝ) (j : d) (a γ : d → ℝ) :
    row e j a ⬝ᵥ γ = a ⬝ᵥ coeff e j γ := by
  simp only [row, coeff, add_dotProduct, sub_dotProduct, smul_dotProduct,
    single_dotProduct, dotProduct_add, dotProduct_single, smul_eq_mul]
  ring

theorem target_coeff (e : d → ℝ) (j : d) (hj : e j ≠ 0) (γ : d → ℝ) :
    e ⬝ᵥ coeff e j γ = γ j := by
  simp only [coeff, dotProduct_add, dotProduct_single]
  field_simp
  ring

theorem uncoeff_coeff (e : d → ℝ) (j : d) (hj : e j ≠ 0) (γ : d → ℝ) :
    uncoeff e j (coeff e j γ) = γ := by
  rw [uncoeff, target_coeff e j hj]
  ext k
  by_cases hk : k = j <;> simp [coeff, hk]

theorem coeff_uncoeff (e : d → ℝ) (j : d) (hj : e j ≠ 0) (β : d → ℝ) :
    coeff e j (uncoeff e j β) = β := by
  ext k
  by_cases hk : k = j
  · subst k
    simp only [coeff, uncoeff, dotProduct_add, dotProduct_single, Pi.add_apply,
      Pi.single_eq_same]
    field_simp
    ring
  · simp [coeff, uncoeff, hk]

/-- The transformed target is the pivot coefficient, with its sign unchanged. -/
theorem target (e : d → ℝ) (j : d) (hj : e j ≠ 0) (θ : ℝ) (γ : d → ℝ) :
    e ⬝ᵥ (origin e j θ + coeff e j γ) = θ + γ j := by
  rw [dotProduct_add, target_coeff e j hj]
  simp only [origin, dotProduct_single]
  rw [mul_div_cancel₀ θ hj]

omit [Fintype ι] in
/-- Residual agreement holds for every coefficient, independently of nonsingularity. -/
theorem residual (e : d → ℝ) (j : d) (θ : ℝ) (x : ι → d → ℝ)
    (y : ι → ℝ) (γ : d → ℝ) (i : ι) :
    response e j θ x y i - row e j (x i) ⬝ᵥ γ =
      y i - x i ⬝ᵥ (origin e j θ + coeff e j γ) := by
  rw [row_dot, dotProduct_add]
  simp only [response, origin, dotProduct_single]
  ring

omit [Fintype ι] in
/-- GP is preserved without changing observation indices or the dimension. -/
theorem generalPosition_iff (e : d → ℝ) (j : d) (hj : e j ≠ 0) (x : ι → d → ℝ) :
    GeneralPosition (fun i => row e j (x i)) ↔ GeneralPosition x := by
  constructor
  · intro h s hs
    have := (h s hs).map' (rowEquiv e j hj).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (rowEquiv e j hj).symm.injective)
    change LinearIndependent ℝ (fun i : s => unrow e j (row e j (x i))) at this
    simpa only [unrow_row e j hj] using this
  · intro h s hs
    exact (h s hs).map' (rowEquiv e j hj).toLinearMap
      (LinearMap.ker_eq_bot.mpr (rowEquiv e j hj).injective)

/-- Normal-equation vectors transform by the invertible row map, even for singular weights. -/
theorem normal_vector (e : d → ℝ) (j : d) (hj : e j ≠ 0) (θ : ℝ)
    (x : ι → d → ℝ) (y w : ι → ℝ) (γ : d → ℝ) :
    (∑ i, w i • ((response e j θ x y i - row e j (x i) ⬝ᵥ γ) • row e j (x i))) =
      row e j (∑ i, w i • ((y i - x i ⬝ᵥ (origin e j θ + coeff e j γ)) • x i)) := by
  change _ = (rowEquiv e j hj) _
  rw [map_sum]
  simp only [map_smul, rowEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  exact Finset.sum_congr rfl fun i _ => by rw [residual]

/-- Normal equations correspond in both directions without a rank assumption. -/
theorem normal_iff (e : d → ℝ) (j : d) (hj : e j ≠ 0) (θ : ℝ)
    (x : ι → d → ℝ) (y w : ι → ℝ) (γ : d → ℝ) :
    (∑ i, w i • ((response e j θ x y i - row e j (x i) ⬝ᵥ γ) • row e j (x i))) = 0 ↔
      (∑ i, w i • ((y i - x i ⬝ᵥ (origin e j θ + coeff e j γ)) • x i)) = 0 := by
  rw [normal_vector e j hj]
  exact (rowEquiv e j hj).map_eq_zero_iff

/-- The coefficient matrix `B` of the sparse change. -/
@[expose] def basisMatrix (e : d → ℝ) (j : d) : Matrix d d ℝ :=
  1 + vecMulVec (Pi.single j (1 / e j)) (Pi.single j 1 - e)

theorem basisMatrix_mulVec (e : d → ℝ) (j : d) (γ : d → ℝ) :
    basisMatrix e j *ᵥ γ = coeff e j γ := by
  ext k
  simp only [basisMatrix, add_mulVec, one_mulVec, vecMulVec_mulVec,
    sub_dotProduct, single_dotProduct, Pi.add_apply, Pi.smul_apply,
    Pi.single_apply, coeff, smul_eq_mul, op_smul_eq_smul]
  split_ifs <;> ring

theorem basisMatrix_isUnit (e : d → ℝ) (j : d) (hj : e j ≠ 0) :
    IsUnit (basisMatrix e j) := by
  apply mulVec_injective_iff_isUnit.mp
  intro a b hab
  simp only [basisMatrix_mulVec] at hab
  simpa only [uncoeff_coeff e j hj] using congrArg (uncoeff e j) hab

/-- Exact Gram congruence, for arbitrary real weights. -/
theorem gram_congruence (e : d → ℝ) (j : d) (x : ι → d → ℝ) (w : ι → ℝ) :
    weightedGram 0 Finset.univ (fun i => row e j (x i)) w =
      (basisMatrix e j)ᵀ * weightedGram 0 Finset.univ x w * basisMatrix e j := by
  apply Matrix.ext
  intro k l
  simp only [weightedGram, zero_add, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs =>
    arg 2; ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [vecMulVec_apply]
  symm
  have hrow (a : d → ℝ) (k : d) :
      (∑ m, a m * basisMatrix e j m k) = row e j a k := by
    have h := row_dot e j a (Pi.single k 1)
    rw [← basisMatrix_mulVec, dotProduct_mulVec] at h
    simpa only [dotProduct_single, mul_one, vecMul_apply_eq_sum] using h.symm
  calc
    _ = w i * ((∑ m, x i m * basisMatrix e j m k) *
        (∑ m, x i m * basisMatrix e j m l)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [hrow, hrow]

omit [Fintype d] in
/-- Positive definiteness corresponds for every weight vector, without GP. -/
theorem posDef_iff [Finite d] (e : d → ℝ) (j : d) (hj : e j ≠ 0)
    (x : ι → d → ℝ) (w : ι → ℝ) :
    (weightedGram 0 Finset.univ (fun i => row e j (x i)) w).PosDef ↔
      (weightedGram 0 Finset.univ x w).PosDef := by
  let := Fintype.ofFinite d
  rw [gram_congruence]
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
    (basisMatrix_isUnit e j hj).posDef_star_left_conjugate_iff

/-- The actual inverse-matrix fits correspond whenever the design is positive definite. -/
theorem estimate (e : d → ℝ) (j : d) (hj : e j ≠ 0) (θ : ℝ)
    (x : ι → d → ℝ) (y w : ι → ℝ) (hG : (weightedGram 0 Finset.univ x w).PosDef) :
    origin e j θ + coeff e j
      (weightedEstimate 0 0 Finset.univ (fun i => row e j (x i)) (response e j θ x y) w) =
        weightedEstimate 0 0 Finset.univ x y w := by
  apply Eq.symm
  apply weightedEstimate_eq_of_normal x y w
  · exact hG
  · apply (normal_iff e j hj θ x y w _).mp
    exact weightedEstimate_normal _ _ _ ((posDef_iff e j hj x w).mpr hG)

/-- The same weights satisfy exactly the same inequality target. -/
theorem feasible_iff (e : d → ℝ) (j : d) (hj : e j ≠ 0) (θ : ℝ)
    (x : ι → d → ℝ) (y w : ι → ℝ) :
    Feasible (fun i => row e j (x i)) (response e j θ x y) (Pi.single j 1) 0 w ↔
      Feasible x y e θ w := by
  simp only [Feasible, posDef_iff e j hj]
  constructor <;> rintro ⟨hbox, hG, ht⟩
  · refine ⟨hbox, hG, ?_⟩
    rw [← estimate e j hj θ x y w hG, target e j hj]
    simpa only [single_dotProduct, one_mul, add_le_iff_nonpos_right] using ht
  · refine ⟨hbox, hG, ?_⟩
    rw [← estimate e j hj θ x y w hG, target e j hj] at ht
    simpa only [single_dotProduct, one_mul, add_le_iff_nonpos_right] using ht

/-- The fractional feasible sets agree, hence so do their real infima. -/
theorem fractionalStability_eq (e : d → ℝ) (j : d) (hj : e j ≠ 0) (θ : ℝ)
    (x : ι → d → ℝ) (y : ι → ℝ) :
    fractionalStability (fun i => row e j (x i)) (response e j θ x y) (Pi.single j 1) 0 =
      fractionalStability x y e θ := by
  simp only [fractionalStability, feasible_iff e j hj]

/-- Integral feasibility agrees on the original subsets, including repeated observations. -/
theorem integralStability_eq (e : d → ℝ) (j : d) (hj : e j ≠ 0) (θ : ℝ)
    (x : ι → d → ℝ) (y : ι → ℝ) :
    integralStability (fun i => row e j (x i)) (response e j θ x y) (Pi.single j 1) 0 =
      integralStability x y e θ := by
  classical
  simp only [integralStability, feasible_iff e j hj]

/-- The singular-inclusive external equality decision is also invariant. -/
theorem equalityNormalDecision_iff (e : d → ℝ) (j : d) (hj : e j ≠ 0) (θ k : ℝ)
    (x : ι → d → ℝ) (y : ι → ℝ) :
    EqualityNormalDecision (fun i => row e j (x i)) (response e j θ x y) (Pi.single j 1) 0 k ↔
      EqualityNormalDecision x y e θ k := by
  constructor
  · rintro ⟨w, γ, hbox, hn, ht, hm⟩
    refine ⟨w, origin e j θ + coeff e j γ, hbox,
      (normal_iff e j hj θ x y w γ).mp hn, ?_, hm⟩
    rw [target e j hj]
    simpa only [single_dotProduct, one_mul, add_eq_left] using ht
  · rintro ⟨w, β, hbox, hn, ht, hm⟩
    let γ := uncoeff e j (β - origin e j θ)
    have hβ : origin e j θ + coeff e j γ = β := by
      dsimp only [γ]
      rw [coeff_uncoeff e j hj, add_sub_cancel]
    refine ⟨w, γ, hbox, (normal_iff e j hj θ x y w γ).mpr ?_, ?_, hm⟩
    · rwa [hβ]
    · have h := target e j hj θ γ
      rw [hβ, ht] at h
      simpa only [single_dotProduct, one_mul] using (show γ j = 0 by linarith)

/-- Simultaneous feasibility and strict full-data violation exclude the zero target vector. -/
theorem exists_pivot (e : d → ℝ) (θ : ℝ) (x : ι → d → ℝ) (y w : ι → ℝ)
    (hw : Feasible x y e θ w)
    (hfull : θ < e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1)) :
    ∃ j, e j ≠ 0 := by
  by_contra h
  have he : e = 0 := by ext j; simpa using not_exists.mp h j
  rw [he, zero_dotProduct] at hfull
  have := hw.2.2
  rw [he, zero_dotProduct] at this
  linarith

/-- General affine-target version of the actual threshold scan. The external
oracle is supplied on the explicitly transformed observations. -/
theorem bracket_start {n D : ℕ} (q : ℕ → Algorithms.Lean.TimeM ℕ Bool)
    (x : Fin n → Fin (D + 1) → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ)
    (e : Fin (D + 1) → ℝ) (j : Fin (D + 1)) (hj : e j ≠ 0) (θ : ℝ)
    (hq : ExternalSolver.NormalOracle q (fun i => row e j (x i)) (response e j θ x y) j)
    (hw : Feasible x y e θ w) (hmass : 2 * ((D + 1 : ℕ) : ℝ) ≤ ∑ i, w i)
    (hfull : θ < e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1)) :
    (ExternalSolver.search q (n - (D + 1))).ret = ⌈fractionalStability x y e θ⌉₊ := by
  have hG := hgp.weightedGram_posDef x (fun _ => 1) (by simp) (by
    have hsum : (∑ i, w i) ≤ n := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ => (1 : ℝ))
        (fun i _ => (hw.1 i).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    linarith)
  have hfull' : 0 < (Pi.single j 1) ⬝ᵥ weightedEstimate 0 0 Finset.univ
      (fun i => row e j (x i)) (response e j θ x y) (fun _ => 1) := by
    rw [← estimate e j hj θ x y _ hG, target e j hj] at hfull
    simpa only [single_dotProduct, one_mul, lt_add_iff_pos_right] using hfull
  have := ExternalSolver.bracket_start q _ ((generalPosition_iff e j hj x).mpr hgp)
    _ w j hq ((feasible_iff e j hj θ x y w).mpr hw) hmass hfull'
  rwa [fractionalStability_eq e j hj] at this

/-- The computed bracket covers integral stability for an arbitrary affine target. -/
theorem integral_bracket {n D : ℕ} (q : ℕ → Algorithms.Lean.TimeM ℕ Bool)
    (x : Fin n → Fin (D + 1) → ℝ) (hgp : GeneralPosition x) (y w : Fin n → ℝ)
    (e : Fin (D + 1) → ℝ) (j : Fin (D + 1)) (hj : e j ≠ 0) (θ : ℝ)
    (hq : ExternalSolver.NormalOracle q (fun i => row e j (x i)) (response e j θ x y) j)
    (hw : Feasible x y e θ w) (hmass : 2 * ((D + 1 : ℕ) : ℝ) ≤ ∑ i, w i)
    (hfull : θ < e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1)) :
    (ExternalSolver.search q (n - (D + 1))).ret ≤ integralStability x y e θ ∧
      integralStability x y e θ ≤ (ExternalSolver.search q (n - (D + 1))).ret + D := by
  rw [bracket_start q x hgp y w e j hj θ hq hw hmass hfull]
  obtain ⟨hlo, hhi⟩ := stability_ceiling_bounds x hgp y e θ w hw (by simpa using hmass)
  simp only [Fintype.card_fin] at hhi
  exact ⟨hlo, by omega⟩

end Cslib.LeastSquares.AffineTarget
