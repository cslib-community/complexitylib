/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.Kronecker
public import Complexity.Foundations.Quantum.Measurement

/-!
# Bipartite pure states

A pure state of a bipartite system with computational bases `ι` and `κ` is a vector of
`ℂ^{ι × κ}`. This file provides:

* the product state `ψ ⊗ φ` with amplitudes `ψ_i φ_k` (`Cslib.Quantum.prodState`), the coordinate
  form of the tensor product `ℂ^ι ⊗ ℂ^κ ≅ ℂ^{ι × κ}`, with `⟪ψ ⊗ φ, ψ' ⊗ φ'⟫ = ⟪ψ, ψ'⟫ ⟪φ, φ'⟫`;
* the action of Kronecker products `A ⊗ₖ B` on product states (for the action of `A ⊗ₖ 1` and
  `1 ⊗ₖ B` on any state, see `Matrix.kronecker_one_mulVec_apply` and
  `Matrix.one_kronecker_mulVec_apply`);
* measuring the first system in the computational basis: for outcome `i` the second system is
  left in the conditional state `(⟨i| ⊗ 1) Ψ` (`Cslib.Quantum.condState`), of squared norm the
  probability of `i` (`Cslib.Quantum.measure_map_fst_apply`), which normalizes to the
  post-measurement state (`Cslib.Quantum.postMeasure`), [de Wolf][deWolf2019], Section 1.3.

## Main definitions

* `Cslib.Quantum.prodState`: the product state `ψ ⊗ φ`.
* `Cslib.Quantum.condState`: the unnormalized state of the second system after outcome `i` on the
  first.
* `Cslib.Quantum.postMeasure`: its normalization, the post-measurement state.

## Main results

* `Cslib.Quantum.inner_prodState`, `Cslib.Quantum.norm_prodState`: inner products and norms of
  product states factor.
* `Cslib.Quantum.kronecker_mulVec_prodState`: `(A ⊗ₖ B)(ψ ⊗ φ) = Aψ ⊗ Bφ`.
* `Cslib.Quantum.measure_map_fst_apply`: the probability of outcome `i` on the first system is
  `‖condState i Ψ‖²`.
* `Cslib.Quantum.norm_postMeasure`: the post-measurement state of a possible outcome is a unit
  vector.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker

variable {ι κ : Type*}

/-! ### Product states -/

/-- The **product state** `ψ ⊗ φ ∈ ℂ^{ι × κ}`, with amplitudes `(ψ ⊗ φ)_{(i, k)} = ψ_i φ_k`. -/
noncomputable def prodState (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 fun p => ψ.ofLp p.1 * φ.ofLp p.2

@[simp] theorem prodState_apply (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) (p : ι × κ) :
    (prodState ψ φ).ofLp p = ψ.ofLp p.1 * φ.ofLp p.2 := by
  rfl

theorem prodState_add_left (ψ ψ' : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) :
    prodState (ψ + ψ') φ = prodState ψ φ + prodState ψ' φ := by
  ext p; simp [add_mul]

theorem prodState_smul_left (c : ℂ) (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) :
    prodState (c • ψ) φ = c • prodState ψ φ := by
  ext p; simp [mul_assoc]

theorem prodState_ket [DecidableEq ι] [DecidableEq κ] (i : ι) (k : κ) :
    prodState (ket i) (ket k) = ket (i, k) := by
  ext ⟨a, b⟩
  by_cases ha : a = i <;> by_cases hb : b = k <;> simp [ha, hb]

theorem inner_prodState [Fintype ι] [Fintype κ] (ψ ψ' : EuclideanSpace ℂ ι)
    (φ φ' : EuclideanSpace ℂ κ) :
    inner ℂ (prodState ψ φ) (prodState ψ' φ') = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, prodState_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum, Pi.star_apply, star_mul']
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

theorem norm_prodState [Fintype ι] [Fintype κ] (ψ : EuclideanSpace ℂ ι)
    (φ : EuclideanSpace ℂ κ) : ‖prodState ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  have h := inner_prodState ψ ψ φ φ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖prodState ψ φ‖ ^ 2 = (‖ψ‖ * ‖φ‖) ^ 2 := by
    rw [mul_pow]; exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h'

/-! ### Kronecker products -/

/-- `(A ⊗ₖ B)(ψ ⊗ φ) = Aψ ⊗ Bφ`; see `Matrix.kronecker_mulVec_mul` for the action of a
Kronecker product on vectors over any commutative semiring. -/
theorem kronecker_mulVec_prodState [Fintype ι] [Fintype κ] (A : Matrix ι ι ℂ)
    (B : Matrix κ κ ℂ) (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) :
    (A ⊗ₖ B) *ᵥ (prodState ψ φ).ofLp = fun p => (A *ᵥ ψ.ofLp) p.1 * (B *ᵥ φ.ofLp) p.2 :=
  kronecker_mulVec_mul A B ψ.ofLp φ.ofLp

/-! ### Measuring the first system -/

/-- The **conditional state** `(⟨i| ⊗ 1) Ψ` of the second system after outcome `i` of a
computational-basis measurement of the first: the unnormalized post-measurement state, with
amplitudes `Ψ_{(i, k)}`. -/
noncomputable def condState (i : ι) : EuclideanSpace ℂ (ι × κ) →ₗ[ℂ] EuclideanSpace ℂ κ where
  toFun Ψ := WithLp.toLp 2 fun k => Ψ.ofLp (i, k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem condState_apply (i : ι) (Ψ : EuclideanSpace ℂ (ι × κ)) (k : κ) :
    (condState i Ψ).ofLp k = Ψ.ofLp (i, k) := by
  rfl

theorem condState_prodState (i : ι) (ψ : EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ κ) :
    condState i (prodState ψ φ) = ψ.ofLp i • φ := by
  ext k; simp

/-- The squared norm of the conditional state is the probability of the outcome. -/
theorem norm_condState_sq [Fintype ι] [Fintype κ] [DecidableEq ι] (i : ι)
    (Ψ : EuclideanSpace ℂ (ι × κ)) :
    ‖condState i Ψ‖ ^ 2 = measureProb Ψ (univ.filter fun p => p.1 = i) := by
  rw [EuclideanSpace.norm_sq_eq, measureProb, sum_filter, Fintype.sum_prod_type]
  simp

/-- Measuring the first system of a unit state `Ψ` gives outcome `i` with probability
`‖(⟨i| ⊗ 1) Ψ‖²`. -/
theorem measure_map_fst_apply [Fintype ι] [Fintype κ]
    (Ψ : EuclideanSpace ℂ (ι × κ)) (hΨ : ‖Ψ‖ = 1) (i : ι) :
    (measure Ψ hΨ).map Prod.fst i = ENNReal.ofReal (‖condState i Ψ‖ ^ 2) := by
  classical
  rw [PMF.map_apply, tsum_fintype, EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, Fintype.sum_prod_type,
    Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)]
  · simp
  · simp [Ne.symm hj]

/-- The **post-measurement state** `(⟨i| ⊗ 1) Ψ / ‖(⟨i| ⊗ 1) Ψ‖` of the second system after
outcome `i` on the first. -/
noncomputable def postMeasure [Fintype κ] (i : ι) (Ψ : EuclideanSpace ℂ (ι × κ)) :
    EuclideanSpace ℂ κ :=
  ((‖condState i Ψ‖⁻¹ : ℝ) : ℂ) • condState i Ψ

theorem postMeasure_def [Fintype κ] (i : ι) (Ψ : EuclideanSpace ℂ (ι × κ)) :
    postMeasure i Ψ = ((‖condState i Ψ‖⁻¹ : ℝ) : ℂ) • condState i Ψ := by
  rfl

/-- The post-measurement state of an outcome of positive probability is a unit vector. -/
theorem norm_postMeasure [Fintype κ] (i : ι) (Ψ : EuclideanSpace ℂ (ι × κ))
    (h : condState i Ψ ≠ 0) : ‖postMeasure i Ψ‖ = 1 := by
  rw [postMeasure, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)

end Cslib.Quantum
