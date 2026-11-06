/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-!
# Positive definite Gram matrices from spanning families

A finite family spanning the real coordinate space has positive definite Gram
matrix `∑ x xᵀ`. The proof uses only finite sums and orthogonality and applies
also to an empty coordinate type. No independence or cardinality hypothesis
is imposed on the spanning family.
-/

public section

namespace Matrix

open Submodule

variable {ι d : Type*}

/-- A spanning family of observations has a positive definite unweighted Gram matrix. -/
theorem posDef_sum_vecMulVec_of_span_eq_top [Finite d] (s : Finset ι) (x : ι → d → ℝ)
    (hspan : span ℝ (x '' (s : Set ι)) = ⊤) :
    (∑ i ∈ s, vecMulVec (x i) (x i)).PosDef := by
  classical
  let := Fintype.ofFinite d
  have hps : (∑ i ∈ s, vecMulVec (x i) (x i)).PosSemidef := by
    exact posSemidef_sum s fun i hi => by simpa using posSemidef_vecMulVec_self_star (x i)
  refine posDef_iff_dotProduct_mulVec.mpr ⟨hps.isHermitian, ?_⟩
  intro v hv
  have hex : ∃ i ∈ s, v ⬝ᵥ x i ≠ 0 := by
    by_contra h
    have hz : ∀ i ∈ s, v ⬝ᵥ x i = 0 := by simpa using h
    let f : (d → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun u => v ⬝ᵥ u
        map_add' := fun u z => dotProduct_add v u z
        map_smul' := fun a u => by simp [dotProduct_smul] }
    have hf : span ℝ (x '' (s : Set ι)) ≤ LinearMap.ker f := by
      apply span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      exact hz i hi
    have hself : v ⬝ᵥ v = 0 := hf (by rw [hspan]; trivial)
    exact hv (dotProduct_self_eq_zero.mp hself)
  have hq : star v ⬝ᵥ ((∑ i ∈ s, vecMulVec (x i) (x i)) *ᵥ v) =
      ∑ i ∈ s, (v ⬝ᵥ x i) ^ 2 := by
    simp only [star_trivial, sum_mulVec, dotProduct_sum, vecMulVec_mulVec,
      dotProduct_smul, op_smul_eq_smul, smul_eq_mul, dotProduct_comm (x _), pow_two]
  rw [hq]
  exact Finset.sum_pos' (fun i hi => sq_nonneg _) (by
    obtain ⟨i, hi, hne⟩ := hex
    exact ⟨i, hi, sq_pos_of_ne_zero hne⟩)

end Matrix
