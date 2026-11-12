/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Mathlib/Analysis/CStarAlgebra/Matrix.lean)

public import CslibFrontier.Init
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Euclidean operator-norm bounds for real matrices

Bilinear operator-norm characterization, Schur's test, and entry bounds for the `ℓ²` operator norm
`‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖` on finite real matrices.

## Main definitions

* `Matrix.absVec`: coordinatewise absolute-value vector in `EuclideanSpace ℝ κ`.

## Main results

* `Matrix.absVec_apply`, `Matrix.norm_absVec_le`, `Matrix.inner_toEuclideanCLM_le_absVec`:
  entrywise nonnegativity and absolute-value comparison for bilinear forms.
* `Matrix.opNorm_toEuclideanCLM_le_of_inner`: `‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ C` from
  unit-ball bilinear evaluations `inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) ≤ C`.
* `Matrix.opNorm_toEuclideanCLM_le_sqrt`: Schur's test, bounding
  `‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖` by `√(R · C)` from row and column `ℓ¹` bounds `R` and `C`.
* `Matrix.abs_entry_le_norm_toEuclideanCLM`: every entry magnitude is at most
  `‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖`.
-/

public section

namespace Matrix

open Finset

/-- Coordinatewise absolute-value vector in `EuclideanSpace ℝ κ`. -/
@[expose] noncomputable def absVec {κ : Type*} (u : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ κ :=
  WithLp.toLp 2 fun x => |u.ofLp x|

@[simp] theorem absVec_apply {κ : Type*} (u : EuclideanSpace ℝ κ) (x : κ) :
    (absVec u).ofLp x = |u.ofLp x| :=
  rfl

theorem norm_absVec_le {κ : Type*} [Fintype κ] {u : EuclideanSpace ℝ κ} (hu : ‖u‖ ≤ 1) :
    ‖absVec u‖ ≤ 1 := by
  rw [← sq_le_one_iff₀ (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
  simpa [EuclideanSpace.real_norm_sq_eq] using pow_le_one₀ (n := 2) (norm_nonneg u) hu

theorem inner_toEuclideanCLM_le_absVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Γ : Matrix κ κ ℝ} (hnonneg : ∀ x y, 0 ≤ Γ x y) (u v : EuclideanSpace ℝ κ) :
    inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ v) ≤
      inner ℝ (absVec u) (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (absVec v)) := by
  rw [Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, mul_sum, absVec_apply]
  refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
  have heq : u.ofLp x * (Γ x y * v.ofLp y) = Γ x y * (u.ofLp x * v.ofLp y) := by ring
  have heqPos : |u.ofLp x| * (Γ x y * |v.ofLp y|) = Γ x y * (|u.ofLp x| * |v.ofLp y|) := by ring
  rw [heq, heqPos]
  refine mul_le_mul_of_nonneg_left ?_ (hnonneg x y)
  rw [← abs_mul]
  exact le_abs_self _

/-- Operator norm bound from bilinear evaluations on vectors of norm at most `1`. -/
theorem opNorm_toEuclideanCLM_le_of_inner {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u v : EuclideanSpace ℝ κ, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) ≤ C) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le hC fun v u hv hu => ?_
  rw [RCLike.re_to_real, real_inner_comm]
  exact h u v hu.le hv.le

private theorem sum_abs_mul_sq_le_of_row_le {κ : Type*} [Fintype κ]
    (A : Matrix κ κ ℝ) {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ x, ∑ y, |A x y| ≤ R)
    {u : EuclideanSpace ℝ κ} (hu : ‖u‖ ≤ 1) :
    ∑ p : κ × κ, (√(|A p.1 p.2|) * |u.ofLp p.1|) ^ 2 ≤ R := by
  rw [Fintype.sum_prod_type]
  calc ∑ x, ∑ y, (√(|A x y|) * |u.ofLp x|) ^ 2
      = ∑ x, u.ofLp x ^ 2 * ∑ y, |A x y| := by
          refine sum_congr rfl fun x _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun y _ => ?_
          rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs, mul_comm]
    _ ≤ ∑ x, u.ofLp x ^ 2 * R :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hrow x) (sq_nonneg _)
    _ = (∑ x, u.ofLp x ^ 2) * R := (sum_mul _ _ _).symm
    _ ≤ 1 * R := by
          refine mul_le_mul_of_nonneg_right ?_ hR
          rw [← EuclideanSpace.real_norm_sq_eq]
          exact pow_le_one₀ (norm_nonneg _) hu
    _ = R := one_mul R

/-- **Schur's test** for Euclidean operator norms: if row `ℓ¹` norms are at most `R` and column
`ℓ¹` norms are at most `C`, then `‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ √(R · C)`. -/
theorem opNorm_toEuclideanCLM_le_sqrt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ x, ∑ y, |A x y| ≤ R) (hcol : ∀ y, ∑ x, |A x y| ≤ C) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ √(R * C) := by
  refine opNorm_toEuclideanCLM_le_of_inner A (Real.sqrt_nonneg _) fun u v hu hv => ?_
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, mul_sum]
  have h1 : ∑ x, ∑ y, u.ofLp x * (A x y * v.ofLp y) ≤
      ∑ x, ∑ y, |A x y| * (|u.ofLp x| * |v.ofLp y|) := by
    refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
    calc u.ofLp x * (A x y * v.ofLp y) ≤ |u.ofLp x * (A x y * v.ofLp y)| := le_abs_self _
      _ = |A x y| * (|u.ofLp x| * |v.ofLp y|) := by rw [abs_mul, abs_mul]; ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (κ × κ))
    (fun p => √(|A p.1 p.2|) * |u.ofLp p.1|) (fun p => √(|A p.1 p.2|) * |v.ofLp p.2|)
  have hterm : (∑ x, ∑ y, |A x y| * (|u.ofLp x| * |v.ofLp y|)) =
      ∑ p : κ × κ, (√(|A p.1 p.2|) * |u.ofLp p.1|) * (√(|A p.1 p.2|) * |v.ofLp p.2|) := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    calc |A x y| * (|u.ofLp x| * |v.ofLp y|)
        = (√(|A x y|) * √(|A x y|)) * (|u.ofLp x| * |v.ofLp y|) := by
            rw [Real.mul_self_sqrt (abs_nonneg _)]
      _ = (√(|A x y|) * |u.ofLp x|) * (√(|A x y|) * |v.ofLp y|) := by ring
  have hlhs : ∑ p : κ × κ, (√(|A p.1 p.2|) * |u.ofLp p.1|) ^ 2 ≤ R :=
    sum_abs_mul_sq_le_of_row_le A hR hrow hu
  have hrhs : ∑ p : κ × κ, (√(|A p.1 p.2|) * |v.ofLp p.2|) ^ 2 ≤ C := by
    have ht := sum_abs_mul_sq_le_of_row_le Aᵀ hC (fun y => by simpa [transpose_apply] using hcol y)
      hv
    rw [Fintype.sum_prod_type, sum_comm]
    rw [Fintype.sum_prod_type] at ht
    simpa [transpose_apply] using ht
  calc ∑ x, ∑ y, u.ofLp x * (A x y * v.ofLp y)
      ≤ ∑ p : κ × κ, (√(|A p.1 p.2|) * |u.ofLp p.1|) * (√(|A p.1 p.2|) * |v.ofLp p.2|) :=
        hterm ▸ h1
    _ ≤ √(∑ p : κ × κ, (√(|A p.1 p.2|) * |u.ofLp p.1|) ^ 2) *
          √(∑ p : κ × κ, (√(|A p.1 p.2|) * |v.ofLp p.2|) ^ 2) := hcs
    _ ≤ √R * √C := mul_le_mul (Real.sqrt_le_sqrt hlhs) (Real.sqrt_le_sqrt hrhs)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = √(R * C) := (Real.sqrt_mul hR _).symm

/-- Every matrix entry has magnitude at most its Euclidean operator norm. -/
theorem abs_entry_le_norm_toEuclideanCLM {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) (x y : κ) :
    |A x y| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by
  set ex : EuclideanSpace ℝ κ := EuclideanSpace.single x 1
  set ey : EuclideanSpace ℝ κ := EuclideanSpace.single y 1
  have hex : ‖ex‖ = 1 := by simp [ex, PiLp.norm_single]
  have hey : ‖ey‖ = 1 := by simp [ey, PiLp.norm_single]
  have hxy : inner ℝ ex (Matrix.toEuclideanCLM (𝕜 := ℝ) A ey) = A x y := by
    rw [Matrix.inner_toEuclideanCLM]
    simp [ex, ey, dotProduct, Matrix.mulVec]
  calc |A x y| = |inner ℝ ex (Matrix.toEuclideanCLM (𝕜 := ℝ) A ey)| := by rw [hxy]
    _ ≤ ‖ex‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A ey‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖ey‖) := by
          rw [hex]
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) zero_le_one
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := by rw [hey, mul_one, one_mul]

end Matrix
