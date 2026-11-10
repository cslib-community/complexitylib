/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Linarith

/-!
# Mixed strategies

A *mixed strategy* over a finite set `ι` of pure strategies is a probability vector `x : ι → ℝ`:
its entries are nonnegative and sum to `1` (`Cslib.GameTheory.IsMixedStrategy`). Mixed strategies
are plain vectors, so that they can be fed to `Matrix.mulVec`, to the polyhedral API in
`CslibFrontier.Foundations.LinearAlgebra.Matrix.Vertex` and to continuous maps on `ι → ℝ`. They
are exactly the weight vectors of the points of `Convexity.StdSimplex ℝ ι`, the representation of
distributions used in `CslibFrontier.Probability.Minimax` and
`CslibFrontier.GameTheory.Strategic.Smooth`
(`Cslib.GameTheory.isMixedStrategy_iff_mem_range_weights`).

## Main definitions

* `Cslib.GameTheory.IsMixedStrategy`: a probability vector.

## Main results

* `Cslib.GameTheory.IsMixedStrategy.forall_dotProduct_le_iff`: a probability vector maximizes a
  linear function over the simplex iff its support consists of maximizers.
* `Cslib.GameTheory.isMixedStrategy_iff_mem_range_weights`: mixed strategies are the weight vectors
  of the points of `Convexity.StdSimplex ℝ ι`.
* `Cslib.GameTheory.IsMixedStrategy.dotProduct_le_of_forall_le`,
  `Cslib.GameTheory.IsMixedStrategy.dotProduct_eq_of_forall_pos`: averages under a mixed strategy.
-/

public section

open Finset Matrix

namespace Cslib.GameTheory

variable {ι : Type*} [Fintype ι] {x w : ι → ℝ} {c : ℝ}

/-- A *mixed strategy* over a finite set `ι` of pure strategies: a probability vector. -/
def IsMixedStrategy (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

theorem isMixedStrategy_iff : IsMixedStrategy x ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 :=
  Iff.rfl

theorem IsMixedStrategy.nonneg (hx : IsMixedStrategy x) (i : ι) : 0 ≤ x i := hx.1 i

theorem IsMixedStrategy.sum_eq_one (hx : IsMixedStrategy x) : ∑ i, x i = 1 := hx.2

/-- A mixed strategy plays some pure strategy with positive probability. -/
theorem IsMixedStrategy.exists_pos (hx : IsMixedStrategy x) : ∃ i, 0 < x i := by
  by_contra hne
  push Not at hne
  have : ∑ i, x i = 0 := sum_eq_zero fun i _ => le_antisymm (hne i) (hx.1 i)
  rw [hx.2] at this
  exact one_ne_zero this

theorem IsMixedStrategy.ne_zero (hx : IsMixedStrategy x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := hx.exists_pos
  exact lt_irrefl _ hi

/-- Averaging a positive vector under a mixed strategy gives a positive number. -/
theorem IsMixedStrategy.dotProduct_pos (hx : IsMixedStrategy x) (hw : ∀ i, 0 < w i) :
    0 < x ⬝ᵥ w := by
  obtain ⟨i, hi⟩ := hx.exists_pos
  exact (sum_pos_iff_of_nonneg fun j _ => mul_nonneg (hx.1 j) (hw j).le).2
    ⟨i, mem_univ _, mul_pos hi (hw i)⟩

/-- Normalizing a nonzero nonnegative vector gives a mixed strategy. -/
theorem isMixedStrategy_inv_sum_smul (hx : ∀ i, 0 ≤ x i) (hx₀ : x ≠ 0) :
    IsMixedStrategy ((∑ i, x i)⁻¹ • x) := by
  have hpos : 0 < ∑ i, x i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx₀
    exact (sum_pos_iff_of_nonneg fun j _ => hx j).2 ⟨i, mem_univ _, (hx i).lt_of_ne' hi⟩
  refine ⟨fun i => smul_nonneg (inv_nonneg.2 hpos.le) (hx i), ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
  exact inv_mul_cancel₀ hpos.ne'

/-- A mixed strategy is determined by the ray it spans. -/
theorem IsMixedStrategy.eq_of_smul_eq_smul {x' : ι → ℝ} {c' : ℝ} (hx : IsMixedStrategy x)
    (hx' : IsMixedStrategy x') (hc : c ≠ 0) (h : c • x = c' • x') : x = x' := by
  have hcc : c = c' := by
    have := congrArg (fun v : ι → ℝ => ∑ i, v i) h
    simpa only [Pi.smul_apply, smul_eq_mul, ← mul_sum, hx.2, hx'.2, mul_one] using this
  subst hcc
  exact smul_right_injective _ hc h

/-- Mixed strategies are the weight vectors of the points of `Convexity.StdSimplex ℝ ι`. -/
theorem isMixedStrategy_iff_mem_range_weights :
    IsMixedStrategy x ↔ x ∈ Set.range fun p : Convexity.StdSimplex ℝ ι => (p.weights : ι → ℝ) := by
  rw [Convexity.StdSimplex.range_toFun_comp_weights]
  simp [IsMixedStrategy]

theorem isMixedStrategy_weights (p : Convexity.StdSimplex ℝ ι) :
    IsMixedStrategy (p.weights : ι → ℝ) :=
  isMixedStrategy_iff_mem_range_weights.2 ⟨p, rfl⟩

/-- A pure strategy, as a mixed strategy. -/
theorem isMixedStrategy_single [DecidableEq ι] (i : ι) : IsMixedStrategy (Pi.single i (1 : ℝ)) :=
  ⟨fun j => by by_cases h : j = i <;> simp [h], by simp⟩

/-- Averaging a vector that equals `c` on the support of a mixed strategy gives `c`. -/
theorem IsMixedStrategy.dotProduct_eq_of_forall_pos (hx : IsMixedStrategy x)
    (h : ∀ i, 0 < x i → w i = c) : x ⬝ᵥ w = c := by
  calc x ⬝ᵥ w = ∑ i, x i * c := by
        refine sum_congr rfl fun i _ => ?_
        rcases (hx.1 i).lt_or_eq with hi | hi
        · rw [h i hi]
        · rw [← hi, zero_mul, zero_mul]
    _ = c := by rw [← sum_mul, hx.2, one_mul]

/-- Averaging a vector bounded by `c` under a mixed strategy gives at most `c`. -/
theorem IsMixedStrategy.dotProduct_le_of_forall_le (hx : IsMixedStrategy x) (h : ∀ i, w i ≤ c) :
    x ⬝ᵥ w ≤ c := by
  calc x ⬝ᵥ w = ∑ i, x i * w i := rfl
    _ ≤ ∑ i, x i * c := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hx.1 i)
    _ = c := by rw [← sum_mul, hx.2, one_mul]

/-- A mixed strategy maximizes the linear function `x ↦ x ⬝ᵥ w` over all mixed strategies iff every
pure strategy in its support maximizes `w`. -/
theorem IsMixedStrategy.forall_dotProduct_le_iff (hx : IsMixedStrategy x) :
    (∀ x', IsMixedStrategy x' → x' ⬝ᵥ w ≤ x ⬝ᵥ w) ↔ ∀ i, 0 < x i → ∀ i', w i' ≤ w i := by
  classical
  constructor
  · intro h i hi i'
    by_contra hlt
    push Not at hlt
    obtain ⟨i₀, -, hi₀⟩ := exists_max_image univ w ⟨i, mem_univ _⟩
    have h₁ := h _ (isMixedStrategy_single i₀)
    rw [single_dotProduct, one_mul] at h₁
    have h₂ : x ⬝ᵥ w < w i₀ := by
      calc x ⬝ᵥ w = ∑ j, x j * w j := rfl
        _ < ∑ j, x j * w i₀ := by
          refine sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (hi₀ j (mem_univ _)) (hx.1 j))
            ⟨i, mem_univ _, mul_lt_mul_of_pos_left
              (hlt.trans_le (hi₀ i' (mem_univ _))) hi⟩
        _ = w i₀ := by rw [← sum_mul, hx.2, one_mul]
    linarith
  · intro h x' hx'
    obtain ⟨i₀, hi₀⟩ := hx.exists_pos
    rw [hx.dotProduct_eq_of_forall_pos fun i hi => le_antisymm (h i₀ hi₀ i) (h i hi i₀)]
    exact hx'.dotProduct_le_of_forall_le (h i₀ hi₀)

end Cslib.GameTheory
