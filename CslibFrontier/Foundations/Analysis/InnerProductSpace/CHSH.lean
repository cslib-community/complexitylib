/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The CHSH inequality for vectors

For vectors `u₀, u₁, v₀, v₁` of norm at most `1` in an inner product space,
`Re⟨u₀, v₀⟩ + Re⟨u₀, v₁⟩ + Re⟨u₁, v₀⟩ - Re⟨u₁, v₁⟩ ≤ 2√2` (`chsh_re_inner_le`). The first two terms
are at most `‖v₀ + v₁‖` and the last two at most `‖v₀ - v₁‖` by Cauchy–Schwarz, and the
parallelogram law bounds `‖v₀ + v₁‖ + ‖v₀ - v₁‖` by `2√2`. Applied to the vectors `(A_x ⊗ 1) ψ`
and `(1 ⊗ B_y) ψ` of a quantum strategy, this is Tsirelson's inequality
[Cirel'son][Cirelson1980].

Mathlib's `tsirelson_inequality` (`Mathlib.Algebra.Star.CHSH`) is the operator form of the same
bound, for a CHSH tuple of self-adjoint involutions in an ordered `*`-algebra.

## Main results

* `chsh_re_inner_le`: the CHSH inequality for vectors of norm at most `1`.

## References

* [B. S. Cirel'son, *Quantum generalizations of Bell's inequality*][Cirelson1980]
-/

public section

/-- The **CHSH inequality for vectors**: for vectors `u₀, u₁, v₀, v₁` of norm at most `1` in an
inner product space, `Re⟨u₀,v₀⟩ + Re⟨u₀,v₁⟩ + Re⟨u₁,v₀⟩ - Re⟨u₁,v₁⟩ ≤ 2√2`. -/
theorem chsh_re_inner_le {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {u₀ u₁ v₀ v₁ : E} (hu₀ : ‖u₀‖ ≤ 1) (hu₁ : ‖u₁‖ ≤ 1) (hv₀ : ‖v₀‖ ≤ 1) (hv₁ : ‖v₁‖ ≤ 1) :
    RCLike.re (inner 𝕜 u₀ v₀) + RCLike.re (inner 𝕜 u₀ v₁) + RCLike.re (inner 𝕜 u₁ v₀) -
      RCLike.re (inner 𝕜 u₁ v₁) ≤ 2 * √2 := by
  have h₀ : RCLike.re (inner 𝕜 u₀ v₀) + RCLike.re (inner 𝕜 u₀ v₁) ≤ ‖v₀ + v₁‖ := by
    rw [← map_add, ← inner_add_right]
    exact (re_inner_le_norm u₀ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu₀)
  have h₁ : RCLike.re (inner 𝕜 u₁ v₀) - RCLike.re (inner 𝕜 u₁ v₁) ≤ ‖v₀ - v₁‖ := by
    rw [← map_sub, ← inner_sub_right]
    exact (re_inner_le_norm u₁ _).trans (mul_le_of_le_one_left (norm_nonneg _) hu₁)
  have hpar := parallelogram_law_with_norm 𝕜 v₀ v₁
  have hv₀' : ‖v₀‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hv₀
  have hv₁' : ‖v₁‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hv₁
  have hs : (2 * √2) ^ 2 = 8 := by rw [mul_pow, Real.sq_sqrt zero_le_two]; norm_num
  have hab : ‖v₀ + v₁‖ + ‖v₀ - v₁‖ ≤ 2 * √2 := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    rw [hs]
    nlinarith [sq_nonneg (‖v₀ + v₁‖ - ‖v₀ - v₁‖)]
  linarith
