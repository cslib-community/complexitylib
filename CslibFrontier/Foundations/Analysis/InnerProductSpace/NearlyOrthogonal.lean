/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/Basic.lean`)

public import CslibFrontier.Foundations.Analysis.InnerProductSpace.Basic

/-!
# Few nearly orthogonal vectors correlate with a fixed vector

Let `v i`, `i ∈ s`, be vectors of squared norm at most `A > 0` whose pairwise inner products are
at most `δ A`, and let `T` be a vector of squared norm at most `A` with `⟪T, v i⟫ ≥ γ A` for every
`i ∈ s`, where `γ ≥ 0`. Then `#s * γ ^ 2 ≤ 1 + (#s - 1) * δ` (`card_mul_sq_le_of_inner_ge`). The
bound is one-sided: pairs of strongly anticorrelated vectors are allowed. The proof is the
Cauchy–Schwarz inequality for `T` and the sum `U = ∑ i ∈ s, v i`: on one side
`⟪T, U⟫ ≥ #s γ A`, on the other `‖U‖ ^ 2 ≤ #s A + #s (#s - 1) δ A` by expanding the square
(`norm_sum_sq_real`). This is the geometric argument behind the binary Johnson bound
(`Cslib.Code.card_mul_sq_sub_le_of_le_sum_signVal_mul_signVal`).

If instead the pairwise inner products are at most `δ A` in absolute value and
`|⟪T, v i⟫| ≥ γ A`, the same bound follows by replacing each `v i` with `± v i`, the sign of
`⟪T, v i⟫` (`card_mul_sq_le_of_abs_inner_ge`), so `#s * (γ ^ 2 - δ) ≤ 1` when `δ ≥ 0`
(`card_mul_sub_le_one_of_abs_inner_ge`): at most `1 / (γ ^ 2 - δ)` of the vectors correlate with
`T` once `γ ^ 2 > δ`. This is a Cauchy–Schwarz form of the Gram-matrix argument of Kane and
Williams ([KaneWilliams2016], `arXiv:1511.07860v1`, Lemma 6.1), stated here with explicit
constants for vectors in any real inner product space.

## Main results

* `card_mul_sq_le_of_inner_ge`: `#s * γ ^ 2 ≤ 1 + (#s - 1) * δ`, for one-sided bounds.
* `card_mul_sq_le_of_abs_inner_ge`: the same for bounds in absolute value.
* `card_mul_sub_le_one_of_abs_inner_ge`: `#s * (γ ^ 2 - δ) ≤ 1` for `δ ≥ 0`.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016], `arXiv:1511.07860v1`,
  Lemma 6.1 (`uncorrAgreeLem`)
-/

public section

open Finset
open scoped RealInnerProductSpace

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Few nearly orthogonal vectors correlate with a fixed vector**, one-sided form: if `v i`,
`i ∈ s`, have squared norms at most `A > 0` and pairwise inner products at most `δ A`, and `T` has
squared norm at most `A` and `⟪T, v i⟫ ≥ γ A` for all `i ∈ s` with `γ ≥ 0`, then
`#s * γ ^ 2 ≤ 1 + (#s - 1) * δ`. -/
theorem card_mul_sq_le_of_inner_ge {s : Finset ι} (hs : s.Nonempty) (v : ι → V) (T : V)
    {A δ γ : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ) (hT : ‖T‖ ^ 2 ≤ A) (hv : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ A)
    (hδ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫ ≤ δ * A)
    (hTv : ∀ i ∈ s, γ * A ≤ ⟪T, v i⟫) :
    (#s : ℝ) * γ ^ 2 ≤ 1 + (#s - 1) * δ := by
  classical
  set U : V := ∑ i ∈ s, v i with hU
  -- the sum correlates with `T` by at least `#s γ A`
  have hlow : (#s : ℝ) * (γ * A) ≤ ⟪T, U⟫ := by
    rw [hU, inner_sum, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hTv
  -- and has squared norm at most `#s A + (#s ^ 2 - #s) δ A`
  have hUsq : ‖U‖ ^ 2 ≤ (#s : ℝ) * A + ((#s : ℝ) * #s - #s) * (δ * A) := by
    rw [hU, norm_sum_sq_real]
    have hdiag : ∑ i ∈ s, ‖v i‖ ^ 2 ≤ (#s : ℝ) * A := by
      calc ∑ i ∈ s, ‖v i‖ ^ 2 ≤ ∑ _i ∈ s, A := sum_le_sum hv
        _ = (#s : ℝ) * A := by rw [sum_const, nsmul_eq_mul]
    have hoff : ∑ p ∈ s.offDiag, ⟪v p.1, v p.2⟫ ≤ ((#s : ℝ) * #s - #s) * (δ * A) := by
      calc ∑ p ∈ s.offDiag, ⟪v p.1, v p.2⟫ ≤ ∑ _p ∈ s.offDiag, δ * A := by
            refine sum_le_sum fun p hp => ?_
            obtain ⟨h1, h2, hne⟩ := mem_offDiag.mp hp
            exact hδ _ h1 _ h2 hne
        _ = ((#s : ℝ) * #s - #s) * (δ * A) := by
            rw [sum_const, offDiag_card, nsmul_eq_mul, Nat.cast_sub (Nat.le_mul_self _),
              Nat.cast_mul]
    linarith
  -- Cauchy–Schwarz
  have hcs : ⟪T, U⟫ ^ 2 ≤ ‖T‖ ^ 2 * ‖U‖ ^ 2 := by
    rw [← mul_pow]
    exact sq_le_sq' (abs_le.mp (abs_real_inner_le_norm T U)).1 (real_inner_le_norm T U)
  have hcard : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have hkey : ((#s : ℝ) * (γ * A)) ^ 2 ≤ A * ((#s : ℝ) * A + ((#s : ℝ) * #s - #s) * (δ * A)) :=
    (pow_le_pow_left₀ (by positivity) hlow 2).trans
      (hcs.trans (mul_le_mul hT hUsq (sq_nonneg _) hA.le))
  have hfactor : ((#s : ℝ) * (γ * A)) ^ 2 = (#s : ℝ) * A ^ 2 * ((#s : ℝ) * γ ^ 2) := by ring
  have hfactor' : A * ((#s : ℝ) * A + ((#s : ℝ) * #s - #s) * (δ * A)) =
      (#s : ℝ) * A ^ 2 * (1 + (#s - 1) * δ) := by ring
  rw [hfactor, hfactor'] at hkey
  exact le_of_mul_le_mul_left hkey (by positivity)

/-- **Few nearly orthogonal vectors correlate with a fixed vector**: if `v i`, `i ∈ s`, have squared
norms at most `A > 0` and pairwise inner products at most `δ A` in absolute value, and `T` has
squared norm at most `A` and `|⟪T, v i⟫| ≥ γ A` for all `i ∈ s` with `γ ≥ 0`, then
`#s * γ ^ 2 ≤ 1 + (#s - 1) * δ` ([KaneWilliams2016], `arXiv:1511.07860v1`, Lemma 6.1, with
explicit constants). -/
theorem card_mul_sq_le_of_abs_inner_ge {s : Finset ι} (hs : s.Nonempty) (v : ι → V) (T : V)
    {A δ γ : ℝ} (hA : 0 < A) (hγ : 0 ≤ γ) (hT : ‖T‖ ^ 2 ≤ A) (hv : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ A)
    (hδ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → |⟪v i, v j⟫| ≤ δ * A)
    (hTv : ∀ i ∈ s, γ * A ≤ |⟪T, v i⟫|) :
    (#s : ℝ) * γ ^ 2 ≤ 1 + (#s - 1) * δ := by
  -- flip each vector to the sign of its correlation with `T`
  set ε : ι → ℝ := fun i => if 0 ≤ ⟪T, v i⟫ then 1 else -1 with hε
  have hε_abs (i : ι) : |ε i| = 1 := by
    by_cases h : 0 ≤ ⟪T, v i⟫ <;> simp [ε, h]
  have hε_mul (i : ι) : ε i * ⟪T, v i⟫ = |⟪T, v i⟫| := by
    by_cases h : 0 ≤ ⟪T, v i⟫
    · simp [ε, h, abs_of_nonneg h]
    · simp [ε, h, abs_of_neg (not_le.mp h)]
  refine card_mul_sq_le_of_inner_ge hs (fun i => ε i • v i) T hA hγ hT (fun i hi => ?_)
    (fun i hi j hj hij => ?_) (fun i hi => ?_)
  · rw [norm_smul, Real.norm_eq_abs, hε_abs, one_mul]
    exact hv i hi
  · rw [real_inner_smul_left, real_inner_smul_right]
    calc ε i * (ε j * ⟪v i, v j⟫) ≤ |ε i * (ε j * ⟪v i, v j⟫)| := le_abs_self _
      _ = |⟪v i, v j⟫| := by rw [abs_mul, abs_mul, hε_abs, hε_abs, one_mul, one_mul]
      _ ≤ δ * A := hδ i hi j hj hij
  · rw [real_inner_smul_right, hε_mul]
    exact hTv i hi

/-- **Few nearly orthogonal vectors correlate with a fixed vector**, list-size form: under the
hypotheses of `card_mul_sq_le_of_abs_inner_ge` with `δ ≥ 0` (and `s` possibly empty),
`#s * (γ ^ 2 - δ) ≤ 1`. Once `γ ^ 2 > δ`, at most `1 / (γ ^ 2 - δ)` vectors correlate with
`T`. -/
theorem card_mul_sub_le_one_of_abs_inner_ge (s : Finset ι) (v : ι → V) (T : V)
    {A δ γ : ℝ} (hA : 0 < A) (hδ0 : 0 ≤ δ) (hγ : 0 ≤ γ) (hT : ‖T‖ ^ 2 ≤ A)
    (hv : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ A) (hδ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → |⟪v i, v j⟫| ≤ δ * A)
    (hTv : ∀ i ∈ s, γ * A ≤ |⟪T, v i⟫|) :
    (#s : ℝ) * (γ ^ 2 - δ) ≤ 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have h := card_mul_sq_le_of_abs_inner_ge hs v T hA hγ hT hv hδ hTv
    nlinarith
