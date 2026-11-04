/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric.Slices
public import Complexity.Foundations.Combinatorics.Expander.FourthMoment
import Complexity.Foundations.Data.Finset.Expect

/-!
# Integrating actual endpoint-dependent conditional walks

Each retained source/endpoint pair has its own actual environment subtype and rotation map.
A sample is restricted to that subtype before averaging. The graph fourth-moment theorem
therefore supplies the conditional contraction, rather than taking an output-moment estimate
as a hypothesis. Integration retains the exact joint retention densities, including empty
slices. Uniform spectral bounds introduce no reciprocal-density penalty.

This is the graph-to-integrated-norm step in [OpenAI2026LogSpace, Lemma 7.8, printed p. 42],
source label `est-prefix-noise`, revision `7ef5c0cc` (23 September 2026, not peer reviewed).
The source uses eighth moments; here the existing graph theorem supplies fourth moments.
The actual task graphs and the requirement that they vary every sample-dependent coordinate
remain model obligations. This does not construct the recursive estimator or its schedules.

## Main results

* `Cslib.expect_conditionalWalk_sub_mean_pow_four_le`: actual conditional graph contraction.
* `Cslib.rowNormPow_conditionalWalk_le_sum`: nonuniform gaps retain exact densities.
* `Cslib.rowNormPow_conditionalWalk_le_raw`: uniform contraction from raw input moments.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 7.8, printed p. 42, proof of `est-prefix-noise`, revision `7ef5c0cc`
  (preprint, not peer reviewed).
-/

public section

namespace Cslib

open Finset
open scoped BigOperators

variable {Ω V D : Type*} [Fintype Ω]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]

/-- The actual retained source/endpoint environment, possibly empty. -/
abbrev RetainedPairSlice (x y : V) := ↥({σ | X σ x ∧ Y σ y} : Finset Ω)

/-- Uniform mean on the actual retained-pair slice, with zero mean on an empty slice. -/
@[expose] noncomputable def rowSliceMean (F : Ω → V → V → ℝ) (x y : V) : ℝ :=
  𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), F σ x y

open Classical in
/-- A concrete family of graph averages on each actual retained-pair slice. Values outside
that pair's retention event are zero and are ignored by the integrated row norm. -/
@[expose] noncomputable def conditionalWalk [Fintype D]
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D) (t : V → V → ℕ)
    (F : Ω → V → V → ℝ) (σ : Ω) (x y : V) : ℝ :=
  if h : σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω) then
    ((G x y).walk ^ (2 * t x y)) (fun τ => F τ.val x y) ⟨σ, h⟩ else 0

/-- A retained environment is evaluated by its own pair's graph, without changing slices. -/
theorem conditionalWalk_coe [Fintype D]
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D) (t : V → V → ℕ)
    (F : Ω → V → V → ℝ) (x y : V) (σ : RetainedPairSlice X Y x y) :
    conditionalWalk X Y G t F σ.val x y =
      ((G x y).walk ^ (2 * t x y)) (fun τ => F τ.val x y) σ := by
  simp only [conditionalWalk, dite_eq_left σ.property, Subtype.coe_eta]

/-- The graph's uniform vertex average is precisely the conditional finite-set average. -/
theorem expect_retainedPairSlice (x y : V) (f : Ω → ℝ) :
    (𝔼 σ : RetainedPairSlice X Y x y, f σ.val) =
      𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), f σ := by
  simp only [expect_eq_sum_div_card, card_univ, Fintype.card_coe, sum_coe_sort]

/-- The existing graph theorem supplies the actual conditional fourth-moment contraction.
No positivity or nonemptiness assumption on the retained slice is required. -/
theorem expect_conditionalWalk_sub_mean_pow_four_le [Fintype D] [Nonempty D]
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D) (t : V → V → ℕ)
    (F : Ω → V → V → ℝ) (x y : V) :
    (𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω),
      |conditionalWalk X Y G t F σ x y - rowSliceMean X Y F x y| ^ 4) ≤
      2 * (G x y).spectralExpansion ^ (2 * t x y) *
        𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω),
          |F σ x y - rowSliceMean X Y F x y| ^ 4 := by
  have hmean := expect_retainedPairSlice X Y x y (fun σ => F σ x y)
  have h := (G x y).expect_walk_pow_two_mul_sub_expect_pow_four_le
    (fun σ => F σ.val x y) (t x y)
  have habs (r : ℝ) : |r| ^ 4 = r ^ 4 := (by decide : Even (4 : ℕ)).pow_abs r
  rw [← expect_retainedPairSlice X Y x y, ← expect_retainedPairSlice X Y x y]
  simp only [habs, conditionalWalk_coe]
  simpa only [hmean, rowSliceMean] using h

variable [Fintype V]

/-- Nonuniform pair-specific graph gaps and walk lengths retain the exact slice densities. -/
theorem rowNormPow_conditionalWalk_le_sum [Fintype D] [Nonempty D] {N u : ℝ}
    (hNu : 0 ≤ N * u) (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D)
    (t : V → V → ℕ) (F : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y =>
      conditionalWalk X Y G t F σ x y - rowSliceMean X Y F x y) ≤
      (N * u)⁻¹ * ∑ x, ∑ y,
        (({σ | X σ x ∧ Y σ y} : Finset Ω).dens : ℝ) *
          (2 * (G x y).spectralExpansion ^ (2 * t x y) *
            𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω),
              |F σ x y - rowSliceMean X Y F x y| ^ 4) :=
  rowNormPow_le_sum_conditional_budgets hNu _ _
    (expect_conditionalWalk_sub_mean_pow_four_le X Y G t F)

/-- A uniform spectral bound contracts the centered integrated row moment directly, even
when the pair slices have unequal densities or are empty. -/
theorem rowNormPow_conditionalWalk_le [Fintype D] [Nonempty D] {N u lam : ℝ}
    (hNu : 0 ≤ N * u) (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D)
    (hgap : ∀ x y, (G x y).spectralExpansion ≤ lam) (t : ℕ) (F : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y =>
      conditionalWalk X Y G (fun _ _ => t) F σ x y - rowSliceMean X Y F x y) ≤
      2 * lam ^ (2 * t) * rowNormPow 4 N u X Y
        (fun σ x y => F σ x y - rowSliceMean X Y F x y) := by
  apply rowNormPow_le_of_conditional_expect_le hNu
  intro x y
  refine (expect_conditionalWalk_sub_mean_pow_four_le X Y G (fun _ _ => t) F x y).trans ?_
  apply mul_le_mul_of_nonneg_right _ (expect_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (G x y).spectralExpansion_nonneg
    (hgap x y) _) (by norm_num)

private theorem expect_sub_expect_pow_four_le_raw {A : Type*} [Fintype A] (f : A → ℝ) :
    (𝔼 σ, |f σ - 𝔼 τ, f τ| ^ 4) ≤ 16 * 𝔼 σ, |f σ| ^ 4 := by
  rcases isEmpty_or_nonempty A with hA | hA
  · simp
  have habs (r : ℝ) : |r| ^ 4 = r ^ 4 := (by decide : Even (4 : ℕ)).pow_abs r
  have hfirst := sq_expect_le_expect_sq (univ : Finset A) f
  have hsecond := sq_expect_le_expect_sq (univ : Finset A) (fun σ => f σ ^ 2)
  have hpow := pow_le_pow_left₀ (sq_nonneg (𝔼 σ, f σ)) hfirst 2
  have hmean : |𝔼 σ, f σ| ^ 4 ≤ 𝔼 σ, |f σ| ^ 4 := by
    simpa only [habs, ← pow_mul, Nat.reduceMul] using hpow.trans hsecond
  have hpoint (σ : A) : |f σ - 𝔼 τ, f τ| ^ 4 ≤
      8 * (|f σ| ^ 4 + |𝔼 τ, f τ| ^ 4) := by
    have ht := pow_le_pow_left₀ (abs_nonneg (f σ - 𝔼 τ, f τ)) (abs_sub (f σ) (𝔼 τ, f τ)) 4
    have ha := add_pow_le (abs_nonneg (f σ)) (abs_nonneg (𝔼 τ, f τ)) 4
    norm_num only [Nat.reduceSub, Nat.reducePow] at ha
    exact ht.trans ha
  have h : (𝔼 σ, |f σ - 𝔼 τ, f τ| ^ 4) ≤
      𝔼 σ, 8 * (|f σ| ^ 4 + |𝔼 τ, f τ| ^ 4) := expect_le_expect fun σ _ => hpoint σ
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const] at h
  linarith

/-- The graph family also contracts from the uncentered raw integrated input moment, at the
fixed cost 32. The cost is independent of every slice density and input moment. -/
theorem rowNormPow_conditionalWalk_le_raw [Fintype D] [Nonempty D] {N u lam : ℝ}
    (hNu : 0 ≤ N * u) (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D)
    (hgap : ∀ x y, (G x y).spectralExpansion ≤ lam) (t : ℕ) (F : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y =>
      conditionalWalk X Y G (fun _ _ => t) F σ x y - rowSliceMean X Y F x y) ≤
      32 * lam ^ (2 * t) * rowNormPow 4 N u X Y F := by
  apply rowNormPow_le_of_conditional_expect_le hNu
  intro x y
  have hlocal := expect_conditionalWalk_sub_mean_pow_four_le X Y G (fun _ _ => t) F x y
  have hraw := expect_sub_expect_pow_four_le_raw (fun σ : RetainedPairSlice X Y x y => F σ.val x y)
  have hmean := expect_retainedPairSlice X Y x y (fun σ => F σ x y)
  simp only [hmean] at hraw
  rw [expect_retainedPairSlice X Y x y (fun σ =>
      |F σ x y - 𝔼 τ ∈ ({τ | X τ x ∧ Y τ y} : Finset Ω), F τ x y| ^ 4),
    expect_retainedPairSlice X Y x y (fun σ => |F σ x y| ^ 4)] at hraw
  have hpow := pow_le_pow_left₀ (G x y).spectralExpansion_nonneg (hgap x y) (2 * t)
  have hmoment : 0 ≤ 𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), |F σ x y| ^ 4 := by
    positivity
  have hscale := mul_le_mul_of_nonneg_left hraw
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg (G x y).spectralExpansion_nonneg (2 * t)))
  have hgapscale := mul_le_mul_of_nonneg_right hpow hmoment
  dsimp only [rowSliceMean] at hlocal ⊢
  nlinarith

end Cslib
