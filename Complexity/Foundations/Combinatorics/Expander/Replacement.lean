/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Power
public import Complexity.Foundations.Combinatorics.Expander.Zigzag
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Real.Sqrt

/-!
# The balanced replacement product of rotation maps

The **balanced replacement product** `G.balancedReplacement H` of a `D`-regular graph `G` on `V`
with a graph `H` on the labels `D` of `G` is a graph on `V × D` with twice the degree of `H`
[Reingold, Vadhan and Wigderson, Section 6.2][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]. Its walk operator is `(B̃ + Ã) / 2`, where
`B̃ = I ⊗ W_H` is the walk on the copies `{v} × D` of `H` and `Ã` permutes the vertices by the
rotation map of `G`. Since the zig-zag walk `B̃ Ã B̃` is one of the eight terms of its cube,
`λ(G Ⓡ H) ^ 3 ≤ 7 / 8 + λ(G ⓩ H) / 8`, so that `λ(G Ⓡ H) ≤ 1 - (1 - λ(G)) (1 - λ(H)) ^ 2 / 24`
[Reingold, Vadhan and Wigderson, Theorem 6.7][ReingoldVadhanWigderson2002].

## Main definitions

* `Cslib.RotationMap.balancedReplacement`: the balanced replacement product `G Ⓡ H`.

## Main results

* `Cslib.RotationMap.walk_balancedReplacement`: the walk operator of `G Ⓡ H` is `(B̃ + Ã) / 2`.
* `Cslib.RotationMap.spectralExpansion_balancedReplacement_pow_three_le`,
  `Cslib.RotationMap.spectralExpansion_balancedReplacement_le`,
  `Cslib.RotationMap.spectralExpansion_balancedReplacement_lt_one`: the balanced replacement
  product of two expanders is an expander.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open Fintype (expect_sq_le_of_expect_mul_le)
open Real (expect_mul_le_sqrt_mul_sqrt)
open scoped BigOperators

variable {V D E : Type*} (G : RotationMap V D) (H : RotationMap D E)

/-- The **balanced replacement product** of a `D`-regular graph `G` on `V` with a graph `H` on the
labels `D` of `G` [Reingold, Vadhan and Wigderson, Definition 6.6][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]. Every vertex `v` of `G` is replaced by the copy
`{v} × D` of `H`. At `(v, k)`, the edge `Sum.inl i` is the edge `i` of `H` at `k` inside the copy,
and the edges `Sum.inr i`, one for every label `i` of `H`, all cross the `k`-th edge of `G` at `v`,
to `G.rot (v, k)`. So a step of the random walk takes a step in `H` or crosses an edge of `G` with
probability `1 / 2` each. -/
def balancedReplacement : RotationMap (V × D) (E ⊕ E) where
  rot
    | (p, .inl i) => ((p.1, (H.rot (p.2, i)).1), .inl (H.rot (p.2, i)).2)
    | (p, .inr i) => (G.rot p, .inr i)
  rot_involutive
    | (_, .inl _) => by simp
    | (_, .inr _) => by simp

/-- The edges `Sum.inl i` of the balanced replacement product are those of `H`. -/
@[simp]
theorem rot_balancedReplacement_inl (p : V × D) (i : E) :
    (G.balancedReplacement H).rot (p, .inl i) =
      ((p.1, (H.rot (p.2, i)).1), .inl (H.rot (p.2, i)).2) :=
  rfl

/-- The edges `Sum.inr i` of the balanced replacement product are those of `G`. -/
@[simp]
theorem rot_balancedReplacement_inr (p : V × D) (i : E) :
    (G.balancedReplacement H).rot (p, .inr i) = (G.rot p, .inr i) :=
  rfl

variable [Fintype E]

/-- When `H` has edges, the walk operator of the balanced replacement product is `(B̃ + Ã) / 2`
[Reingold, Vadhan and Wigderson, Theorem 6.7][ReingoldVadhanWigderson2002], where `B̃ = I ⊗ W_H` is
the walk operator of `H` on every copy and `Ã` permutes the vertices `V × D` by the rotation map of
`G`. -/
theorem walk_balancedReplacement [Nonempty E] :
    (G.balancedReplacement H).walk =
      (2⁻¹ : ℝ) • (((loops V Unit).tensor H).walk + LinearMap.funLeft ℝ ℝ G.rot) :=
  LinearMap.ext fun f ↦ funext fun p ↦ by
    have hE : (Fintype.card E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [LinearMap.smul_apply, LinearMap.add_apply, walk_apply, Fintype.expect_eq_sum_div_card,
      Fintype.sum_sum_type, Fintype.card_sum, Pi.smul_apply, Pi.add_apply, walk_loops_tensor_apply,
      walk_apply, Fintype.expect_eq_sum_div_card, LinearMap.funLeft_apply]
    simp only [neighbor, rot_balancedReplacement_inl, rot_balancedReplacement_inr, sum_const,
      card_univ, nsmul_eq_mul, Nat.cast_add, smul_eq_mul]
    field_simp
    ring

variable [Fintype V] [Fintype D]

/-- Each 3-step word in operators on `V × D → ℝ` that do not increase the second moment has
bilinear form bounded by `√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)`. -/
private theorem expect_mul_three_word_le (h f : V × D → ℝ)
    {T₁ T₂ T₃ : Module.End ℝ (V × D → ℝ)}
    (h₁ : ∀ g, 𝔼 p, T₁ g p ^ 2 ≤ 𝔼 p, g p ^ 2)
    (h₂ : ∀ g, 𝔼 p, T₂ g p ^ 2 ≤ 𝔼 p, g p ^ 2)
    (h₃ : ∀ g, 𝔼 p, T₃ g p ^ 2 ≤ 𝔼 p, g p ^ 2) :
    𝔼 p, h p * (T₁ * T₂ * T₃) f p ≤ √(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2) :=
  (expect_mul_le_sqrt_mul_sqrt univ _ _).trans <|
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ((h₁ _).trans ((h₂ _).trans (h₃ f))))
      (Real.sqrt_nonneg _)

/-- The cube of the walk operator of the balanced replacement product, in bilinear form. -/
private theorem expect_mul_walk_balancedReplacement_pow_three_le [Nonempty E] (h : V × D → ℝ)
    {f : V × D → ℝ} (hf : 𝔼 p, f p = 0) :
    𝔼 p, h p * ((G.balancedReplacement H).pow 3).walk f p ≤
      (7 / 8 + (G.zigzag H).spectralExpansion / 8) * (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := by
  -- `B̃` and `Ã` do not increase the second moment
  have hB (g : V × D → ℝ) : 𝔼 p, ((loops V Unit).tensor H).walk g p ^ 2 ≤ 𝔼 p, g p ^ 2 :=
    ((loops V Unit).tensor H).expect_walk_sq_le g
  have hA (g : V × D → ℝ) : 𝔼 p, LinearMap.funLeft ℝ ℝ G.rot g p ^ 2 ≤ 𝔼 p, g p ^ 2 :=
    (expect_comp_rot G fun p ↦ g p ^ 2).le
  -- the cube contains the zig-zag walk `B̃ Ã B̃` once
  have hZ : 𝔼 p, h p * (G.zigzag H).walk f p ≤
      (G.zigzag H).spectralExpansion * (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := by
    refine (expect_mul_le_sqrt_mul_sqrt univ _ _).trans ?_
    rw [mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq (spectralExpansion_nonneg _), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt ((G.zigzag H).expect_walk_sq_le_spectralExpansion_sq_mul hf)
  set B := ((loops V Unit).tensor H).walk
  set A : Module.End ℝ (V × D → ℝ) := LinearMap.funLeft ℝ ℝ G.rot
  rw [walk_zigzag, ← LinearMap.comp_assoc] at hZ
  have hexp : (B + A) ^ 3 = B * B * B + B * B * A + B * A * B + B * A * A + A * B * B +
      A * B * A + A * A * B + A * A * A := by
    noncomm_ring
  rw [walk_pow, walk_balancedReplacement, smul_pow, hexp]
  calc
    _ = (2⁻¹ : ℝ) ^ 3 * (𝔼 p, h p * (B * B * B) f p + 𝔼 p, h p * (B * B * A) f p +
          𝔼 p, h p * (B * A * B) f p + 𝔼 p, h p * (B * A * A) f p +
          𝔼 p, h p * (A * B * B) f p + 𝔼 p, h p * (A * B * A) f p +
          𝔼 p, h p * (A * A * B) f p + 𝔼 p, h p * (A * A * A) f p) := by
      simp only [LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul, ← expect_add_distrib, mul_expect]
      exact expect_congr rfl fun p _ ↦ by ring
    _ ≤ _ := by
      have h₁ := expect_mul_three_word_le h f hB hB hB
      have h₂ := expect_mul_three_word_le h f hB hB hA
      have h₄ := expect_mul_three_word_le h f hB hA hA
      have h₅ := expect_mul_three_word_le h f hA hB hB
      have h₆ := expect_mul_three_word_le h f hA hB hA
      have h₇ := expect_mul_three_word_le h f hA hA hB
      have h₈ := expect_mul_three_word_le h f hA hA hA
      have h₃ : 𝔼 p, h p * (B * A * B) f p ≤
          (G.zigzag H).spectralExpansion * (√(𝔼 p, h p ^ 2) * √(𝔼 p, f p ^ 2)) := hZ
      rw [show (2⁻¹ : ℝ) ^ 3 = 8⁻¹ by norm_num]
      linarith

/-- The cube of the spectral expansion of the balanced replacement product is at most
`7 / 8 + λ(G ⓩ H) / 8` [Reingold, Vadhan and Wigderson, Theorem 6.7][ReingoldVadhanWigderson2002]:
the zig-zag walk is one of the eight terms of the cube of its walk operator. -/
theorem spectralExpansion_balancedReplacement_pow_three_le :
    (G.balancedReplacement H).spectralExpansion ^ 3 ≤
      7 / 8 + (G.zigzag H).spectralExpansion / 8 := by
  rw [← spectralExpansion_pow _ three_ne_zero]
  have hZ := (G.zigzag H).spectralExpansion_nonneg
  refine spectralExpansion_le (by positivity) fun f hf ↦ ?_
  rcases isEmpty_or_nonempty E with hE | hE
  · have : (G.balancedReplacement H).walk = 0 :=
      LinearMap.ext fun f ↦ funext fun p ↦ by simp [walk_apply]
    rw [walk_pow, this, zero_pow three_ne_zero]
    simpa using mul_nonneg (sq_nonneg (7 / 8 + (G.zigzag H).spectralExpansion / 8))
      (expect_nonneg fun p _ ↦ sq_nonneg (f p))
  rcases isEmpty_or_nonempty D with hD | hD
  · simp
  exact expect_sq_le_of_expect_mul_le (G.expect_mul_walk_balancedReplacement_pow_three_le H _ hf)

/-- The spectral expansion of the balanced replacement product is at most
`1 - (1 - λ(G)) (1 - λ(H)) ^ 2 / 24`: the balanced replacement product of two expanders is an
expander. -/
theorem spectralExpansion_balancedReplacement_le :
    (G.balancedReplacement H).spectralExpansion ≤
      1 - (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2 / 24 := by
  have hμ := G.spectralExpansion_nonneg
  have hν := H.spectralExpansion_nonneg
  have hμ₁ := G.spectralExpansion_le_one
  have hν₁ := H.spectralExpansion_le_one
  have hZ := G.spectralExpansion_zigzag_le_one_sub H
  have h3 := G.spectralExpansion_balancedReplacement_pow_three_le H
  set x := (1 - G.spectralExpansion) * (1 - H.spectralExpansion) ^ 2
  have hx₀ : 0 ≤ x := mul_nonneg (by linarith) (sq_nonneg _)
  have hx₁ : x ≤ 1 :=
    (mul_le_mul (by linarith) (pow_le_one₀ (by linarith) (by linarith)) (sq_nonneg _)
      zero_le_one).trans_eq (one_mul 1)
  refine (pow_le_pow_iff_left₀ (spectralExpansion_nonneg _) (by linarith) three_ne_zero).1 ?_
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 72 - x)]

/-- The balanced replacement product of two graphs of spectral expansion less than `1` has spectral
expansion less than `1` [Reingold, Vadhan and Wigderson, Theorem 6.7][ReingoldVadhanWigderson2002].
-/
theorem spectralExpansion_balancedReplacement_lt_one (hG : G.spectralExpansion < 1)
    (hH : H.spectralExpansion < 1) : (G.balancedReplacement H).spectralExpansion < 1 := by
  refine (G.spectralExpansion_balancedReplacement_le H).trans_lt (sub_lt_self 1 ?_)
  have := mul_pos (sub_pos.2 hG) (pow_pos (sub_pos.2 hH) 2)
  positivity

end Cslib.RotationMap
