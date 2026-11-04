/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Lazy
public import Complexity.Foundations.Combinatorics.Expander.Perm
import Complexity.Foundations.Data.Finset.Expect

/-!
# Box products of permutation multigraphs

Two families of permutations `σ : K → Equiv.Perm V` and `τ : K' → Equiv.Perm W` give the family
`boxProdPerms σ τ : K ⊕ K' → Equiv.Perm (V × W)` that moves one coordinate at a time: `σ k` on the
first, `τ k'` on the second. Its multigraph `ofPerms (boxProdPerms σ τ)` is the box (Cartesian)
product of the multigraphs of `σ` and `τ`. Its random walk picks a coordinate, with probability
proportional to the number of its permutations, and takes a step there.

A Poincaré inequality with constant `c` for both families gives one for the product with the same
constant (`mul_expect_sq_le_boxProdPerms`). The proof splits a function of expectation zero on
`V × W` orthogonally into its averages over the fibers `{v} × W` and a part of average zero on every
fiber. The second family controls the fiber part, and the first controls the fiber averages, whose
changes along `σ` are at most the averages of the changes of the function (Jensen). This is the
two-factor case of the tensorization of the spectral gap of product chains: the gap of the product
walk is at least the smaller of the gaps of the factors, weighted by their shares of the degree
(`secondEigenvalue_ofPerms_boxProdPerms_le`). For `J` factors of equal degree and gap `γ`, iterating
gives the gap `γ / J`. This is the walk that the OpenAI preprint on derandomizing logarithmic space
applies to a uniformly selected component of its sampling environment, with gap `γ / J` for `J`
components [OpenAI, proof of Lemma 6.2][OpenAI2026LogSpace]; the statements and proofs here are
ours.

## Main definitions

* `Cslib.RotationMap.boxProdPerms`: the permutations of `V × W` that move one coordinate.

## Main results

* `Cslib.RotationMap.mul_expect_sq_le_boxProdPerms`: Poincaré inequalities for the two factors give
  one for the box product, with the same constant.
* `Cslib.RotationMap.secondEigenvalue_ofPerms_boxProdPerms_le`: the second eigenvalue of the box
  product, `λ₂ ≤ 1 - min (|K| (1 - λ₂(σ))) (|K'| (1 - λ₂(τ))) / (|K| + |K'|)`.
* `Cslib.RotationMap.spectralExpansion_lazy_ofPerms_boxProdPerms_le`: the same bound, halved, for
  the spectral expansion of the lazy box product.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V W K K' : Type*}

/-- The permutations of `V × W` that move one coordinate: `σ k` on the first, `τ k'` on the second.
Their multigraph is the box product of the multigraphs of `σ` and `τ`. -/
@[expose]
def boxProdPerms (σ : K → Equiv.Perm V) (τ : K' → Equiv.Perm W) : K ⊕ K' → Equiv.Perm (V × W) :=
  Sum.elim (fun k ↦ (σ k).prodCongr (Equiv.refl W)) fun k ↦ (Equiv.refl V).prodCongr (τ k)

variable (σ : K → Equiv.Perm V) (τ : K' → Equiv.Perm W)

@[simp]
theorem boxProdPerms_inl (k : K) (p : V × W) : boxProdPerms σ τ (.inl k) p = (σ k p.1, p.2) := rfl

@[simp]
theorem boxProdPerms_inr (k : K') (p : V × W) : boxProdPerms σ τ (.inr k) p = (p.1, τ k p.2) := rfl

variable [Fintype V] [Fintype W] [Fintype K] [Fintype K']

variable {σ τ} in
/-- **Poincaré inequalities tensorize**: if both families satisfy the Poincaré
inequality `c 𝔼 f² ≤ ∑ k, 𝔼 v, (f (σ k v) - f v) ^ 2` for every function `f` of expectation zero,
then so does their box product, with the same constant. -/
theorem mul_expect_sq_le_boxProdPerms {c : ℝ}
    (hσ : ∀ f : V → ℝ, 𝔼 v, f v = 0 → c * 𝔼 v, f v ^ 2 ≤ ∑ k, 𝔼 v, (f (σ k v) - f v) ^ 2)
    (hτ : ∀ g : W → ℝ, 𝔼 w, g w = 0 → c * 𝔼 w, g w ^ 2 ≤ ∑ k, 𝔼 w, (g (τ k w) - g w) ^ 2)
    (f : V × W → ℝ) (hf : 𝔼 p, f p = 0) :
    c * 𝔼 p, f p ^ 2 ≤ ∑ k, 𝔼 p, (f (boxProdPerms σ τ k p) - f p) ^ 2 := by
  rcases isEmpty_or_nonempty W with hW | hW
  · simp
  -- The fiber averages `g` and the decomposition `𝔼 f² = 𝔼 g² + 𝔼 (f - g)²`.
  set g : V → ℝ := fun v ↦ 𝔼 w, f (v, w) with hg
  have hsplit : 𝔼 p, f p ^ 2 = 𝔼 v, g v ^ 2 + 𝔼 v, 𝔼 w, (f (v, w) - g v) ^ 2 := by
    have h := Fintype.expect_add_sq_of_expect_fiber_eq_zero g
      (g := fun p ↦ f p - g p.1) (Fintype.expect_sub_expect_fiber f)
    simpa only [add_sub_cancel, Fintype.expect_prod_type, Fintype.expect_const] using h
  -- The second family controls the parts of average zero on the fibers.
  have hfib (v : V) :
      c * 𝔼 w, (f (v, w) - g v) ^ 2 ≤ ∑ k, 𝔼 w, (f (v, τ k w) - f (v, w)) ^ 2 := by
    have := hτ (fun w ↦ f (v, w) - g v) (Fintype.expect_sub_expect_fiber f v)
    simpa only [sub_sub_sub_cancel_right] using this
  -- The first family controls the fiber averages, by Jensen's inequality.
  have hg0 : 𝔼 v, g v = 0 := by rw [← Fintype.expect_prod_type]; exact hf
  have hjensen (k : K) (v : V) : (g (σ k v) - g v) ^ 2 ≤ 𝔼 w, (f (σ k v, w) - f (v, w)) ^ 2 := by
    simpa only [hg, expect_sub_distrib] using
      sq_expect_le_expect_sq univ fun w ↦ f (σ k v, w) - f (v, w)
  calc c * 𝔼 p, f p ^ 2
      = c * 𝔼 v, g v ^ 2 + 𝔼 v, c * 𝔼 w, (f (v, w) - g v) ^ 2 := by
        rw [hsplit, mul_add, mul_expect _ fun v ↦ 𝔼 w, (f (v, w) - g v) ^ 2]
    _ ≤ ∑ k, 𝔼 v, (g (σ k v) - g v) ^ 2 + 𝔼 v, ∑ k, 𝔼 w, (f (v, τ k w) - f (v, w)) ^ 2 :=
        add_le_add (hσ g hg0) (expect_le_expect fun v _ ↦ hfib v)
    _ ≤ ∑ k, 𝔼 v, 𝔼 w, (f (σ k v, w) - f (v, w)) ^ 2 +
          𝔼 v, ∑ k, 𝔼 w, (f (v, τ k w) - f (v, w)) ^ 2 := by
        gcongr with k _ v
        exact hjensen k v
    _ = ∑ k, 𝔼 p, (f (boxProdPerms σ τ k p) - f p) ^ 2 := by
        rw [Fintype.sum_sum_type, expect_sum_comm]
        simp only [boxProdPerms_inl, boxProdPerms_inr, Fintype.expect_prod_type]

/-- A bound on the second eigenvalue of a permutation multigraph gives a Poincaré inequality for
its permutations, with constant `2 |K| (1 - λ₂)`. -/
private theorem mul_expect_sq_le_of_secondEigenvalue [Nonempty K] (σ : K → Equiv.Perm V)
    (f : V → ℝ) (hf : 𝔼 v, f v = 0) :
    2 * Fintype.card K * (1 - (ofPerms σ).secondEigenvalue) * 𝔼 v, f v ^ 2 ≤
      ∑ k, 𝔼 v, (f (σ k v) - f v) ^ 2 := by
  have hK : (0 : ℝ) < 2 * Fintype.card K := by
    have := Fintype.card_pos (α := K)
    positivity
  have h := (ofPerms σ).expect_mul_walk_le_secondEigenvalue_mul hf
  rw [expect_mul_walk_ofPerms] at h
  have := mul_le_mul_of_nonneg_left h hK.le
  rw [mul_sub, mul_div_cancel₀ _ hK.ne'] at this
  linarith

/-- **The spectral gap of a box product**: the second eigenvalue of the box product of two
permutation multigraphs is at most
`1 - min (|K| (1 - λ₂(σ))) (|K'| (1 - λ₂(τ))) / (|K| + |K'|)`. For factors with the same number of
permutations, the gap is at least half the smaller gap of the factors. -/
theorem secondEigenvalue_ofPerms_boxProdPerms_le [Nonempty K] [Nonempty K'] :
    (ofPerms (boxProdPerms σ τ)).secondEigenvalue ≤
      1 - min (Fintype.card K * (1 - (ofPerms σ).secondEigenvalue))
        (Fintype.card K' * (1 - (ofPerms τ).secondEigenvalue)) /
        (Fintype.card K + Fintype.card K') := by
  set a : ℝ := Fintype.card K * (1 - (ofPerms σ).secondEigenvalue)
  set b : ℝ := Fintype.card K' * (1 - (ofPerms τ).secondEigenvalue)
  have hKK : (0 : ℝ) < Fintype.card K + Fintype.card K' := by
    have := Fintype.card_pos (α := K)
    positivity
  rcases subsingleton_or_nontrivial (V × W) with hV | hV
  · -- On at most one vertex `λ₂ = 0`, and the bound is nonnegative as `λ₂ ≥ -1` for the factors.
    rw [secondEigenvalue_eq_zero_of_subsingleton, sub_nonneg, div_le_one hKK]
    have ha2 : a ≤ 2 * Fintype.card K := by
      have := (ofPerms σ).neg_one_le_secondEigenvalue
      have : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
      simp only [a]
      nlinarith
    have hb2 : b ≤ 2 * Fintype.card K' := by
      have := (ofPerms τ).neg_one_le_secondEigenvalue
      have : (0 : ℝ) ≤ Fintype.card K' := Nat.cast_nonneg _
      simp only [b]
      nlinarith
    linarith [min_le_left a b, min_le_right a b]
  have h := secondEigenvalue_ofPerms_le (boxProdPerms σ τ) (c := 2 * min a b) fun f hf ↦
    mul_expect_sq_le_boxProdPerms
      (fun g hg ↦ (mul_le_mul_of_nonneg_right (by linarith [min_le_left a b])
        (expect_nonneg fun _ _ ↦ sq_nonneg _)).trans (mul_expect_sq_le_of_secondEigenvalue σ g hg))
      (fun g hg ↦ (mul_le_mul_of_nonneg_right (by linarith [min_le_right a b])
        (expect_nonneg fun _ _ ↦ sq_nonneg _)).trans (mul_expect_sq_le_of_secondEigenvalue τ g hg))
      f hf
  refine h.trans_eq ?_
  rw [Fintype.card_sum, Nat.cast_add, mul_div_mul_left _ _ two_ne_zero]

/-- **The lazy box product is an expander** when both factors are: its spectral expansion is at most
`1 - min (|K| (1 - λ₂(σ))) (|K'| (1 - λ₂(τ))) / (2 (|K| + |K'|))`. -/
theorem spectralExpansion_lazy_ofPerms_boxProdPerms_le [Nonempty K] [Nonempty K'] :
    (ofPerms (boxProdPerms σ τ)).lazy.spectralExpansion ≤
      1 - min (Fintype.card K * (1 - (ofPerms σ).secondEigenvalue))
        (Fintype.card K' * (1 - (ofPerms τ).secondEigenvalue)) /
        (2 * (Fintype.card K + Fintype.card K')) := by
  have h₁ := (ofPerms (boxProdPerms σ τ)).spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two
  have h₂ := secondEigenvalue_ofPerms_boxProdPerms_le σ τ
  rw [div_mul_eq_div_div_swap]
  linarith

end Cslib.RotationMap
