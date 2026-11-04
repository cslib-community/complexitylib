/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.FourthMoment
public import Complexity.Probability.PairwiseIndependentHash.ComponentGap

/-!
# Fourth-moment conditional averaging on retention slices

The conditional averaging walks of the sampler contract fourth moments as well as second moments.
On the retention slice of an identifier `y`, and on a product of retention slices of `J` channels
together with free bits, `2 t` steps of the lazy affine walk multiply the fourth central moment of
every function by at most

`2 (1 - 1 / (155648 H ^ 4)) ^ (2 t)`, respectively `2 (1 - 1 / (155648 (J + 1) H ^ 4)) ^ (2 t)`,

uniformly in the primes, the sides, the identifiers and the torus modulus
(`expect_walk_pow_sliceGraph_affineMove_sub_expect_pow_four_le`,
`expect_walk_pow_componentMove_sub_expect_pow_four_le`). This combines the fourth-moment decay of
a walk from its spectral gap (`RotationMap.expect_walk_pow_two_mul_sub_expect_pow_four_le`) with
the uniform gaps of the affine walks (`spectralExpansion_lazy_ofPerms_affineMove_le`,
`spectralExpansion_lazy_ofPerms_componentMove_le`).

This is the case `s = 4` of the `L^s` bound `‖K^d − Π‖_{s→s} ≤ C_s 2^{−c_s d}` of Lemma 6.2 of
the OpenAI preprint on derandomizing logarithmic space [OpenAI2026LogSpace], for centered inputs.
The preprint interpolates between `L²` and `L^∞` (Riesz–Thorin); the decay here comes from the
`L²` gap by an elementary argument, with the constant `2` and the rate `λ ^ (2 t)` over `2 t`
steps.

## Main results

* `Cslib.Probability.expect_walk_pow_sliceGraph_affineMove_sub_expect_pow_four_le`: on one
  retention slice.
* `Cslib.Probability.expect_walk_pow_componentMove_sub_expect_pow_four_le`: on a product of
  retention slices with free bits.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

namespace Cslib.Probability

open Finset RotationMap
open scoped BigOperators

variable {P H L M J : ℕ}

/-- A fourth-moment bound `2 λ ^ (2 t)` from a spectral-expansion bound `λ ≤ lam`. -/
private theorem two_mul_pow_le {V D : Type*} [Fintype V] [Fintype D]
    (G : RotationMap V D) {lam : ℝ} (hG : G.spectralExpansion ≤ lam) (t : ℕ) (X : ℝ)
    (hX : 0 ≤ X) : 2 * G.spectralExpansion ^ (2 * t) * X ≤ 2 * lam ^ (2 * t) * X := by
  gcongr
  exact G.spectralExpansion_nonneg

/-- **Fourth-moment conditional averaging on a retention slice**: on the retention slice of every
identifier `y`, `2 t` steps of the lazy affine walk multiply the fourth central moment of every
function by at most `2 (1 - 1 / (155648 H ^ 4)) ^ (2 t)`, for a prime `P`, `H ≥ 3` and
`1 ≤ L ≤ P`, uniformly in `P`, `L` and `y`. -/
theorem expect_walk_pow_sliceGraph_affineMove_sub_expect_pow_four_le [Fact P.Prime] [NeZero L]
    (hH : 3 ≤ H) (hL : L ≤ P) (y : ZMod P) (f : RetentionSlice P H 1 L y → ℝ) (t : ℕ) :
    𝔼 A, (((sliceGraph L hL y (ofPerms (affineMove P H L 1)).lazy).walk ^ (2 * t)) f A -
        𝔼 B, f B) ^ 4 ≤
      2 * (1 - 1 / (155648 * H ^ 4)) ^ (2 * t) * 𝔼 A, (f A - 𝔼 B, f B) ^ 4 := by
  have : Nonempty ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) := ⟨.inr ⟨0, by omega⟩⟩
  refine ((sliceGraph L hL y _).expect_walk_pow_two_mul_sub_expect_pow_four_le f t).trans ?_
  refine two_mul_pow_le _ ?_ t _ (expect_nonneg fun _ _ ↦ by positivity)
  rw [spectralExpansion_sliceGraph]
  exact spectralExpansion_lazy_ofPerms_affineMove_le hH

/-- **Fourth-moment conditional averaging over channels and free bits**: on the product of the
retention slices of identifiers `y j` of `J` channels with free bits in `ZMod M ^ H`, `2 t` steps
of the lazy product walk multiply the fourth central moment of every function by at most
`2 (1 - 1 / (155648 (J + 1) H ^ 4)) ^ (2 t)`, for `H ≥ 3`, uniformly in the primes, the sides, the
identifiers and the torus modulus. -/
theorem expect_walk_pow_componentMove_sub_expect_pow_four_le {P L : Fin J → ℕ}
    [∀ j, Fact (P j).Prime] [∀ j, NeZero (L j)] [NeZero M] (hH : 3 ≤ H) (hL : ∀ j, L j ≤ P j)
    (y : ∀ j, ZMod (P j))
    (f : (∀ j, RetentionSlice (P j) H 1 (L j) (y j)) × (Fin H → ZMod M) → ℝ) (t : ℕ) :
    𝔼 A, ((((ofPerms (componentMove H M P L)).lazy.reindex
        (componentEquiv M hL y).symm).walk ^ (2 * t)) f A - 𝔼 B, f B) ^ 4 ≤
      2 * (1 - 1 / (155648 * (J + 1) * H ^ 4)) ^ (2 * t) * 𝔼 A, (f A - 𝔼 B, f B) ^ 4 := by
  have : Nonempty ((Σ _ : Fin J, {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) ⊕
      ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H)) := ⟨.inr (.inr ⟨0, by omega⟩)⟩
  refine (RotationMap.expect_walk_pow_two_mul_sub_expect_pow_four_le _ f t).trans ?_
  refine two_mul_pow_le _ ?_ t _ (expect_nonneg fun _ _ ↦ by positivity)
  rw [spectralExpansion_reindex]
  exact spectralExpansion_lazy_ofPerms_componentMove_le hH

end Cslib.Probability
