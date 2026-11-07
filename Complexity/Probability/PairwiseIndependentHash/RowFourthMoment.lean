/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric.ConditionalWalk
public import Complexity.Probability.PairwiseIndependentHash.ComponentGap

/-!
# Actual retained-pair component walks in the integrated row norm

The actual environment slice for each retained pair may have its own representation as a
product of retention slices and free coordinates. If its walk is the transported concrete
component walk, the uniform component gap contracts the global raw fourth moment with the
actual pair densities. Empty slices require no representation or walk-model equality.

The equivalences and operator identities are explicit model obligations: in particular, they
must include every coordinate on which the sample depends. This is a fourth-moment version of
the graph-to-global calculation in [OpenAI2026LogSpace, Lemma 7.8, printed p. 42], revision
`7ef5c0cc` (23 September 2026, not peer reviewed), not the recursive estimator theorem.

## Main results

* `Cslib.Probability.rowNormPow_conditionalWalk_component_le`: integrated component-walk bound.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 7.8, printed p. 42, revision `7ef5c0cc` (preprint, not peer reviewed).
-/

public section

namespace Cslib.Probability

open Finset RotationMap
open scoped BigOperators

/-- The concrete component gap applies on each actual retained-pair slice. Full-coordinate
representation and operator identification are required only when that slice is nonempty.
No conditional output-moment estimate or minimum-density bound is assumed. -/
theorem rowNormPow_conditionalWalk_component_le
    {Ω V D : Type*} [Fintype Ω] [Fintype V] [Fintype D] [Nonempty D]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    {H M J : ℕ} {P L : Fin J → ℕ} [∀ j, Fact (P j).Prime]
    [∀ j, NeZero (L j)] [NeZero M] (hH : 3 ≤ H) (hL : ∀ j, L j ≤ P j)
    (y : V → V → ∀ j, ZMod (P j))
    (G : ∀ x y, RotationMap (RetainedPairSlice X Y x y) D)
    (e : ∀ x z, Nonempty (RetainedPairSlice X Y x z) →
      RetainedPairSlice X Y x z ≃
        ((∀ j, RetentionSlice (P j) H 1 (L j) (y x z j)) × (Fin H → ZMod M)))
    (hmodel : ∀ x z (hn : Nonempty (RetainedPairSlice X Y x z)),
      (G x z).walk = ((((ofPerms (componentMove H M P L)).lazy.reindex
        (componentEquiv M hL (y x z)).symm).reindex (e x z hn).symm).walk))
    {N u : ℝ} (hNu : 0 ≤ N * u) (t : ℕ) (F : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x z =>
      conditionalWalk X Y G (fun _ _ => t) F σ x z - rowSliceMean X Y F x z) ≤
      32 * (1 - 1 / (155648 * (J + 1) * H ^ 4)) ^ (2 * t) * rowNormPow 4 N u X Y F := by
  have hden : (1 : ℝ) ≤ 155648 * ((J : ℝ) + 1) * (H : ℝ) ^ 4 := by
    have hHpos : 0 < H := by omega
    have hn : 1 ≤ 155648 * (J + 1) * H ^ 4 := Nat.succ_le_of_lt (by positivity)
    exact_mod_cast hn
  have hgap0 : (0 : ℝ) ≤ 1 - 1 / (155648 * (J + 1) * H ^ 4) := by
    have hdiv : (1 : ℝ) / (155648 * (J + 1) * H ^ 4) ≤ 1 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < 155648 * (J + 1) * H ^ 4)).2
      simpa only [one_mul] using hden
    linarith
  apply rowNormPow_conditionalWalk_le_raw X Y hNu G
  intro x z
  rcases isEmpty_or_nonempty (RetainedPairSlice X Y x z) with hs | hs
  · rw [(G x z).spectralExpansion_eq_zero_of_subsingleton]
    exact hgap0
  · rw [(G x z).spectralExpansion_eq_of_walk_eq (hmodel x z hs),
      spectralExpansion_reindex, spectralExpansion_reindex]
    exact spectralExpansion_lazy_ofPerms_componentMove_le hH

end Cslib.Probability
