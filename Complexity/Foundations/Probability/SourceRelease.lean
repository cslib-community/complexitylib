/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric
public import Complexity.Foundations.Probability.CorrectionAtom
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Source release through a bounded incoming relation

In a product of stochastic tables, the right factor is queried at an intermediate vertex `z`.
Its error is a common table `e σ z y`: it does not take the old source `x` as an extra argument.
If the left support relation has at most `K` retained sources at each `z`, double counting
eliminates the old source at cost `K`. Changing the source normalization from `1 / u` to
`1 / f` then contributes exactly `f / u`.

This is the explicit source-release inequality in the proof of [OpenAI2026LogSpace, Lemma 7.3],
in the September 23, 2026 source version at `openai/math` commit `7ef5c0cc`. Here the indicators
`X_u`, `Z_f`, and `Y_b` are finite-set restrictions `X`, `Z`, and `Y`; the left normalization
is written `(N * u)⁻¹`. The exponent is any natural number, including the paper's `s = 8`.
The theorem proves the source-domain comparison, not the remaining scale comparisons or the
recursive estimator of that lemma. No independence hypothesis is imposed: the support relation,
channels, and error may all depend on the same environment `σ`.

The correction-atom corollaries discharge the incoming-degree hypothesis using
`Matrix.card_filter_correctionAtom_col_ne_zero_lt`. An arbitrary map from the full environment
to the atom's two seeds allows additional shared coordinates in the right error.

## Main results

* `Finset.sum_sum_filter_le_mul_sum_of_card_le`: the finite double-counting inequality.
* `Cslib.sourceRelease_le_rowNormPow`, `Cslib.sourceRelease_le_vertexNormPow`: the exact
  `K * (f / u)` cost for a common right table or vector.
* `Matrix.correctionAtom_sourceRelease_le_rowNormPow`,
  `Matrix.correctionAtom_sourceRelease_le_vertexNormPow`: source release for correction atoms.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  proof of Lemma 7.3 (preprint, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Finset

/-- A nonnegative weight at a target is counted at most `K` times if that target has at most
`K` incoming sources. The weight is common to all sources. -/
theorem sum_sum_filter_le_mul_sum_of_card_le {α β : Type*} (S : Finset α) (T : Finset β)
    (P : α → β → Prop) [∀ x z, Decidable (P x z)] {w : β → ℝ} {K : ℕ}
    (hw : ∀ z ∈ T, 0 ≤ w z) (hK : ∀ z ∈ T, #{x ∈ S | P x z} ≤ K) :
    ∑ x ∈ S, ∑ z ∈ T with P x z, w z ≤ K * ∑ z ∈ T, w z := by
  calc
    ∑ x ∈ S, ∑ z ∈ T with P x z, w z =
        ∑ z ∈ T, (#{x ∈ S | P x z} : ℝ) * w z := by
      simp only [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun z _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ z ∈ T, (K : ℝ) * w z := by
      refine sum_le_sum fun z hz => mul_le_mul_of_nonneg_right ?_ (hw z hz)
      exact_mod_cast hK z hz
    _ = K * ∑ z ∈ T, w z := (mul_sum ..).symm

end Finset

namespace Cslib

variable {Ω V : Type*} [Fintype Ω] [Fintype V]
  {s : ℕ} {N u f : ℝ} {X Z Y : Ω → V → Prop}
  [∀ σ x, Decidable (X σ x)] [∀ σ z, Decidable (Z σ z)] [∀ σ y, Decidable (Y σ y)]

/-- **Source release for a common right table**, the explicit double-counting estimate in the
proof of [OpenAI2026LogSpace, Lemma 7.3]. A pointwise incoming cap costs `K * (f / u)` in norm
power. The error and the relation may depend on the same environment. -/
theorem sourceRelease_le_rowNormPow (hN : 0 < N) (hu : 0 < u) (hf : 0 < f)
    (P : Ω → V → V → Prop) [∀ σ x z, Decidable (P σ x z)] {K : ℕ}
    (hK : ∀ σ z, Z σ z → #{x ∈ ({x | X σ x} : Finset V) | P σ x z} ≤ K)
    (e : Ω → V → V → ℝ) :
    (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ z ∈ ({z | Z σ z} : Finset V) with P σ x z,
          ∑ y ∈ ({y | Y σ y} : Finset V), |e σ z y| ^ s ≤
      K * (f / u) * rowNormPow s N f Z Y e := by
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, (K : ℝ) *
        ∑ z ∈ ({z | Z σ z} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V),
          |e σ z y| ^ s := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (by positivity)
      refine sum_sum_filter_le_mul_sum_of_card_le _ _ (P σ) (fun _ _ => by positivity) ?_
      intro z hz
      exact hK σ z (by simpa using hz)
    _ = _ := by
      rw [← mul_expect, rowNormPow]
      field_simp

/-- The vector version of source release, used for the right error in a reward update. -/
theorem sourceRelease_le_vertexNormPow (hN : 0 < N) (hu : 0 < u) (hf : 0 < f)
    (P : Ω → V → V → Prop) [∀ σ x z, Decidable (P σ x z)] {K : ℕ}
    (hK : ∀ σ z, Z σ z → #{x ∈ ({x | X σ x} : Finset V) | P σ x z} ≤ K)
    (v : Ω → V → ℝ) :
    (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ z ∈ ({z | Z σ z} : Finset V) with P σ x z, |v σ z| ^ s ≤
      K * (f / u) * vertexNormPow s N f Z v := by
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, (K : ℝ) * ∑ z ∈ ({z | Z σ z} : Finset V), |v σ z| ^ s := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (by positivity)
      refine sum_sum_filter_le_mul_sum_of_card_le _ _ (P σ) (fun _ _ => by positivity) ?_
      intro z hz
      exact hK σ z (by simpa using hz)
    _ = _ := by
      rw [← mul_expect, vertexNormPow]
      field_simp

end Cslib

namespace Matrix

variable {Ω V ι κ : Type*} [Fintype Ω] [Fintype V] [Fintype ι] [Fintype κ]
  {s K Kc : ℕ} {N u f : ℝ} {I : ℝ → ℝ → ℝ} {τ Q h ρ : ℝ → ℝ}
  {G : Matrix V V ℝ} {g₀ : V → ℝ} {X : ι → V → Prop} {Y Yt : κ → V → Prop}
  [∀ t x, Decidable (X t x)] [∀ t z, Decidable (Y t z)] [∀ t z, Decidable (Yt t z)]

/-- Source release for an actual correction atom. Its incoming gate supplies the degree bound;
no separate sparsity or independence assumption is needed. `draw` selects the atom's seeds
from the full shared environment. -/
theorem correctionAtom_sourceRelease_le_rowNormPow (draw : Ω → ι × κ)
    (Yb : Ω → V → Prop) [∀ σ y, Decidable (Yb σ y)] (hN : 0 < N) (hu : 0 < u) (hf : 0 < f)
    (hKc : 0 < Kc) (hIQ : ∀ v r, Q v ≠ 0 → ρ r ≠ 0 → I v r = 1)
    {g : ℝ} (hg : g ≤ 1) (hτ : ∀ r, g ≤ r → τ r = 0) (e : Ω → V → V → ℝ) :
    (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X (draw σ).1 x} : Finset V),
        ∑ z ∈ ({z | Yt (draw σ).2 z} : Finset V)
          with correctionAtom I τ K Kc f G X Y Yt Q h ρ g₀ (draw σ) x z ≠ 0,
            ∑ y ∈ ({y | Yb σ y} : Finset V), |e σ z y| ^ s ≤
      Kc * (f / u) * Cslib.rowNormPow s N f (fun σ z => Yt (draw σ).2 z) Yb e := by
  refine Cslib.sourceRelease_le_rowNormPow hN hu hf _ (fun σ z _ => ?_) e
  exact (card_filter_correctionAtom_col_ne_zero_lt hKc hIQ hg hτ (draw σ) z).le

/-- Source release for a common right vector through a correction atom, with its incoming
degree bound supplied by the incoming gate. -/
theorem correctionAtom_sourceRelease_le_vertexNormPow (draw : Ω → ι × κ)
    (hN : 0 < N) (hu : 0 < u) (hf : 0 < f) (hKc : 0 < Kc)
    (hIQ : ∀ v r, Q v ≠ 0 → ρ r ≠ 0 → I v r = 1)
    {g : ℝ} (hg : g ≤ 1) (hτ : ∀ r, g ≤ r → τ r = 0) (v : Ω → V → ℝ) :
    (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X (draw σ).1 x} : Finset V),
        ∑ z ∈ ({z | Yt (draw σ).2 z} : Finset V)
          with correctionAtom I τ K Kc f G X Y Yt Q h ρ g₀ (draw σ) x z ≠ 0,
            |v σ z| ^ s ≤
      Kc * (f / u) * Cslib.vertexNormPow s N f (fun σ z => Yt (draw σ).2 z) v := by
  refine Cslib.sourceRelease_le_vertexNormPow hN hu hf _ (fun σ z _ => ?_) v
  exact (card_filter_correctionAtom_col_ne_zero_lt hKc hIQ hg hτ (draw σ) z).le

end Matrix
