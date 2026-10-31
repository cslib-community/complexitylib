/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.OverflowNoise
public import Complexity.Foundations.Probability.RootMetric.Minkowski

/-!
# Moment budgets for the actual first-overflow noise tail

The pointwise unique-tail comparison and finite Minkowski inequality turn individual noise
moment budgets into a budget for the actual first-overflow tail. All arrays and events may
depend on the same environment. No conditional rarity factor is applied to noise.

This supplies the finite Minkowski step of [OpenAI2026LogSpace, Section 8.4], leading to
`buf-noise-sum`. The individual prefix-noise estimates, propagation-weight bounds and the
uniform bound on their weighted budget sum remain separate obligations.

## Main results

* `Cslib.RowCompression.vertexNormPow_firstOverflowNoiseTail_le_pow_sum`: the actual tail
  satisfies the power of the weighted sum of individual moment budgets.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, proof paragraph leading to equation labelled `buf-noise-sum`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.RowCompression

/-- **The finite first-overflow noise budget.** Individual normalized `p`-th moments bounded
by `ε i ^ p` give a tail budget `(∑ i < m, w i * ε i) ^ p`. This allows arbitrary correlation
between all noise arrays, the compression run, and the retained sources. -/
theorem vertexNormPow_firstOverflowNoiseTail_le_pow_sum {Ω V ι : Type*}
    [Fintype Ω] [Fintype V] (S : Ω → V → Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : Ω → V → ℕ → ι → Fin 2 → ℝ) (a : Ω → V → State ι) (m : ℕ)
    {p : ℕ} (hp : p ≠ 0) {N u : ℝ} (hNu : 0 ≤ N * u)
    (X : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    (w ε : ℕ → ℝ) (γ : ℕ → Ω → V → ℝ)
    (hw : ∀ i < m, 0 ≤ w i) (hε : ∀ i < m, 0 ≤ ε i)
    (hγ : ∀ i < m, ∀ σ x, X σ x → 0 ≤ γ i σ x)
    (hbudget : ∀ i < m, vertexNormPow p N u X (γ i) ≤ ε i ^ p) :
    vertexNormPow p N u X (fun σ x =>
      firstOverflowNoiseTail (S σ x) n K ρ (Δ σ x) (a σ x) m w (fun i => γ i σ x)) ≤
        (∑ i ∈ range m, w i * ε i) ^ p :=
  (vertexNormPow_firstOverflowNoiseTail_le S n K ρ Δ a m hNu X w γ hw hγ).trans
    (vertexNormPow_sum_le_pow_sum hp hNu (range m) γ w ε
      (fun i hi => hw i (mem_range.mp hi)) (fun i hi => hε i (mem_range.mp hi))
      (fun i hi => hbudget i (mem_range.mp hi)))

end Cslib.RowCompression
