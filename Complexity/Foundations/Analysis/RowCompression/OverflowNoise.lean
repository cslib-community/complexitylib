/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.FalseOverflow
public import Complexity.Foundations.Probability.RootMetric
public import Complexity.Foundations.Data.Finset.UniqueTail
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Positivity

/-!
# Noise tails at the unique actual first overflow

On each row there is at most one first-overflow index. Hence the sum of its selected noise
tail is bounded by the full weighted noise sum, pointwise in the environment. The resulting
integrated moment comparison permits arbitrary dependence between noise and overflow.

This is the pointwise aggregation step in [OpenAI2026LogSpace, Section 8.4], the paragraph
leading to equation `buf-noise-sum`. The event is `IsFirstOverflow` of the actual compression
run. No conditional rarity discount is claimed for noise. Prefix-noise budgets, Minkowski,
propagation weights and convergence of their final series remain separate.

## Main results

* `Cslib.RowCompression.firstOverflowNoiseTail_le`: selected actual tails cost at most one full sum.
* `Cslib.RowCompression.vertexNormPow_firstOverflowNoiseTail_le`: integrated moment comparison
  in the existing `RootMetric` normalization, allowing all correlations.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, proof paragraph leading to equation labelled `buf-noise-sum`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.RowCompression

variable {ι : Type*}

/-- The sum of weighted tails selected by actual first-overflow events before group `m`.
This finite quantity is defined even for runs without an overflow. -/
@[expose] noncomputable def firstOverflowNoiseTail (s : Finset ι) (n K : ℕ → ℕ)
    (ρ : ℕ → ℝ) (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (m : ℕ) (w γ : ℕ → ℝ) : ℝ := by
  classical
  exact ∑ j ∈ range m, if IsFirstOverflow s n K ρ Δ a j then
    ∑ i ∈ Ico j m, w i * γ i else 0

/-- Nonnegative weights and noise give a nonnegative selected tail, even without an overflow. -/
theorem firstOverflowNoiseTail_nonneg (s : Finset ι) (n K : ℕ → ℕ)
    (ρ : ℕ → ℝ) (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (m : ℕ) {w γ : ℕ → ℝ}
    (hw : ∀ i < m, 0 ≤ w i) (hγ : ∀ i < m, 0 ≤ γ i) :
    0 ≤ firstOverflowNoiseTail s n K ρ Δ a m w γ := by
  classical
  unfold firstOverflowNoiseTail
  refine sum_nonneg fun j _ => ?_
  split_ifs
  · exact sum_nonneg fun i hi => mul_nonneg (hw i (mem_Ico.mp hi).2) (hγ i (mem_Ico.mp hi).2)
  · exact le_rfl

/-- **Actual first-overflow noise aggregation.** The first index is unique for every run,
so its nonnegative weighted tail is bounded by the single full sum. -/
theorem firstOverflowNoiseTail_le (s : Finset ι) (n K : ℕ → ℕ)
    (ρ : ℕ → ℝ) (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (m : ℕ) {w γ : ℕ → ℝ}
    (hw : ∀ i < m, 0 ≤ w i) (hγ : ∀ i < m, 0 ≤ γ i) :
    firstOverflowNoiseTail s n K ρ Δ a m w γ ≤ ∑ i ∈ range m, w i * γ i := by
  classical
  exact sum_ite_Ico_le_sum_range m (IsFirstOverflow s n K ρ Δ a)
    (fun i hi => mul_nonneg (hw i hi) (hγ i hi)) (fun _ _ _ _ hj hk => hj.unique hk)

/-- **Integrated noise aggregation.** Noise may depend on the same environment as the entire
compression run. No independence or conditional-frequency hypothesis occurs. -/
theorem vertexNormPow_firstOverflowNoiseTail_le {Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : Ω → V → Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : Ω → V → ℕ → ι → Fin 2 → ℝ) (a : Ω → V → State ι) (m : ℕ)
    {p : ℕ} {N u : ℝ} (hNu : 0 ≤ N * u) (X : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    (w : ℕ → ℝ) (γ : ℕ → Ω → V → ℝ) (hw : ∀ i < m, 0 ≤ w i)
    (hγ : ∀ i < m, ∀ σ x, X σ x → 0 ≤ γ i σ x) :
    vertexNormPow p N u X (fun σ x =>
      firstOverflowNoiseTail (S σ x) n K ρ (Δ σ x) (a σ x) m w (fun i => γ i σ x)) ≤
        vertexNormPow p N u X (fun σ x => ∑ i ∈ range m, w i * γ i σ x) := by
  unfold vertexNormPow
  refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
  refine sum_le_sum fun x hx => ?_
  have hx' : X σ x := (mem_filter.mp hx).2
  have hnoise := firstOverflowNoiseTail_nonneg (S σ x) n K ρ (Δ σ x) (a σ x) m hw
    (fun i hi => hγ i hi σ x hx')
  have hfull : 0 ≤ ∑ i ∈ range m, w i * γ i σ x :=
    sum_nonneg fun i hi => mul_nonneg (hw i (mem_range.mp hi)) (hγ i (mem_range.mp hi) σ x hx')
  rw [abs_of_nonneg hnoise, abs_of_nonneg hfull]
  exact pow_le_pow_left₀ hnoise
    (firstOverflowNoiseTail_le (S σ x) n K ρ (Δ σ x) (a σ x) m hw
      (fun i hi => hγ i hi σ x hx')) p

end Cslib.RowCompression
