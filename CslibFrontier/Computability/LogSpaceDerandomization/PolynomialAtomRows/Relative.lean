/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.PolynomialAtomRows.RootError
public import CslibFrontier.Computability.LogSpaceDerandomization.PolynomialAtomRows.Saturation
public import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.GateClosure
public import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.SentinelRelative
import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.SaturatedRoot
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Relative stability of actual polynomial row outputs

The preparation, auxiliary score, and witness have a uniform fourth-root comparison between
the actual compression schedule and the zero-increment reference with the same initial loss.
The coefficient depends only on the chosen function and its support scale. It does not depend
on entry magnitudes, retained width, capacities, horizon, compression scale, or errors.

The proof treats every error budget. A large budget uses the concrete output range. For a
small budget, at least `K` large true entries close both actual padded-rank gates. Otherwise,
common sentinel replacement gives quantitative state stability; upper entry saturation and
exact rank coupling transfer it back to the actual outputs. No final-error, count, threshold
ceiling, or scalar regularity assumption is passed to the public comparison theorem.

## Main results

* `Cslib.PolynomialAtomRow.exists_iterate_root_bound`: uniform relative fourth-root stability
  for the actual calculation and its stationary reference, for every error budget.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, Lemma 8.3, specialized to the concrete polynomial fourth-root family
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

universe u
namespace Cslib.PolynomialAtomRow

open Finset RowCompression

variable (kind : PolynomialAtomRow) {θ η : ℝ}

/-- **Relative stability for the concrete fourth-root family.** The constant is uniform in
all calculation data, including the compression scale. The actual schedule is compared with
the zero-increment reference having the same initial loss. There is no small-error or
heavy-count premise: both count branches and every nonnegative error budget are covered. -/
theorem exists_iterate_root_bound (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ) (ρ : ℕ → ℝ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (truth raw₀ loss : ι → Fin 2 → ℝ) (z η : ℝ) (K : ℕ),
      0 < η → η ≤ θ / 10000 → z ≤ η → 0 < K →
      ∀ (m : ℕ), 0 < m → (∀ i < m, K ≤ n i) → (∀ i < m, ρ i ≤ η) →
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ η / 2) →
      (∀ y ∈ s, ∀ ν, |loss y ν| ≤ η / 2) →
      ∀ (ε : ℕ → ℝ), (∀ i ≤ m, 0 ≤ ε i) →
      (∀ i ≤ m, ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw₀ i y) ≤ ε i) →
      ∀ y ∈ s,
      |kind.stateRootError θ s K
        (iterate s n (fun _ => K) ρ Δ ⟨z, raw₀ + loss⟩ m)
        (iterate s n (fun _ => K) ρ (fun _ => 0) ⟨z, truth + loss⟩ m) y| ≤
        C * prefixErrorBudget ε m := by
  let H := fun d (_v : ℝ) r => kind.eval θ d r
  have hsat (d d' v r : ℝ) (hd : θ ≤ d) (hd' : θ ≤ d') : H d v r = H d' v r :=
    kind.eval_eq_of_entry_ge hθ hd hd'
  have hrange {ι : Type u} (s : Finset ι) (K : ℕ) (a b : State ι) (y : ι) :
      |RowCompression.stateRootError H s K a b y| ≤ 1 := by
    simpa only [RowCompression.stateRootError, stateRootError, H]
      using kind.abs_stateRootError_le_one θ s K a b y
  have hroot : ∃ A : ℝ, 0 ≤ A ∧ ∀ d v r d' v' r',
      |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
        A * (|d - d'| + |v - v'| + |r - r'|) := by
    obtain ⟨A, hA, hbound⟩ := kind.exists_abs_eval_root_sub_le θ
    refine ⟨A, hA, ?_⟩
    intro d v r d' v' r'
    exact (hbound d r d' r').trans
      (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (v - v')]) hA)
  have hgate (d v r : ℝ) (hr : θ ≤ r) : H d v r = 0 :=
    kind.eval_eq_zero_of_rank_ge hθ ((kind.gateThreshold_le_scale hθ).trans hr)
  simpa only [RowCompression.stateRootError, stateRootError, H] using
    RowCompression.exists_iterate_root_bound H hsat 1 (by norm_num) hrange hroot hgate hθ

end Cslib.PolynomialAtomRow
