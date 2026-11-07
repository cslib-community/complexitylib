/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric
import Complexity.Foundations.Data.Finset.Markov
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Conditioning an integrated moment on one retained start

An integrated error bound controls the conditional moment at any specified retained vertex.
The cost is exactly `N * u / π`, where `π` is the actual density of environments retaining
that vertex and `u` is the nominal rate in `vertexNormPow`. The nominal and actual rates need
not agree. No independence of the retention mask and the error is assumed.

These are the moment and Markov steps of [OpenAI2026LogSpace, Lemma 12.2], equations
`final-conditional` and `final-tail`, at revision `7ef5c0cc` (23 September 2026, unrefereed).
The source uses eighth moments; the statements here allow every natural exponent, including
the fourth moments of the library's estimator route. They apply to an error array supplied by
the caller; they do not construct the recursive estimator or prove its global moment bound.

## Main results

* `Cslib.expect_retained_vertex_pow_le`: conditional moment from the integrated norm.
* `Cslib.retained_vertex_tail_le`: conditional tail bound at a specified start.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 12.2, revision `7ef5c0cc` (preprint, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

variable {Ω V : Type*} [Fintype Ω] [Fintype V]
  {p : ℕ} {N u : ℝ} {X : Ω → V → Prop} [∀ σ x, Decidable (X σ x)]

/-- Keeping one nonnegative summand converts the integrated norm into a conditional moment.
The conditioning event must be nonempty; its actual density appears in the denominator. -/
theorem expect_retained_vertex_pow_le (hNu : 0 < N * u) (v : Ω → V → ℝ) (z : V)
    (hz : ({σ | X σ z} : Finset Ω).Nonempty) :
    (𝔼 σ ∈ ({σ | X σ z} : Finset Ω), |v σ z| ^ p) ≤
      N * u / (({σ | X σ z} : Finset Ω).dens : ℝ) * vertexNormPow p N u X v := by
  classical
  let E : Finset Ω := {σ | X σ z}
  have hπ : (0 : ℝ) < E.dens := by exact_mod_cast hz.dens_pos
  have hkeep : (𝔼 σ, if σ ∈ E then |v σ z| ^ p else 0) ≤
      𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), |v σ x| ^ p := by
    refine expect_le_expect fun σ _ => ?_
    split_ifs with hσ
    · exact single_le_sum (f := fun x : V => |v σ x| ^ p)
        (fun x _ => pow_nonneg (abs_nonneg _) _)
        (show z ∈ ({x | X σ x} : Finset V) by
          simpa only [E, mem_filter, mem_univ, true_and] using hσ)
    · exact sum_nonneg fun x _ => pow_nonneg (abs_nonneg _) _
  rw [Fintype.expect_ite_mem, NNRat.smul_def] at hkeep
  change (𝔼 σ ∈ E, |v σ z| ^ p) ≤ _
  apply (mul_le_mul_iff_right₀ hπ).mp
  calc
    (E.dens : ℝ) * (𝔼 σ ∈ E, |v σ z| ^ p) ≤
        𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V), |v σ x| ^ p := by
          exact hkeep
    _ = (E.dens : ℝ) * (N * u / (E.dens : ℝ) * vertexNormPow p N u X v) := by
      unfold vertexNormPow
      field_simp [hNu.ne', hπ.ne']
      rw [mul_assoc, mul_div_cancel_right₀ _ hNu.ne']

/-- Markov's bound for the fraction of retained environments whose error exceeds `η`.
The ratio of cardinalities is the uniform conditional probability, not the unconditional
density of the bad event. -/
theorem retained_vertex_tail_le (hNu : 0 < N * u) (v : Ω → V → ℝ) (z : V)
    (hz : ({σ | X σ z} : Finset Ω).Nonempty) {η : ℝ} (hη : 0 < η) :
    (#{σ ∈ ({σ | X σ z} : Finset Ω) | η < |v σ z|} : ℝ) /
        #({σ | X σ z} : Finset Ω) ≤
      (N * u / (({σ | X σ z} : Finset Ω).dens : ℝ) * vertexNormPow p N u X v) / η ^ p := by
  classical
  have hcard : (0 : ℝ) < #({σ | X σ z} : Finset Ω) := by exact_mod_cast hz.card_pos
  have hmarkov := card_filter_mul_le_sum ({σ | X σ z} : Finset Ω)
    (fun σ => η < |v σ z|) (fun σ => |v σ z| ^ p)
    (fun σ _ => pow_nonneg (abs_nonneg _) p)
    (fun σ _ h => pow_le_pow_left₀ hη.le h.le p)
  apply (le_div_iff₀ (pow_pos hη p)).2
  calc
    _ ≤ (𝔼 σ ∈ ({σ | X σ z} : Finset Ω), |v σ z| ^ p) := by
      rw [expect_eq_sum_div_card, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hmarkov hcard.le
    _ ≤ _ := expect_retained_vertex_pow_le hNu v z hz

end Cslib
