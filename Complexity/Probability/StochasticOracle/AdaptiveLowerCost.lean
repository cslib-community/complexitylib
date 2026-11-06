/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.FiniteTable
import Mathlib.Tactic

/-!
# Conditional-history accounting for adaptive revealed progress

This is the expectation argument in [Wang2027], Theorem 5(2), Section 6
(PDF p. 12), Appendix A.5 (PDF p. 16). It is a finite-transcript accounting
lemma, not the full theorem: deriving the pathwise progress count from actual
revealed sets and proving the deadline binomial tail remain separate obligations.

`conditional_lower_cost` allows a different finite history alphabet at each turn.
Each history includes the selected batch before its responses. The hypotheses
are unnormalized conditional inequalities, multiplied by history probability;
thus null histories need no division or arbitrary conditional-law convention.
Neither progress nor costs are assumed independent between turns.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Finset Cslib.Optimization.OneConstraint

open scoped Classical in
/-- The universal lower-cost accounting step. `issued` is the reached-turn indicator,
`progress` counts reached turns with revealed progress, and `bill` is the issued
batch's token bill (zero for an unissued turn). `complete` implies at least `r`
progress turns. Conditional bounds apply at each history and selected batch.
This proves `η * r * c / p ≤ E[bill]` without independence or a supplied aggregate
expected-cost hypothesis. -/
theorem conditional_lower_cost
    {Ω : Type} [Fintype Ω] (w : Distribution Ω ℝ) (u : ℕ)
    (H : Fin u → Type) [∀ t, Finite (H t)]
    (history : (t : Fin u) → Ω → H t)
    (issued progress bill : Fin u → Ω → ℝ) (complete : Ω → Prop)
    (r p c η : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (hη : η ≤ w.mean fun ω => if complete ω then 1 else 0)
    (hcount : ∀ ω, r * (if complete ω then 1 else 0) ≤ ∑ t, progress t ω)
    (hr : 0 ≤ r)
    (hprogress : ∀ t h,
      (∑ ω, w.weight ω * (if history t ω = h then progress t ω else 0)) ≤
        p * ∑ ω, w.weight ω * (if history t ω = h then issued t ω else 0))
    (hbill : ∀ t h,
      c * (∑ ω, w.weight ω * (if history t ω = h then issued t ω else 0)) ≤
        ∑ ω, w.weight ω * (if history t ω = h then bill t ω else 0)) :
    η * r * c / p ≤ w.mean (fun ω => ∑ t, bill t ω) := by
  classical
  let (t : Fin u) : Fintype (H t) := Fintype.ofFinite (H t)
  have partition (t : Fin u) (f : Ω → ℝ) :
      (∑ h, ∑ ω, w.weight ω * (if history t ω = h then f ω else 0)) =
        w.mean f := by
    rw [sum_comm]
    simp [Distribution.mean, mul_ite]
  have hg (t : Fin u) : w.mean (progress t) ≤ p * w.mean (issued t) := by
    have hs := sum_le_sum (fun h (_ : h ∈ (univ : Finset (H t))) => hprogress t h)
    simpa only [← mul_sum, partition] using hs
  have hb (t : Fin u) : c * w.mean (issued t) ≤ w.mean (bill t) := by
    have hs := sum_le_sum (fun h (_ : h ∈ (univ : Finset (H t))) => hbill t h)
    simpa only [← mul_sum, partition] using hs
  have hsum (f : Fin u → Ω → ℝ) :
      w.mean (fun ω => ∑ t, f t ω) = ∑ t, w.mean (f t) := by
    simp only [Distribution.mean, mul_sum]
    rw [sum_comm]
  have hpath : r * w.mean (fun ω => if complete ω then 1 else 0) ≤
      ∑ t, w.mean (progress t) := by
    rw [← hsum, ← Distribution.mean_mul]
    exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hcount ω) (w.nonneg ω)
  have hg' := sum_le_sum (fun t (_ : t ∈ (univ : Finset (Fin u))) => hg t)
  have hb' := sum_le_sum (fun t (_ : t ∈ (univ : Finset (Fin u))) => hb t)
  rw [← mul_sum] at hg' hb'
  rw [hsum, div_le_iff₀ hp]
  have hη' := mul_le_mul_of_nonneg_left hη hr
  have hchain : η * r ≤ p * ∑ t, w.mean (issued t) := by nlinarith
  have := mul_le_mul_of_nonneg_left hchain hc
  nlinarith

end Cslib.Probability.StochasticOracle
