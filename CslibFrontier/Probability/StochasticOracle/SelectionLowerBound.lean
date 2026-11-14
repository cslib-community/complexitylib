/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy

/-!
# Universal selection-only lower accounting

[Wang2027], Theorem 5(2), PDF p. 12, Appendix A.5, p. 16. A policy is an
arbitrary randomized choice/output kernel for a fixed oracle. Successful extraction
is constrained only by selection-only provenance. The count bridge is derived from
all revealed proposals and the size cap, without a retention or certification rule.

## Main results

* `lower_cost`, `universal_lower_cost`: source token lower bound for arbitrary admissible policies.
* `successProbability_eq_integral`, `expectedCost_eq_integral`: actual process interpretation.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy
open Cslib.Optimization.OneConstraint AdaptiveSelection PartialCover Finset MeasureTheory
variable {B R J E : Type} [Fintype B] [Fintype R] [Fintype J]
  [DecidableEq J] [DecidableEq E]

omit [DecidableEq J] in
/-- Actual finite-history accounting is the cylinder expectation under the
constructed infinite policy law, including randomized final extraction. -/
theorem successProbability_eq_integral [MeasurableSpace (Record B R)]
    [MeasurableSingletonClass (Record B R)] (O : Oracle B R J) (π : Policy B R J)
    (I : Instance E J) (ρ D : ℝ) (u : ℕ) :
    successProbability O π I ρ D u =
      ∫ ω, success O π I ρ D (responseHistory ω u) ∂responseMeasure (law O π) :=
  (integral_responseHistory (law O π) (success O π I ρ D) u).symm

omit [DecidableEq J] in
/-- The same physical policy execution supplies the actual finite token expectation. -/
theorem expectedCost_eq_integral [MeasurableSpace (Record B R)]
    [MeasurableSingletonClass (Record B R)] (O : Oracle B R J) (π : Policy B R J)
    (u : ℕ) : expectedCost O π u =
      ∫ ω, accruedBill (bill O) (responseHistory ω u) ∂responseMeasure (law O π) :=
  (integral_responseHistory (law O π) (accruedBill (bill O)) u).symm

/-- Source universal token lower bound for an arbitrary actual admissible policy.
Only its achieved success level is an input; no count, expected-cost lower bound
or optimality conclusion is assumed. Conditional bounds apply only on support. -/
theorem lower_cost (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (hA : Admissible O π) (b r u : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p c ℓ ρ D η : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (_hη0 : 0 ≤ η)
    (H : LowerBounds O π I b p c ℓ)
    (hη : η ≤ successProbability O π I ρ D u) :
    η * (r : ℝ) * c / p ≤ expectedCost O π u := by
  classical
  let P : ℕ → ℝ := fun t => historyExpectation (law O π)
    (fun h => (law O π h).mean (fun x => if reveals I (proposals O) h x then 1 else 0)) t []
  let A : ℕ → ℝ := fun t => historyExpectation (law O π)
    (fun h => (law O π h).mean (fun x => if issued h x then 1 else 0)) t []
  let C : ℕ → ℝ := fun t => historyExpectation (law O π)
    (fun h => (law O π h).mean (bill O h)) t []
  have hg (t : ℕ) : P t ≤ p * A t := by
    have h := historyExpectation_mono_reachable (law O π) _ _
      (fun h hh => (conditional_means O π I b p c ℓ H h hh).1) t [] .nil
    simpa only [historyExpectation_mul] using h
  have hb (t : ℕ) : c * A t ≤ C t := by
    have h := historyExpectation_mono_reachable (law O π) _ _
      (fun h hh => (conditional_means O π I b p c ℓ H h hh).2) t [] .nil
    simpa only [historyExpectation_mul] using h
  have hpath : ∀ h, Reachable (law O π) h → (r : ℝ) * success O π I ρ D h ≤
      accruedBill (fun h x => if reveals I (proposals O) h x then 1 else 0) h := by
    intro h hh
    rw [accrued_indicator_eq_count]
    apply (mul_le_mul_of_nonneg_left
      (success_le_count_tail O π I hA b r hr p c ℓ ρ D H h hh) (Nat.cast_nonneg r)).trans
    split_ifs with ht
    · simpa only [mul_one] using
        (show (r : ℝ) ≤ count (reveals I (proposals O)) h by exact_mod_cast ht)
    · simp
  have hs : η * (r : ℝ) ≤ ∑ t ∈ range u, P t := by
    have hm := historyExpectation_mono_reachable (law O π) _ _ hpath u [] .nil
    rw [historyExpectation_mul, historyExpectation_accruedBill, accruedBill,
      zero_add, executionCost_eq_sum] at hm
    have hη' := mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg r)
    change r * successProbability O π I ρ D u ≤ _ at hm
    nlinarith
  have he : expectedCost O π u = ∑ t ∈ range u, C t := by
    rw [expectedCost, historyExpectation_accruedBill, accruedBill, zero_add,
      executionCost_eq_sum]
  rw [he]
  simpa only [Fin.sum_univ_eq_sum_range] using
    marginal_lower_cost (fun t : Fin u => A t.val) (fun t : Fin u => P t.val)
      (fun t : Fin u => C t.val) (η * r) p c hp hc
      (by simpa only [Fin.sum_univ_eq_sum_range] using hs)
      (fun t => hg t.val) (fun t => hb t.val)

/-- The lower bound quantifies over all admissible policies for this oracle, not
only a constructed policy. Universal assumptions contain only local envelopes. -/
theorem universal_lower_cost (O : Oracle B R J) (I : Instance E J)
    (b r u : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p c ℓ ρ D η : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (hη0 : 0 ≤ η)
    (H : UniversalBounds O I b p c ℓ) :
    ∀ π : Policy B R J, Admissible O π → η ≤ successProbability O π I ρ D u →
      η * (r : ℝ) * c / p ≤ expectedCost O π u := by
  intro π hA hη
  exact lower_cost O π I hA b r u hr p c ℓ ρ D η hp hc hη0 (H π hA) hη

end Cslib.Probability.StochasticOracle.SelectionPolicy
