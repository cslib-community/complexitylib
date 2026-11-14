/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.Discrete
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Stopped token costs for arbitrary discrete response laws

The finite stopped-cost sum of [Wang2027], Appendix A.5, for arbitrary PMF
responses and nonnegative response-dependent charges. Costs use the actual
`accruedBill` of `stoppedBill`: billing stops at actual retained completion.
No finite response alphabet, independence, integrability or total-cost premise
is imposed. Only supported incomplete histories need a one-step mean envelope.

## Main results

* `accruedBill_eq_sum_discrete`: exact finite tower accounting for actual invoices.
* `accruedBill_le_binomial_sum_discrete`: the finite binomial survival-sum bound.
* `accruedBill_le_mean_discrete`: the budget/mean envelope `c * min(n, r / p)`.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open PartialCover MeasureTheory
open scoped ENNReal
variable {E J Ω : Type*} [DecidableEq E] [DecidableEq J]

/-- Actual accrued bills agree when their next-response charges agree on every
supported prefix and supported next response. -/
theorem accruedBill_congr_on_support
    (step : ∀ t : ℕ, (Fin t → Ω) → PMF Ω)
    (bill other : List Ω → Ω → ℝ)
    (H : ∀ t h, h ∈ (PMF.seqProcess step t).support →
      ∀ x ∈ (step t h).support, bill (PMF.seqHistory h) x = other (PMF.seqHistory h) x)
    (n : ℕ) (h : Fin n → Ω) (hh : h ∈ (PMF.seqProcess step n).support) :
    accruedBill bill (PMF.seqHistory h) = accruedBill other (PMF.seqHistory h) := by
  induction n with
  | zero => simp [accruedBill]
  | succ n ih =>
    simp only [PMF.seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
    obtain ⟨g, hg, x, hx, rfl⟩ := hh
    rw [PMF.seqHistory_snoc, accruedBill, accruedBill, ih g hg, H n g hg x hx]

/-- One-step tower accounting for the actual nonnegative accrued bill. The
response and its charge may be correlated and have unbounded discrete support. -/
theorem accruedBill_step_discrete (law : List Ω → PMF Ω)
    (bill : List Ω → Ω → ℝ) (hb : ∀ h x, 0 ≤ bill h x) (n : ℕ) :
    (∑' h, PMF.seqProcess (responseStep law) (n + 1) h *
      ENNReal.ofReal (accruedBill bill (PMF.seqHistory h))) =
      (∑' h, PMF.seqProcess (responseStep law) n h *
        ENNReal.ofReal (accruedBill bill (PMF.seqHistory h))) +
      ∑' h, PMF.seqProcess (responseStep law) n h *
        ∑' x, law (PMF.seqHistory h) x * ENNReal.ofReal (bill (PMF.seqHistory h) x) := by
  rw [PMF.seqProcess, PMF.tsum_bind_mul]
  simp_rw [PMF.tsum_map_mul, PMF.seqHistory_snoc, accruedBill,
    ENNReal.ofReal_add (accruedBill_nonneg bill hb _) (hb _ _), mul_add,
    tsum_add]
  simp_rw [ENNReal.tsum_mul_right, responseStep, PMF.tsum_coe, one_mul, mul_add]
  rw [tsum_add]

/-- Finite tower accounting as a sum of actual conditional mean charges. -/
theorem accruedBill_eq_sum_discrete (law : List Ω → PMF Ω)
    (bill : List Ω → Ω → ℝ) (hb : ∀ h x, 0 ≤ bill h x) (n : ℕ) :
    (∑' h, PMF.seqProcess (responseStep law) n h *
      ENNReal.ofReal (accruedBill bill (PMF.seqHistory h))) =
      ∑ t ∈ Finset.range n, ∑' h, PMF.seqProcess (responseStep law) t h *
        ∑' x, law (PMF.seqHistory h) x * ENNReal.ofReal (bill (PMF.seqHistory h) x) := by
  induction n with
  | zero => simp [PMF.seqProcess, accruedBill]
  | succ n ih => rw [accruedBill_step_discrete law bill hb, ih, Finset.sum_range_succ]

/-- A supported-history conditional mean envelope bounds the next stopped charge
by the probability that the actual retained family is still incomplete. -/
theorem stoppedBill_marginal_le_discrete
    (I : Instance E J) (ρ : ℝ) (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → PMF Ω) (charge : List Ω → Ω → ℝ) (c : ℝ) (t : ℕ)
    (hb : ∀ h : Fin t → Ω, h ∈ (PMF.seqProcess (responseStep law) t).support →
      I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground →
      (∑' x, law (PMF.seqHistory h) x * ENNReal.ofReal (charge (PMF.seqHistory h) x)) ≤
        ENNReal.ofReal c) :
    (∑' h, PMF.seqProcess (responseStep law) t h *
      ∑' x, law (PMF.seqHistory h) x *
        ENNReal.ofReal (stoppedBill I ρ proposal charge (PMF.seqHistory h) x)) ≤
      ENNReal.ofReal c * (PMF.seqProcess (responseStep law) t).toOuterMeasure
        {h | I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground} := by
  classical
  rw [PMF.toOuterMeasure_eq_tsum_mul_indicator, ← ENNReal.tsum_mul_left]
  apply tsum_le_tsum
  intro h
  by_cases hs : h ∈ (PMF.seqProcess (responseStep law) t).support
  · by_cases hc : I.covered (selected I ρ proposal (PMF.seqHistory h)) = I.ground
    · simp [stoppedBill, hc]
    · have hm :
          PMF.seqProcess (responseStep law) t h *
            (∑' x, law (PMF.seqHistory h) x * ENNReal.ofReal (charge (PMF.seqHistory h) x)) ≤
          PMF.seqProcess (responseStep law) t h * ENNReal.ofReal c := by
        gcongr
        exact hb h hs hc
      simpa [stoppedBill, hc, mul_comm, mul_left_comm] using hm
  · have hz : PMF.seqProcess (responseStep law) t h = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hs
    simp [hz]

/-- The finite survival-sum bound for actual stopped response-dependent token
costs. Only reached incomplete prefixes need conditional probability and charge
mean bounds; no finite response alphabet or integrability premise is required. -/
theorem accruedBill_le_binomial_sum_discrete
    (I : Instance E J) (ρ : ℝ) (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → PMF Ω) (a r n : ℕ) (hr : I.ground.card ≤ a * r)
    (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ t, t < n → ∀ h : Fin t → Ω,
      h ∈ (PMF.seqProcess (responseStep law) t).support →
      I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground →
      (p : ℝ) ≤ ((law (PMF.seqHistory h)).toOuterMeasure
        {x | productive I ρ proposal a (PMF.seqHistory h) x = true}).toReal)
    (charge : List Ω → Ω → ℝ) (hcharge : ∀ h x, 0 ≤ charge h x)
    (c : ℝ) (hc : 0 ≤ c)
    (hcost : ∀ t, t < n → ∀ h : Fin t → Ω,
      h ∈ (PMF.seqProcess (responseStep law) t).support →
      I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground →
      (∑' x, law (PMF.seqHistory h) x * ENNReal.ofReal (charge (PMF.seqHistory h) x)) ≤
        ENNReal.ofReal c) :
    (∑' h, PMF.seqProcess (responseStep law) n h *
      ENNReal.ofReal (accruedBill (stoppedBill I ρ proposal charge) (PMF.seqHistory h))) ≤
      ENNReal.ofReal (c * ∑ t ∈ Finset.range n,
        (ProbabilityTheory.binomial t p).real (Set.Iio r)) := by
  classical
  have hbn : ∀ h x, 0 ≤ stoppedBill I ρ proposal charge h x := by
    intro h x
    unfold stoppedBill
    split_ifs
    · exact le_rfl
    · exact hcharge h x
  rw [accruedBill_eq_sum_discrete law _ hbn, Finset.mul_sum,
    ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg hc measureReal_nonneg)]
  apply Finset.sum_le_sum
  intro t ht
  have htn : t < n := Finset.mem_range.mp ht
  apply (stoppedBill_marginal_le_discrete I ρ proposal law charge c t
    (hcost t htn)).trans
  have hp' := incompletion_le_binomial_discrete I ρ proposal law a r t hr p
    (fun s hs => hp s (hs.trans htn))
  have he := ENNReal.ofReal_le_ofReal hp'
  rw [ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _)] at he
  rw [ENNReal.ofReal_mul hc]
  gcongr

/-- The finite budget and waiting-time mean envelopes for the actual stopped bill.
Strictly positive productivity is needed only for the `r / p` envelope. -/
theorem accruedBill_le_mean_discrete
    (I : Instance E J) (ρ : ℝ) (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → PMF Ω) (a r n : ℕ) (hr : I.ground.card ≤ a * r)
    (p : Set.Icc (0 : ℝ) 1) (hp0 : 0 < (p : ℝ))
    (hp : ∀ t, t < n → ∀ h : Fin t → Ω,
      h ∈ (PMF.seqProcess (responseStep law) t).support →
      I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground →
      (p : ℝ) ≤ ((law (PMF.seqHistory h)).toOuterMeasure
        {x | productive I ρ proposal a (PMF.seqHistory h) x = true}).toReal)
    (charge : List Ω → Ω → ℝ) (hcharge : ∀ h x, 0 ≤ charge h x)
    (c : ℝ) (hc : 0 ≤ c)
    (hcost : ∀ t, t < n → ∀ h : Fin t → Ω,
      h ∈ (PMF.seqProcess (responseStep law) t).support →
      I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground →
      (∑' x, law (PMF.seqHistory h) x * ENNReal.ofReal (charge (PMF.seqHistory h) x)) ≤
        ENNReal.ofReal c) :
    (∑' h, PMF.seqProcess (responseStep law) n h *
      ENNReal.ofReal (accruedBill (stoppedBill I ρ proposal charge) (PMF.seqHistory h))) ≤
      ENNReal.ofReal (c * min (n : ℝ) ((r : ℝ) / p)) := by
  apply (accruedBill_le_binomial_sum_discrete I ρ proposal law a r n hr p hp
    charge hcharge c hc hcost).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hc
  apply le_min
  · calc
      (∑ t ∈ Finset.range n, (ProbabilityTheory.binomial t p).real (Set.Iio r)) ≤
          ∑ _t ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun _ _ => measureReal_le_one)
      _ = (n : ℝ) := by simp
  · exact Cslib.Probability.sum_binomial_real_Iio_le n r hp0

end Cslib.Probability.StochasticOracle.AdaptiveSelection
