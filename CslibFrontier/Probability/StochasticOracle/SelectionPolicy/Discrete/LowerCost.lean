/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.Competitor
public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.DiscreteCost
public import CslibFrontier.Probability.StochasticOracle.AdaptiveLowerCost
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Markov
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.Tactic

/-!
# Token lower bounds for arbitrary discrete selection-only competitors

The finite-horizon cost argument of [Wang2027], Theorem 5(2), for actual PMF
batch selection and randomized final extraction. Revealed progress uses all valid
proposals, including locally unretained ones. Provenance constrains only outputs
counted as certified successes; arbitrary failed masks remain permitted.

The bound permits infinite expected token cost. Its premises are local source
progress, revealed-size and invoice envelopes plus selection-only provenance;
no aggregate count, cost lower bound or integrability is assumed.

## Main definitions

* `LowerBounds`: local source limitations and successful-only output provenance.

## Main results

* `conditional_accounting`: progress/issued and invoice/issued inequalities from selected batches.
* `lower_cost`: the actual extended token expectation is at least `eta * r * c / p`.

This module proves the token part, not the necessary deadline-binomial bound or
native realization of arbitrary behavioral policies.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
open AdaptiveSelection PartialCover MeasureTheory
open scoped ENNReal
variable {B R E J : Type} [DecidableEq E] [DecidableEq J]

private theorem indicator_mean {α : Type*} (q : PMF α) (test : α → Bool) :
    (∑' x, q x * ENNReal.ofReal (if test x then (1 : ℝ) else 0)) =
      q.toOuterMeasure {x | test x = true} := by
  classical
  rw [PMF.toOuterMeasure_eq_tsum_mul_indicator]
  apply tsum_congr
  intro x
  by_cases hx : test x = true <;> simp [hx]

section Source
variable (I : Instance E J)
  (propose : List (Record B R) → B → R → List (Finset J))
  (choose : List (Record B R) → PMF (Option B))
  (respond : List (Record B R) → B → PMF R)
  (output : List (Record B R) → PMF (Finset J))
  (charge duration : List (Record B R) → B → R → ℝ)

/-- Primitive limitations of a fixed oracle against one arbitrary competitor.
Only positive-probability chosen batches and successful output masks are constrained. -/
structure LowerBounds (u b : ℕ) (p c ρ D : ℝ) : Prop
    extends ProgressBounds I propose choose respond output duration u b p ρ D where
  /-- Actual realized token charges are nonnegative. -/
  charge_nonneg : ∀ h i x, 0 ≤ charge h i x
  /-- Issued batches have a conditional expected invoice of at least `c`. -/
  cost : ∀ t, t < u → ∀ h : Fin t → Record B R,
    h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) t).support →
    none ∉ PMF.seqHistory h → ∀ i, some i ∈ (choose (PMF.seqHistory h)).support →
      ENNReal.ofReal c ≤ ∑' x, respond (PMF.seqHistory h) i x *
        ENNReal.ofReal (charge (PMF.seqHistory h) i x)

/-- Batchwise source limitations yield the actual conditional progress/issued
and invoice/issued inequalities, including randomized halt decisions. -/
theorem conditional_accounting (u b : ℕ) (p c ρ D : ℝ) (hp : 0 ≤ p)
    (H : LowerBounds I propose choose respond output charge duration u b p c ρ D)
    (t : ℕ) (ht : t < u) (h : Fin t → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) t).support) :
    ((policyLaw choose respond (PMF.seqHistory h)).toOuterMeasure
      {x | reveals I (recordProposals propose) (PMF.seqHistory h) x = true} ≤
      ENNReal.ofReal p * (policyLaw choose respond (PMF.seqHistory h)).toOuterMeasure
        {x | issued (PMF.seqHistory h) x = true}) ∧
    (ENNReal.ofReal c * (policyLaw choose respond (PMF.seqHistory h)).toOuterMeasure
        {x | issued (PMF.seqHistory h) x = true} ≤
      ∑' x, policyLaw choose respond (PMF.seqHistory h) x *
        ENNReal.ofReal (recordResource charge (PMF.seqHistory h) x)) := by
  constructor
  · exact conditional_progress_le_issued I propose choose respond output duration
      u b p ρ D hp H.toProgressBounds t ht h hh
  · classical
    by_cases hn : none ∈ PMF.seqHistory h
    · simp [policyLaw, hn, PMF.toOuterMeasure_pure_apply, issued,
        PMF.pure_apply, ite_mul]
    · let κ := responseRecord respond (PMF.seqHistory h)
      have hlaw : policyLaw choose respond (PMF.seqHistory h) =
          (choose (PMF.seqHistory h)).bind κ := by
        rw [policyLaw, ite_eq_right hn]
      simp only [hlaw, PMF.toOuterMeasure_bind_apply, κ, responseRecord_issued, PMF.tsum_bind_mul]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_le_tsum
      intro q
      cases q with
      | none => simp [responseRecord, PMF.pure_apply, ite_mul]
      | some q =>
        by_cases hq : some q ∈ (choose (PMF.seqHistory h)).support
        · have hm := mul_le_mul_of_nonneg_left (H.cost t ht h hh hn q hq)
            (show 0 ≤ choose (PMF.seqHistory h) (some q) from zero_le)
          dsimp only [κ, responseRecord]
          rw [PMF.tsum_map_mul]
          simpa only [Option.isSome_some, ite_true, mul_one, one_mul,
            recordResource_some, mul_comm] using hm
        · have hz := (PMF.apply_eq_zero_iff _ _).mpr hq
          simp [hz]

/-- A success level forces the corresponding first moment of actual revealed
progress. Markov's inequality is applied to the actual count, not a supplied bridge. -/
theorem success_mul_count_le (u b r : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p c ρ D η : ℝ) (hη0 : 0 ≤ η)
    (H : LowerBounds I propose choose respond output charge duration u b p c ρ D)
    (hη : ENNReal.ofReal η ≤ (outputLaw choose respond output u).toOuterMeasure
      {z | CertifiedOutput I ρ D duration z.history z.returned}) :
    ENNReal.ofReal (η * r) ≤
      ∑' h, PMF.seqProcess (responseStep (policyLaw choose respond)) u h *
        (count (reveals I (recordProposals propose)) (PMF.seqHistory h) : ℝ≥0∞) := by
  have ht := hη.trans (success_le_count_tail I propose choose respond output duration
    u b r hr p ρ D H.toProgressBounds)
  have hm := PMF.mul_toOuterMeasure_le_tsum
    (PMF.seqProcess (responseStep (policyLaw choose respond)) u)
    (fun h => (count (reveals I (recordProposals propose)) (PMF.seqHistory h) : ℝ≥0∞))
    (r : ℝ≥0∞)
  rw [ENNReal.ofReal_mul hη0, ENNReal.ofReal_natCast]
  apply le_trans _ hm
  have hx := mul_le_mul_of_nonneg_left ht (show (0 : ℝ≥0∞) ≤ r from zero_le)
  simpa only [Nat.cast_le, mul_comm] using hx

/-- Source token lower bound for every actual arbitrary discrete competitor.
Only its achieved success level is supplied; infinite expected invoices are
allowed, and no integrability or aggregate expected-cost premise is needed. -/
theorem lower_cost (u b r : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p c ρ D η : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (hη0 : 0 ≤ η)
    (H : LowerBounds I propose choose respond output charge duration u b p c ρ D)
    (hη : ENNReal.ofReal η ≤ (outputLaw choose respond output u).toOuterMeasure
      {z | CertifiedOutput I ρ D duration z.history z.returned}) :
    ENNReal.ofReal (η * r * c / p) ≤
      ∑' h, PMF.seqProcess (responseStep (policyLaw choose respond)) u h *
        ENNReal.ofReal (accruedBill (recordResource charge) (PMF.seqHistory h)) := by
  classical
  let K := policyLaw choose respond
  let μ := fun t => PMF.seqProcess (responseStep K) t
  let marginal := fun (bill : List (Record B R) → Record B R → ℝ) (t : ℕ) =>
    ∑' h, μ t h * ∑' x, K (PMF.seqHistory h) x * ENNReal.ofReal (bill (PMF.seqHistory h) x)
  let P := marginal (fun h x => if reveals I (recordProposals propose) h x then 1 else 0)
  let A := marginal (fun h x => if issued h x then 1 else 0)
  let C := marginal (recordResource charge)
  let total := ∑' h, μ u h *
    ENNReal.ofReal (accruedBill (recordResource charge) (PMF.seqHistory h))
  change ENNReal.ofReal (η * r * c / p) ≤ total
  have hCsum : total = ∑ t ∈ Finset.range u, C t :=
    accruedBill_eq_sum_discrete K (recordResource charge)
      (recordResource_nonneg charge H.charge_nonneg) u
  have hPA (t : ℕ) (ht : t < u) : P t ≤ ENNReal.ofReal p * A t := by
    calc
      P t = ∑' h, μ t h * (K (PMF.seqHistory h)).toOuterMeasure
          {x | reveals I (recordProposals propose) (PMF.seqHistory h) x = true} := by
        dsimp only [P, marginal]
        simp_rw [indicator_mean]
      _ ≤ ∑' h, μ t h * (ENNReal.ofReal p * (K (PMF.seqHistory h)).toOuterMeasure
          {x | issued (PMF.seqHistory h) x = true}) :=
        PMF.tsum_mul_mono_support (μ t) (fun h hh =>
          (conditional_accounting I propose choose respond output charge duration
            u b p c ρ D hp.le H t ht h hh).1)
      _ = ENNReal.ofReal p * A t := by
        dsimp only [A, marginal]
        simp_rw [indicator_mean]
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro h
        ac_rfl
  have hCA (t : ℕ) (ht : t < u) : ENNReal.ofReal c * A t ≤ C t := by
    calc
      ENNReal.ofReal c * A t = ∑' h, μ t h *
          (ENNReal.ofReal c * (K (PMF.seqHistory h)).toOuterMeasure
            {x | issued (PMF.seqHistory h) x = true}) := by
        dsimp only [A, marginal]
        simp_rw [indicator_mean]
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro h
        ac_rfl
      _ ≤ C t := PMF.tsum_mul_mono_support (μ t) (fun h hh =>
        (conditional_accounting I propose choose respond output charge duration
          u b p c ρ D hp.le H t ht h hh).2)
  have hPsum : (∑ t ∈ Finset.range u, P t) =
      ∑' h, μ u h * (count (reveals I (recordProposals propose)) (PMF.seqHistory h) : ℝ≥0∞) := by
    have he : (∑' h, μ u h * ENNReal.ofReal (accruedBill
          (fun h x => if reveals I (recordProposals propose) h x then 1 else 0)
          (PMF.seqHistory h))) = ∑ t ∈ Finset.range u, P t :=
      accruedBill_eq_sum_discrete K _ (by intro h x; split_ifs <;> norm_num) u
    simpa only [accrued_indicator_eq_count, ENNReal.ofReal_natCast] using he.symm
  have hcount : ENNReal.ofReal (η * r) ≤ ∑ t : Fin u, P t.val := by
    have hs := success_mul_count_le I propose choose respond output charge duration
      u b r hr p c ρ D η hη0 H hη
    rw [← hPsum] at hs
    rw [Fin.sum_univ_eq_sum_range]
    exact hs
  have hm := marginal_cost_mul_le (fun t : Fin u => A t.val)
    (fun t : Fin u => P t.val) (fun t : Fin u => C t.val)
    (ENNReal.ofReal (η * r)) (ENNReal.ofReal p) (ENNReal.ofReal c) zero_le zero_le
    hcount (fun t => hPA t.val t.isLt) (fun t => hCA t.val t.isLt)
  rw [ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_mul' hc]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mpr
  rw [hCsum]
  simpa only [Fin.sum_univ_eq_sum_range] using hm

end Source
end Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
