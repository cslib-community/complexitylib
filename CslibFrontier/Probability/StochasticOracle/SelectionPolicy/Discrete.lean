/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Execution
public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Output
public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.DiscreteCost
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.Tactic

/-!
# Stopped batch-selecting policies with arbitrary discrete responses

The source upper policy of [Wang2027], Theorem 5(1), constructed by selecting a
batch, drawing its actual response, and retaining locally certified proposals.
Both components remain in the transcript. Completion emits an absorbing halt
record, so subsequent records have zero charge and reveal no information.

At supported incomplete prefixes, batchwise productivity, conditional invoice
means and actual durations imply a joint certified-output/deadline probability
bound and finite stopped-token survival-sum and budget/mean bounds. Raw recorded
invoices are proved equal to coverage-stopped billing on actual executions.

This is a finite-horizon PMF semantic construction, without a finite response
alphabet or a claim that arbitrary stochastic kernels compile into native machines.
The finite-table conversion is in `Discrete.FiniteTable`.

## Main definitions

* `retainingLaw`: actual batch-then-response execution with absorbing halt records.
* `UpperBounds`: primitive contracts on supported selected batches at reached incomplete prefixes.

## Main results

* `upper_conditional`: transfer batchwise progress and invoice envelopes to the joint law.
* `certified_success`: certified retained coverage within the actual physical deadline.
* `cost_le_binomial_sum`, `cost_le_mean`: actual raw invoice bounds.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
open AdaptiveSelection PartialCover MeasureTheory
open scoped ENNReal
variable {B R E J : Type} [DecidableEq E] [DecidableEq J]

/-- Select a batch before completion and halt when the actual retained family covers. -/
@[expose] def retainingChoose (I : Instance E J) (ρ : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B) (h : List (Record B R)) : PMF (Option B) := by
  classical
  exact if I.covered (selected I ρ (recordProposals propose) h) = I.ground
    then PMF.pure none else (select h).map some

/-- The retaining policy calls the same execution kernel as arbitrary competitors. -/
@[expose] def retainingLaw (I : Instance E J) (ρ : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (respond : List (Record B R) → B → PMF R)
    (h : List (Record B R)) : PMF (Record B R) :=
  policyLaw (retainingChoose I ρ propose select) respond h

open scoped Classical in
/-- Prior halts and retained completion absorb; otherwise the selected batch is
sampled before its response. This characterizes the shared execution specialization. -/
theorem retainingLaw_eq (I : Instance E J) (ρ : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (respond : List (Record B R) → B → PMF R)
    (h : List (Record B R)) :
    retainingLaw I ρ propose select respond h =
      if none ∈ h ∨ I.covered (selected I ρ (recordProposals propose) h) = I.ground
      then PMF.pure none
      else (select h).bind fun b => (respond h b).map fun x => some (b, x) := by
  classical
  by_cases hn : none ∈ h
  · simp [retainingLaw, policyLaw, hn]
  · by_cases hc : I.covered (selected I ρ (recordProposals propose) h) = I.ground <;>
      simp [retainingLaw, policyLaw, responseRecord, retainingChoose, hn, hc, PMF.bind_map,
        Function.comp_def]

/-- Every supported incomplete prefix is active: the actual policy has not halted. -/
theorem retaining_active
    (I : Instance E J) (ρ : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (respond : List (Record B R) → B → PMF R)
    (n : ℕ) (h : Fin n → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) n).support)
    (hc : I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory h)) ≠ I.ground) :
    none ∉ PMF.seqHistory h := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [PMF.seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
    obtain ⟨g, hg, x, hx, rfl⟩ := hh
    rw [PMF.seqHistory_snoc] at hc ⊢
    cases x with
    | none =>
      have hc' : I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory g)) ≠
          I.ground := by
        simpa only [selected, recordProposals, Instance.retain] using hc
      have hs := ih g hg hc'
      have hz : retainingLaw I ρ propose select respond (PMF.seqHistory g) none = 0 := by
        simp [retainingLaw_eq, hs, hc', PMF.bind_apply, PMF.map_apply]
      change retainingLaw I ρ propose select respond (PMF.seqHistory g) none ≠ 0 at hx
      exact (hx hz).elim
    | some z =>
      have hs : none ∉ PMF.seqHistory g := by
        intro hn
        have he : responseStep (retainingLaw I ρ propose select respond) n g =
            PMF.pure none := by simp [responseStep, retainingLaw_eq, hn]
        rw [he] at hx
        simp at hx
      simpa using hs

/-- Supported selected-batch productivity envelopes imply the joint response
law's progress bound. Selection occurs before sampling the actual response. -/
theorem conditional_progress (I : Instance E J) (ρ : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (respond : List (Record B R) → B → PMF R)
    (h : List (Record B R)) (hs : none ∉ h)
    (hc : I.covered (selected I ρ (recordProposals propose) h) ≠ I.ground)
    (a : ℕ) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ b ∈ (select h).support, (p : ℝ) ≤ ((respond h b).toOuterMeasure
      {x | productive I ρ (recordProposals propose) a h (some (b, x)) = true}).toReal) :
    (p : ℝ) ≤ ((retainingLaw I ρ propose select respond h).toOuterMeasure
      {x | productive I ρ (recordProposals propose) a h x = true}).toReal := by
  classical
  rw [retainingLaw_eq, ite_eq_right (by simp [hs, hc])]
  have hu : (select h).toOuterMeasure Set.univ = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)
  have hm := PMF.toOuterMeasure_bind_ge_mul (select h)
    (fun b => (respond h b).map fun x => some (b, x)) Set.univ
    {x | productive I ρ (recordProposals propose) a h x = true}
    p.2.1 (s₁ := 1) (by simp [hu]) (by
      intro b hb _
      simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq] using hp b hb)
  simpa only [one_mul] using hm

/-- Supported selected-batch mean invoices imply the joint law's conditional
mean bound. Null selections impose no invoice condition. -/
theorem conditional_cost (I : Instance E J) (ρ : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (respond : List (Record B R) → B → PMF R)
    (h : List (Record B R)) (hs : none ∉ h)
    (hc : I.covered (selected I ρ (recordProposals propose) h) ≠ I.ground)
    (charge : List (Record B R) → B → R → ℝ) (c : ℝ)
    (hb : ∀ b ∈ (select h).support,
      (∑' x, respond h b x * ENNReal.ofReal (charge h b x)) ≤ ENNReal.ofReal c) :
    (∑' x, retainingLaw I ρ propose select respond h x *
      ENNReal.ofReal (recordResource charge h x)) ≤ ENNReal.ofReal c := by
  classical
  rw [retainingLaw_eq, ite_eq_right (by simp [hs, hc]), PMF.tsum_bind_mul]
  simp_rw [PMF.tsum_map_mul, recordResource_some]
  exact PMF.tsum_mul_le_of_support (select h) hb

/-- The raw actual policy invoice equals coverage-stopped billing on supported
executions: after coverage only the zero-charge halt record can be sampled. -/
theorem accruedBill_eq_stopped (I : Instance E J) (ρ : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (respond : List (Record B R) → B → PMF R)
    (charge : List (Record B R) → B → R → ℝ)
    (n : ℕ) (h : Fin n → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) n).support) :
    accruedBill (recordResource charge) (PMF.seqHistory h) =
      accruedBill (stoppedBill I ρ (recordProposals propose) (recordResource charge))
        (PMF.seqHistory h) := by
  classical
  apply accruedBill_congr_on_support _ _ _ ?_ n h hh
  intro t g _ x hx
  by_cases hc : I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory g)) =
      I.ground
  · have he : responseStep (retainingLaw I ρ propose select respond) t g = PMF.pure none := by
      simp [responseStep, retainingLaw_eq, hc]
    rw [he] at hx
    have hx' : x = none := by simpa using hx
    subst x
    simp [stoppedBill, hc]
  · simp [stoppedBill, hc]

section Contracts
variable (I : Instance E J) (ρ : ℝ)
  (propose : List (Record B R) → B → R → List (Finset J))
  (select : List (Record B R) → PMF B)
  (respond : List (Record B R) → B → PMF R)
  (charge duration : List (Record B R) → B → R → ℝ)

/-- Primitive source envelopes at actually reached incomplete prefixes and
actually selected batches. No achieved probability or total-resource bound is a field. -/
structure UpperBounds (u a : ℕ) (p c ell : ℝ) : Prop where
  /-- Realized token charges are nonnegative. -/
  charge_nonneg : ∀ h b x, 0 ≤ charge h b x
  /-- Supported selected batches have conditional productivity at least `p`. -/
  progress : ∀ t, t < u → ∀ h : Fin t → Record B R,
    h ∈ (PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) t).support →
    I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory h)) ≠ I.ground →
    ∀ b ∈ (select (PMF.seqHistory h)).support,
      p ≤ ((respond (PMF.seqHistory h) b).toOuterMeasure
        {x | productive I ρ (recordProposals propose) a (PMF.seqHistory h) (some (b, x)) =
          true}).toReal
  /-- Only issued batches need a conditional token-mean envelope. -/
  cost : ∀ t, t < u → ∀ h : Fin t → Record B R,
    h ∈ (PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) t).support →
    I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory h)) ≠ I.ground →
    ∀ b ∈ (select (PMF.seqHistory h)).support,
      (∑' x, respond (PMF.seqHistory h) b x *
        ENNReal.ofReal (charge (PMF.seqHistory h) b x)) ≤ ENNReal.ofReal c
  /-- Actual supported batch durations, rather than configured cutoffs, are bounded. -/
  time : ∀ t, t < u → ∀ h : Fin t → Record B R,
    h ∈ (PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) t).support →
    I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory h)) ≠ I.ground →
    ∀ b ∈ (select (PMF.seqHistory h)).support,
      ∀ x ∈ (respond (PMF.seqHistory h) b).support,
        0 ≤ duration (PMF.seqHistory h) b x ∧ duration (PMF.seqHistory h) b x ≤ ell

/-- The source batch envelopes give the conditional progress and invoice
bounds for the actual joint response law at every reached incomplete prefix. -/
theorem upper_conditional (u a : ℕ) (p : Set.Icc (0 : ℝ) 1) (c ell : ℝ)
    (H : UpperBounds I ρ propose select respond charge duration u a p c ell)
    (t : ℕ) (ht : t < u) (h : Fin t → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) t).support)
    (hc : I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory h)) ≠ I.ground) :
    ((p : ℝ) ≤ ((retainingLaw I ρ propose select respond (PMF.seqHistory h)).toOuterMeasure
      {x | productive I ρ (recordProposals propose) a (PMF.seqHistory h) x = true}).toReal) ∧
    ((∑' x, retainingLaw I ρ propose select respond (PMF.seqHistory h) x *
      ENNReal.ofReal (recordResource charge (PMF.seqHistory h) x)) ≤ ENNReal.ofReal c) := by
  have hs := retaining_active I ρ propose select respond t h hh hc
  exact ⟨conditional_progress I ρ propose select respond (PMF.seqHistory h) hs hc a p
    (H.progress t ht h hh hc), conditional_cost I ρ propose select respond
    (PMF.seqHistory h) hs hc charge c (H.cost t ht h hh hc)⟩

/-- Actual retained coverage of the stopped batch-selecting policy satisfies the
source binomial success bound, with arbitrary discrete batches and responses. -/
theorem completion_bound (u a r : ℕ) (hr : I.ground.card ≤ a * r)
    (p : Set.Icc (0 : ℝ) 1) (c ell : ℝ)
    (H : UpperBounds I ρ propose select respond charge duration u a p c ell) :
    1 - (ProbabilityTheory.binomial u p).real (Set.Iio r) ≤
      ((PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) u).toOuterMeasure
        {h | I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory h)) =
          I.ground}).toReal := by
  apply binomial_le_completion_discrete I ρ (recordProposals propose)
    (retainingLaw I ρ propose select respond) a r u hr p
  intro t ht h hh hc
  exact (upper_conditional I ρ propose select respond charge duration u a p c ell
    H t ht h hh hc).1

/-- Raw actual invoices of the stopped policy obey the binomial survival sum.
After completion only zero-charge halt records are sampled; no score replacement
or expected-total-cost assumption is part of the source contract. -/
theorem cost_le_binomial_sum (u a r : ℕ) (hr : I.ground.card ≤ a * r)
    (p : Set.Icc (0 : ℝ) 1) (c ell : ℝ) (hc : 0 ≤ c)
    (H : UpperBounds I ρ propose select respond charge duration u a p c ell) :
    (∑' h, PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) u h *
      ENNReal.ofReal (accruedBill (recordResource charge) (PMF.seqHistory h))) ≤
      ENNReal.ofReal (c * ∑ t ∈ Finset.range u,
        (ProbabilityTheory.binomial t p).real (Set.Iio r)) := by
  rw [PMF.tsum_mul_congr_support _ (fun h hh =>
    congrArg ENNReal.ofReal (accruedBill_eq_stopped I ρ propose select respond charge u h hh))]
  apply accruedBill_le_binomial_sum_discrete I ρ (recordProposals propose)
    (retainingLaw I ρ propose select respond) a r u hr p
  · intro t ht h hh hn
    exact (upper_conditional I ρ propose select respond charge duration u a p c ell
      H t ht h hh hn).1
  · exact recordResource_nonneg charge H.charge_nonneg
  · exact hc
  · intro t ht h hh hn
    exact (upper_conditional I ρ propose select respond charge duration u a p c ell
      H t ht h hh hn).2

/-- The actual stopped policy has the source finite-budget/mean token envelope. -/
theorem cost_le_mean (u a r : ℕ) (hr : I.ground.card ≤ a * r)
    (p : Set.Icc (0 : ℝ) 1) (hp0 : 0 < (p : ℝ)) (c ell : ℝ) (hc : 0 ≤ c)
    (H : UpperBounds I ρ propose select respond charge duration u a p c ell) :
    (∑' h, PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) u h *
      ENNReal.ofReal (accruedBill (recordResource charge) (PMF.seqHistory h))) ≤
      ENNReal.ofReal (c * min (u : ℝ) ((r : ℝ) / p)) := by
  rw [PMF.tsum_mul_congr_support _ (fun h hh =>
    congrArg ENNReal.ofReal (accruedBill_eq_stopped I ρ propose select respond charge u h hh))]
  apply accruedBill_le_mean_discrete I ρ (recordProposals propose)
    (retainingLaw I ρ propose select respond) a r u hr p hp0
  · intro t ht h hh hn
    exact (upper_conditional I ρ propose select respond charge duration u a p c ell
      H t ht h hh hn).1
  · exact recordResource_nonneg charge H.charge_nonneg
  · exact hc
  · intro t ht h hh hn
    exact (upper_conditional I ρ propose select respond charge duration u a p c ell
      H t ht h hh hn).2

/-- Actual physical duration is bounded on every supported finite execution,
including the zero-duration halt records after completion. -/
theorem duration_bound (u a : ℕ) (p c ell : ℝ) (hell : 0 ≤ ell)
    (H : UpperBounds I ρ propose select respond charge duration u a p c ell)
    (n : ℕ) (hn : n ≤ u) (h : Fin n → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) n).support) :
    0 ≤ accruedBill (recordResource duration) (PMF.seqHistory h) ∧
      accruedBill (recordResource duration) (PMF.seqHistory h) ≤ (n : ℝ) * ell := by
  classical
  induction n with
  | zero => simp [accruedBill]
  | succ n ih =>
    simp only [PMF.seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
    obtain ⟨g, hg, x, hx, rfl⟩ := hh
    have hi := ih (by omega) g hg
    have ht : n < u := by omega
    have hd : 0 ≤ recordResource duration (PMF.seqHistory g) x ∧
        recordResource duration (PMF.seqHistory g) x ≤ ell := by
      by_cases hs : none ∈ PMF.seqHistory g ∨
          I.covered (selected I ρ (recordProposals propose) (PMF.seqHistory g)) = I.ground
      · have he : responseStep (retainingLaw I ρ propose select respond) n g =
            PMF.pure none := by simp [responseStep, retainingLaw_eq, hs]
        rw [he] at hx
        have hx' : x = none := by simpa using hx
        subst x
        exact ⟨le_rfl, hell⟩
      · simp only [responseStep, retainingLaw_eq, ite_eq_right hs,
          PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hx
        obtain ⟨b, hb, y, hy, rfl⟩ := hx
        exact H.time n ht g hg (not_or.mp hs).2 b hb y hy
    rw [PMF.seqHistory_snoc, accruedBill]
    refine ⟨add_nonneg hi.1 hd.1, ?_⟩
    push_cast
    nlinarith [hi.2, hd.2]

/-- The actual retained output is certified and returned within the supplied
deadline with the source binomial probability. Latency is derived from supported
batch durations and the finite budget, rather than assumed at the terminal event. -/
theorem certified_success (u a r : ℕ) (hr : I.ground.card ≤ a * r)
    (p : Set.Icc (0 : ℝ) 1) (c ell D : ℝ) (hell : 0 ≤ ell) (hD : (u : ℝ) * ell ≤ D)
    (H : UpperBounds I ρ propose select respond charge duration u a p c ell) :
    1 - (ProbabilityTheory.binomial u p).real (Set.Iio r) ≤
      ((PMF.seqProcess (responseStep (retainingLaw I ρ propose select respond)) u).toOuterMeasure
        {h | CertifiedOutput I ρ D duration (PMF.seqHistory h)
          (selected I ρ (recordProposals propose) (PMF.seqHistory h))}).toReal := by
  apply (completion_bound I ρ propose select respond charge duration u a r hr p c ell H).trans
  apply ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
  apply PMF.toOuterMeasure_mono
  intro h hh
  obtain ⟨hc, hs⟩ := hh
  have hcert := selected_bound I ρ (recordProposals propose) (PMF.seqHistory h)
  rw [hc] at hcert
  exact ⟨hc, hcert, (duration_bound I ρ propose select respond charge duration u a p c ell
    hell H u le_rfl h hs).2.trans hD⟩

end Contracts

end Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
