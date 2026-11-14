/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Execution
public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Output
public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.Discrete
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.Tactic

/-!
# Actual selection-only competitors and revealed progress

An arbitrary discrete batch policy executes its chosen batch, then samples its
final output. Progress, revealed-size and successful-output provenance bounds
force enough actual revealed turns for success. Failed output masks are unrestricted.
These interfaces assume no token-cost or latency envelope.

## Main definitions

* `Outcome`, `outputLaw`: actual execution and randomized extraction.
* `Admissible`: successful-only provenance, independent of source envelopes.
* `expectedCost`, `successProbability`, `DeadlineFeasible`: actual resource/output observations.
* `ProgressBounds`: local progress/size limits and successful-only provenance.

## Main results

* `revealed_card_le`, `success_count`: deterministic count certificates on actual support.
* `success_le_count_tail`: the corresponding successful-output probability bound.
* `outputLaw_pure`, `outputLaw_event_le`: deterministic extraction and event-precondition bounds.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
open AdaptiveSelection PartialCover MeasureTheory
open scoped ENNReal
variable {B R E J : Type} [DecidableEq E] [DecidableEq J]

/-- Actual finite transcript and the family sampled by the policy's extraction kernel. -/
structure Outcome (B R J : Type) where
  /-- Complete newest-first call/halt transcript. -/
  history : List (Record B R)
  /-- The actual returned candidate family, whether successful or failed. -/
  returned : Finset J

/-- Execute the policy, then sample its output conditional on the actual transcript. -/
@[expose] def outputLaw
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (output : List (Record B R) → PMF (Finset J)) (u : ℕ) : PMF (Outcome B R J) :=
  (PMF.seqProcess (responseStep (policyLaw choose respond)) u).bind fun h =>
    (output (PMF.seqHistory h)).map fun C => ⟨PMF.seqHistory h, C⟩

/-- Extended expectation of the actual accrued invoices over the fixed turn budget. -/
@[expose] def expectedCost
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (charge : List (Record B R) → B → R → ℝ) (u : ℕ) : ℝ≥0∞ :=
  ∑' h, PMF.seqProcess (responseStep (policyLaw choose respond)) u h *
    ENNReal.ofReal (accruedBill (recordResource charge) (PMF.seqHistory h))

/-- Probability of the actual randomized output meeting coverage, dual certification
and the accounted physical deadline. -/
@[expose] def successProbability (I : Instance E J)
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (output : List (Record B R) → PMF (Finset J))
    (duration : List (Record B R) → B → R → ℝ) (u : ℕ) (ρ D : ℝ) : ℝ :=
  ((outputLaw choose respond output u).toOuterMeasure
    {z | CertifiedOutput I ρ D duration z.history z.returned}).toReal

/-- Every supported prefix finishes its issued batches by the physical deadline. -/
@[expose] def DeadlineFeasible
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (duration : List (Record B R) → B → R → ℝ) (u : ℕ) (D : ℝ) : Prop :=
  ∀ t, t ≤ u → ∀ h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) t).support,
    accruedBill (recordResource duration) (PMF.seqHistory h) ≤ D

omit [DecidableEq J] in
/-- Deterministic final extraction preserves the actual joint transcript/output law. -/
theorem outputLaw_pure
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (returned : List (Record B R) → Finset J) (u : ℕ) :
    outputLaw choose respond (fun h => PMF.pure (returned h)) u =
      (PMF.seqProcess (responseStep (policyLaw choose respond)) u).map
        (fun h => (⟨PMF.seqHistory h, returned (PMF.seqHistory h)⟩ : Outcome B R J)) := by
  simp only [outputLaw, PMF.pure_map]
  rfl

omit [DecidableEq J] in
/-- An event in the actual randomized output can occur only on its supported
execution precondition. No constraint is needed on unsupported extraction masks. -/
theorem outputLaw_event_le
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (output : List (Record B R) → PMF (Finset J)) (u : ℕ)
    (pre : Set (Fin u → Record B R)) (event : Set (Outcome B R J))
    (H : ∀ h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) u).support,
      ∀ C ∈ (output (PMF.seqHistory h)).support,
        (⟨PMF.seqHistory h, C⟩ : Outcome B R J) ∈ event → h ∈ pre) :
    (outputLaw choose respond output u).toOuterMeasure event ≤
      (PMF.seqProcess (responseStep (policyLaw choose respond)) u).toOuterMeasure pre := by
  classical
  unfold outputLaw
  simpa only [mul_one] using PMF.toOuterMeasure_bind_le_mul_ennreal
    (PMF.seqProcess (responseStep (policyLaw choose respond)) u)
    (fun h => (output (PMF.seqHistory h)).map fun C => (⟨PMF.seqHistory h, C⟩ : Outcome B R J))
    pre event le_rfl (fun _ _ _ => PMF.toOuterMeasure_le_one _ _) (by
      intro h hh hn
      rw [PMF.toOuterMeasure_map_apply]
      apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
      apply Set.disjoint_left.mpr
      intro C hC hs
      exact hn (H h hh C hC hs))

section Source
variable (I : Instance E J)
  (propose : List (Record B R) → B → R → List (Finset J))
  (choose : List (Record B R) → PMF (Option B))
  (respond : List (Record B R) → B → PMF R)
  (output : List (Record B R) → PMF (Finset J))
  (duration : List (Record B R) → B → R → ℝ)

/-- Selection-only provenance for successfully certified actual outputs.
Failed masks are unrestricted, and no progress, cost or time bound is assumed. -/
@[expose] def Admissible (u : ℕ) (ρ D : ℝ) : Prop :=
  ∀ h : Fin u → Record B R,
    h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) u).support →
    ∀ C ∈ (output (PMF.seqHistory h)).support,
      CertifiedOutput I ρ D duration (PMF.seqHistory h) C →
      C ⊆ proposedSets (recordProposals propose) (PMF.seqHistory h)

/-- Primitive progress limitations and provenance for an actual competitor.
Only supported selected batches and successfully certified outputs are constrained. -/
structure ProgressBounds (u b : ℕ) (p ρ D : ℝ) : Prop where
  /-- A supported selected batch reveals new information with probability at most `p`. -/
  progress : ∀ t, t < u → ∀ h : Fin t → Record B R,
    h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) t).support →
    none ∉ PMF.seqHistory h → ∀ i, some i ∈ (choose (PMF.seqHistory h)).support →
    ((respond (PMF.seqHistory h) i).toOuterMeasure
      {x | reveals I (recordProposals propose) (PMF.seqHistory h) (some (i, x)) = true}).toReal ≤ p
  /-- A supported response can reveal only `b` new ground elements. -/
  coverage : ∀ t, t < u → ∀ h : Fin t → Record B R,
    h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) t).support →
    none ∉ PMF.seqHistory h → ∀ i, some i ∈ (choose (PMF.seqHistory h)).support →
    ∀ x ∈ (respond (PMF.seqHistory h) i).support,
      (revealed I (recordProposals propose) (some (i, x) :: PMF.seqHistory h) \
        revealed I (recordProposals propose) (PMF.seqHistory h)).card ≤ b
  /-- Successful extraction can use only actually proposed candidates; failed
  masks, even fabricated ones, need no provenance certificate. -/
  provenance : Admissible I propose choose respond output duration u ρ D

/-- A batchwise progress envelope averages over actual randomized selection,
with no progress contribution from a halt or a previously halted history. -/
theorem conditional_progress_le_issued (u b : ℕ) (p ρ D : ℝ) (hp : 0 ≤ p)
    (H : ProgressBounds I propose choose respond output duration u b p ρ D)
    (t : ℕ) (ht : t < u) (h : Fin t → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) t).support) :
    (policyLaw choose respond (PMF.seqHistory h)).toOuterMeasure
      {x | reveals I (recordProposals propose) (PMF.seqHistory h) x = true} ≤
      ENNReal.ofReal p * (policyLaw choose respond (PMF.seqHistory h)).toOuterMeasure
        {x | issued (PMF.seqHistory h) x = true} := by
  classical
  by_cases hn : none ∈ PMF.seqHistory h
  · simp [policyLaw, hn, PMF.toOuterMeasure_pure_apply, record_reveals_none, issued]
  · let κ := responseRecord respond (PMF.seqHistory h)
    have hlaw : policyLaw choose respond (PMF.seqHistory h) =
        (choose (PMF.seqHistory h)).bind κ := by
      rw [policyLaw, ite_eq_right hn]
    simp only [hlaw, PMF.toOuterMeasure_bind_apply, κ, responseRecord_issued]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_le_tsum
    intro q
    cases q with
    | none => simp [responseRecord, PMF.toOuterMeasure_pure_apply, record_reveals_none]
    | some q =>
      by_cases hq : some q ∈ (choose (PMF.seqHistory h)).support
      · have hP := (ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) hp).mpr
          (H.progress t ht h hh hn q hq)
        have hm := mul_le_mul_of_nonneg_left hP
          (show 0 ≤ choose (PMF.seqHistory h) (some q) from zero_le)
        simpa [κ, responseRecord, PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq,
          mul_comm] using hm
      · have hz := (PMF.apply_eq_zero_iff _ _).mpr hq
        simp [hz]

/-- The actual revealed family satisfies the size/count invariant on supported
prefixes. Its induction reuses the deterministic one-response size lemma. -/
theorem revealed_card_le (u b : ℕ) (p ρ D : ℝ)
    (H : ProgressBounds I propose choose respond output duration u b p ρ D)
    (n : ℕ) (hn : n ≤ u) (h : Fin n → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) n).support) :
    (revealed I (recordProposals propose) (PMF.seqHistory h)).card ≤
      b * count (reveals I (recordProposals propose)) (PMF.seqHistory h) := by
  induction n with
  | zero => simp [revealed, count]
  | succ n ih =>
    simp only [PMF.seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
    obtain ⟨g, hg, x, hx, rfl⟩ := hh
    rw [PMF.seqHistory_snoc]
    apply revealed_card_le_cons I (recordProposals propose) b _ _ ?_ (ih (by omega) g hg)
    cases x with
    | none => simp [revealed, recordProposals, Instance.covered]
    | some z =>
      obtain ⟨hs, hi, hz⟩ := (mem_support_policyLaw_some choose respond _ z.1 z.2).mp hx
      exact H.coverage n (by omega) g hg hs z.1 hi z.2 hz

/-- A successful actual output forces enough revealed-progress turns. No local
retention rule is imposed on the competing policy or its extraction kernel. -/
theorem success_count (u b r : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p ρ D : ℝ) (H : ProgressBounds I propose choose respond output duration u b p ρ D)
    (h : Fin u → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) u).support)
    (C : Finset J) (hC : C ∈ (output (PMF.seqHistory h)).support)
    (hs : CertifiedOutput I ρ D duration (PMF.seqHistory h) C) :
    r ≤ count (reveals I (recordProposals propose)) (PMF.seqHistory h) := by
  have hsub := H.provenance h hh C hC hs
  have hcover : I.ground ⊆ revealed I (recordProposals propose) (PMF.seqHistory h) := by
    rw [← covered_proposedSets I, ← hs.1]
    exact Finset.biUnion_subset_biUnion_of_subset_left I.sets hsub
  have hcard := (Finset.card_le_card hcover).trans
    (revealed_card_le I propose choose respond output duration u b p ρ D H u le_rfl h hh)
  by_contra hn
  have := hr _ (Nat.lt_of_not_ge hn)
  omega

/-- Actual randomized successful extraction is dominated by the revealed-count
threshold event. Provenance is needed only for the successful output masks. -/
theorem success_le_count_tail (u b r : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p ρ D : ℝ) (H : ProgressBounds I propose choose respond output duration u b p ρ D) :
    (outputLaw choose respond output u).toOuterMeasure
      {z | CertifiedOutput I ρ D duration z.history z.returned} ≤
      (PMF.seqProcess (responseStep (policyLaw choose respond)) u).toOuterMeasure
        {h | r ≤ count (reveals I (recordProposals propose)) (PMF.seqHistory h)} := by
  apply outputLaw_event_le
  intro h hh C hC hs
  exact success_count I propose choose respond output duration u b r hr p ρ D H h hh C hC hs

end Source
end Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
