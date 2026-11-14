/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.Competitor
public import Mathlib.Data.Fin.Tuple.Take
import CslibFrontier.Probability.StochasticDomination.SequentialUpper
import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.RecordCount
import CslibFrontier.Probability.PMF.SequentialPrefix
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Necessary deadlines for arbitrary discrete batch policies

The necessary binomial comparison of [Wang2027], Theorem 5(2), for actual PMF
batch selection and randomized output extraction. The source limitations concern
revealed proposals, rather than locally retained proposals, and require no
independence, finite alphabet or token-cost envelope.

## Main definitions

* `LatencyBound`: per-issued-call physical latency on actual support.

## Main results

* `latency_ge_calls`, `count_eq_deadline_prefix`: actual deadline prefixes.
* `revealed_tail_le`: upper comparison for actual revealed progress.
* `deadline_probability_le`: necessary physical deadline bound.

The token lower bound is independent and lives in `Discrete.LowerCost`.
Native realization of arbitrary behavioral policies is not asserted.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
open AdaptiveSelection PartialCover MeasureTheory
open scoped ENNReal
variable {B R E J : Type} [DecidableEq E] [DecidableEq J]
variable (I : Instance E J)
  (propose : List (Record B R) → B → R → List (Finset J))
  (choose : List (Record B R) → PMF (Option B))
  (respond : List (Record B R) → B → PMF R)
  (output : List (Record B R) → PMF (Finset J))
  (duration : List (Record B R) → B → R → ℝ)

/-- A positive physical latency lower bound is imposed only on actually
supported selected batches and their supported responses. The bound concerns
the duration actually added to `accruedBill`, including any cancellation convention. -/
structure LatencyBound (u : ℕ) (ℓ : ℝ) : Prop where
  /-- An actual issued call takes at least `ell` time. -/
  time : ∀ t, t < u → ∀ h : Fin t → Record B R,
    h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) t).support →
    none ∉ PMF.seqHistory h → ∀ i, some i ∈ (choose (PMF.seqHistory h)).support →
    ∀ x ∈ (respond (PMF.seqHistory h) i).support, ℓ ≤ duration (PMF.seqHistory h) i x

/-- The actual supported transcript's elapsed time is at least its issued-call
count times the primitive per-call latency. -/
theorem latency_ge_calls (u n : ℕ) (hn : n ≤ u) (ℓ : ℝ)
    (H : LatencyBound choose respond duration u ℓ)
    (h : Fin n → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) n).support) :
    ℓ * (count issued (PMF.seqHistory h) : ℝ) ≤
      accruedBill (recordResource duration) (PMF.seqHistory h) := by
  induction n with
  | zero => simp [count, accruedBill]
  | succ n ih =>
    simp only [PMF.seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
    obtain ⟨g, hg, x, hx, rfl⟩ := hh
    rw [PMF.seqHistory_snoc, count, accruedBill]
    have hp := ih (by omega) g hg
    cases x with
    | none => simpa only [issued, Option.isSome_none, Bool.false_eq_true, ite_false,
        Nat.add_zero, recordResource_none, add_zero] using hp
    | some z =>
      rcases z with ⟨i, x⟩
      obtain ⟨hs, hi, hz⟩ := (mem_support_policyLaw_some choose respond _ i x).mp hx
      have ht := H.time n (by omega) g hg hs i hi x hz
      simp only [issued, Option.isSome_some, ite_true, recordResource_some,
        Nat.cast_add, Nat.cast_one]
      nlinarith

/-- A supported path meeting the physical deadline gains no revealed progress
after `min u floor(D/ell)` chronological opportunities. -/
theorem count_eq_deadline_prefix (u : ℕ) (ℓ D : ℝ) (hℓ : 0 < ℓ)
    (H : LatencyBound choose respond duration u ℓ)
    (h : Fin u → Record B R)
    (hh : h ∈ (PMF.seqProcess (responseStep (policyLaw choose respond)) u).support)
    (hD : accruedBill (recordResource duration) (PMF.seqHistory h) ≤ D) :
    count (reveals I (recordProposals propose)) (PMF.seqHistory h) =
      count (reveals I (recordProposals propose))
        (PMF.seqHistory (Fin.take (min u ⌊D / ℓ⌋₊) (min_le_left _ _) h)) := by
  have hk : count issued (PMF.seqHistory h) ≤ ⌊D / ℓ⌋₊ := by
    apply Nat.le_floor
    apply (le_div_iff₀ hℓ).mpr
    have ht := latency_ge_calls choose respond duration u u le_rfl ℓ H h hh
    nlinarith
  apply count_eq_prefix_of_issued_bound _ (record_reveals_none propose I) (min_le_left _ _)
  · intro t ht
    have hx := PMF.mem_support_seqProcess_step
      (responseStep (policyLaw choose respond)) h hh t
    cases he : h t with
    | none => exact (ht he).elim
    | some z =>
      rw [he] at hx
      exact ((mem_support_policyLaw_some choose respond _ z.1 z.2).mp hx).1
  · exact le_min (by simpa only [PMF.length_seqHistory] using
      count_le_length issued (PMF.seqHistory h)) hk

/-- The actual revealed-progress tail at any earlier budget has the binomial
upper bound. No token resource assumptions are involved. -/
theorem revealed_tail_le (u b n r : ℕ) (hn : n ≤ u) (p : Set.Icc (0 : ℝ) 1) (ρ D : ℝ)
    (H : ProgressBounds I propose choose respond output duration u b p ρ D) :
    ((PMF.seqProcess (responseStep (policyLaw choose respond)) n).toOuterMeasure
      {h | r ≤ count (reveals I (recordProposals propose)) (PMF.seqHistory h)}).toReal ≤
      (ProbabilityTheory.binomial n p).real (Set.Ici r) := by
  have ht := PMF.seqCount_toReal_Ici_le_of_support
    (responseStep (policyLaw choose respond))
    (fun _ h => {x | reveals I (recordProposals propose) (PMF.seqHistory h) x = true})
    n r p (by
      intro t ht h hh
      have hp := conditional_progress_le_issued I propose choose respond output duration
        u b p ρ D p.2.1 H t (by omega) h hh
      have he : (policyLaw choose respond (PMF.seqHistory h)).toOuterMeasure
          {x | reveals I (recordProposals propose) (PMF.seqHistory h) x = true} ≤
            ENNReal.ofReal p := hp.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (PMF.toOuterMeasure_le_one (policyLaw choose respond (PMF.seqHistory h))
            {x | issued (PMF.seqHistory h) x = true})
          (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal p from zero_le))
      exact (ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) p.2.1).mp he)
  rw [PMF.toOuterMeasure_map_apply] at ht
  simpa only [Set.preimage, Set.mem_Ici, seqCount_eq_count] using ht

/-- Necessary binomial deadline bound for the actual arbitrary discrete
competitor. The independent physical latency hypothesis bounds the number of
completed opportunities; provenance is required only for successful outputs. -/
theorem deadline_probability_le (u b r : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p : Set.Icc (0 : ℝ) 1) (ρ D ℓ : ℝ) (hℓ : 0 < ℓ)
    (H : ProgressBounds I propose choose respond output duration u b p ρ D)
    (HT : LatencyBound choose respond duration u ℓ) :
    successProbability I choose respond output duration u ρ D ≤
      (ProbabilityTheory.binomial (min u ⌊D / ℓ⌋₊) p).real (Set.Ici r) := by
  let v := min u ⌊D / ℓ⌋₊
  let pre : Set (Fin u → Record B R) :=
    {h | r ≤ count (reveals I (recordProposals propose))
      (PMF.seqHistory (Fin.take v (min_le_left _ _) h))}
  have hs := outputLaw_event_le choose respond output u pre
    {z | CertifiedOutput I ρ D duration z.history z.returned} (by
      intro h hh C hC hS
      have hc := success_count I propose choose respond output duration u b r hr p ρ D
        H h hh C hC hS
      have he := count_eq_deadline_prefix I propose choose respond duration u ℓ D hℓ HT
        h hh hS.2.2
      change r ≤ _
      rwa [← he])
  have hm : (PMF.seqProcess (responseStep (policyLaw choose respond)) u).toOuterMeasure pre =
      (PMF.seqProcess (responseStep (policyLaw choose respond)) v).toOuterMeasure
        {h | r ≤ count (reveals I (recordProposals propose)) (PMF.seqHistory h)} := by
    have he := congrArg
      (fun q : PMF (Fin v → Record B R) => q.toOuterMeasure
        {h | r ≤ count (reveals I (recordProposals propose)) (PMF.seqHistory h)})
      (PMF.seqProcess_map_castLE (responseStep (policyLaw choose respond))
        (show v ≤ u from min_le_left _ _))
    rw [PMF.toOuterMeasure_map_apply] at he
    exact he
  have hreal := ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) hs
  rw [hm] at hreal
  exact hreal.trans (revealed_tail_le I propose choose respond output duration
    u b v r (min_le_left _ _) p ρ D H)

end Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
