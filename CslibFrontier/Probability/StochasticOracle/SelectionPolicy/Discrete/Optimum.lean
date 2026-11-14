/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.LowerCost
public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.Deadline
public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete
public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.Provenance
public import Mathlib.Algebra.Order.Floor.Div
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Fixed-budget token optima for actual discrete competitors

The instance-level infimum in [Wang2027], model PDF p. 5 and Theorem 5,
fixes the allowed turn budget and policy class before ranging over feasible policies. Actual
invoices and expected costs may have unbounded discrete support or infinite mean.
The complete-lattice infimum is infinity when no feasible policy exists.

Feasibility contains successful-output provenance, the actual physical deadline
and the actual success level. Source progress and resource envelopes are separate
hypotheses in the derived bounds. The independent `allowed` predicate specifies
the policy class, including opportunity-use restrictions where required; the
constructed upper witness must belong to that class. Its chosen retention decoder
is independent of the oracle's complete proposal decoder used by lower bounds.
Successful-only provenance against that complete decoder is a policy-admission
condition and can be derived from supported-response decoder compatibility.
This is the semantic PMF model; native
realization of these policies remains a separate obligation. The chosen-retention
decoder is deterministic on the recorded history and response. An operational
randomized retainer needs a joint-law representation before using this decoder interface.

## Main definitions

* `Feasible`: fixed-budget resource and success feasibility without source envelopes.
* `feasibleCosts`, `optimalCost`: the chosen policy class at the externally fixed budget.
* `retainingOutput`: the constructed upper policy's actual output.

## Main results

* `le_optimalCost`, `optimalCost_sandwich`: derived universal lower and actual upper bounds.
* `retaining_admissible_of_valid`: source provenance from per-response decoder compatibility.
* `optimalCost_sandwich_ceilDiv`: the manuscript's ceiling-count specialization.
* `matching_envelope_ratio`: the matching-envelope `1 / eta` comparison.
* `optimalCost_eq_top_of_deadline_bound`: source-derived infeasibility.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
open AdaptiveSelection PartialCover MeasureTheory
open scoped ENNReal
variable {B R E J : Type} [DecidableEq E] [DecidableEq J]

/-- Fixed-budget feasible selection-only execution, independent of source lower bounds.
Absorbing halt records pad policies that use fewer than `u` turns. -/
@[expose] def Feasible (I : Instance E J)
    (propose : List (Record B R) → B → R → List (Finset J))
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (output : List (Record B R) → PMF (Finset J))
    (duration : List (Record B R) → B → R → ℝ) (u : ℕ) (ρ D η : ℝ) : Prop :=
  Admissible I propose choose respond output duration u ρ D ∧
    DeadlineFeasible choose respond duration u D ∧
    η ≤ successProbability I choose respond output duration u ρ D

/-- Actual costs of feasible randomized competitors in the chosen policy class,
at the externally fixed budget. -/
@[expose] def feasibleCosts (I : Instance E J)
    (propose : List (Record B R) → B → R → List (Finset J))
    (respond : List (Record B R) → B → PMF R)
    (charge duration : List (Record B R) → B → R → ℝ)
    (allowed : (List (Record B R) → PMF (Option B)) →
      (List (Record B R) → PMF (Finset J)) → Prop) (u : ℕ) (ρ D η : ℝ) : Set ℝ≥0∞ :=
  {z | ∃ choose output, allowed choose output ∧
    Feasible I propose choose respond output duration u ρ D η ∧
    z = expectedCost choose respond charge u}

/-- Instance-level token infimum over the chosen class of actual feasible discrete competitors.
The empty feasible class has value infinity. -/
@[expose] def optimalCost (I : Instance E J)
    (propose : List (Record B R) → B → R → List (Finset J))
    (respond : List (Record B R) → B → PMF R)
    (charge duration : List (Record B R) → B → R → ℝ)
    (allowed : (List (Record B R) → PMF (Option B)) →
      (List (Record B R) → PMF (Finset J)) → Prop) (u : ℕ) (ρ D η : ℝ) : ℝ≥0∞ :=
  sInf (feasibleCosts I propose respond charge duration allowed u ρ D η)

/-- The canonical upper policy extracts its actual locally retained family. -/
@[expose] def retainingOutput (I : Instance E J) (ρ : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (h : List (Record B R)) : PMF (Finset J) :=
  PMF.pure (selected I ρ (recordProposals propose) h)

/-- Canonical retained extraction has provenance even for outputs that fail certification. -/
theorem retaining_admissible (I : Instance E J) (ρ D : ℝ)
    (propose : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (respond : List (Record B R) → B → PMF R)
    (duration : List (Record B R) → B → R → ℝ) (u : ℕ) :
    Admissible I propose (retainingChoose I ρ propose select) respond
      (retainingOutput I ρ propose) duration u ρ D := by
  intro h _ C hC _
  have he : C = selected I ρ (recordProposals propose) (PMF.seqHistory h) := by
    simpa only [retainingOutput, PMF.support_pure, Set.mem_singleton_iff] using hC
  subst C
  exact selected_subset_proposedSets I ρ (recordProposals propose) _

/-- A chosen retention decoder yields a selection-only output when each actual
response emits candidates from the complete, possibly buffered proposal history. -/
theorem retaining_admissible_of_valid (I : Instance E J) (ρ D : ℝ)
    (all retained : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (respond : List (Record B R) → B → PMF R)
    (duration : List (Record B R) → B → R → ℝ) (u : ℕ)
    (H : ProposalsValid (recordProposals all) (recordProposals retained)
      (retainingLaw I ρ retained select respond) u) :
    Admissible I all (retainingChoose I ρ retained select) respond
      (retainingOutput I ρ retained) duration u ρ D := by
  intro h hh C hC _
  have he : C = selected I ρ (recordProposals retained) (PMF.seqHistory h) := by
    simpa only [retainingOutput, PMF.support_pure, Set.mem_singleton_iff] using hC
  subst C
  exact selected_subset_proposedSets_of_valid I ρ (recordProposals all)
    (recordProposals retained) (retainingLaw I ρ retained select respond) u H u le_rfl h hh

section Bounds
variable (I : Instance E J)
  (propose : List (Record B R) → B → R → List (Finset J))
  (respond : List (Record B R) → B → PMF R)
  (charge duration : List (Record B R) → B → R → ℝ)
  (allowed : (List (Record B R) → PMF (Option B)) →
    (List (Record B R) → PMF (Finset J)) → Prop)

/-- Primitive universal token limitations bound the actual fixed-budget infimum;
no feasibility, integrability or lower-optimum conclusion is assumed. -/
theorem le_optimalCost (u b r : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p c ρ D η : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (hη : 0 ≤ η)
    (H : ∀ choose output, allowed choose output →
      Admissible I propose choose respond output duration u ρ D →
      LowerBounds I propose choose respond output charge duration u b p c ρ D) :
    ENNReal.ofReal (η * r * c / p) ≤
      optimalCost I propose respond charge duration allowed u ρ D η := by
  apply le_sInf
  rintro z ⟨choose, output, hAllowed, hf, rfl⟩
  apply lower_cost I propose choose respond output charge duration u b r hr p c ρ D η hp hc hη
    (H choose output hAllowed hf.1)
  exact (ENNReal.ofReal_le_iff_le_toReal (PMF.toOuterMeasure_ne_top _ _)).mpr hf.2.2

/-- Any actual feasible witness bounds the token infimum from above. -/
theorem optimalCost_le (u : ℕ) (ρ D η : ℝ)
    (choose : List (Record B R) → PMF (Option B))
    (output : List (Record B R) → PMF (Finset J))
    (hAllowed : allowed choose output)
    (H : Feasible I propose choose respond output duration u ρ D η) :
    optimalCost I propose respond charge duration allowed u ρ D η ≤
      expectedCost choose respond charge u :=
  sInf_le ⟨choose, output, hAllowed, H, rfl⟩

/-- A success requirement above the derived physical deadline tail leaves
no feasible competitor, so the extended token optimum is infinity. -/
theorem optimalCost_eq_top_of_deadline_bound (u b r : ℕ)
    (hr : ∀ k < r, b * k < I.ground.card)
    (p : Set.Icc (0 : ℝ) 1) (ρ D ℓ η : ℝ) (hℓ : 0 < ℓ)
    (H : ∀ choose output, allowed choose output →
      Admissible I propose choose respond output duration u ρ D →
      ProgressBounds I propose choose respond output duration u b p ρ D)
    (HT : ∀ choose output, allowed choose output →
      Admissible I propose choose respond output duration u ρ D →
      LatencyBound choose respond duration u ℓ)
    (hη : (ProbabilityTheory.binomial (min u ⌊D / ℓ⌋₊) p).real (Set.Ici r) < η) :
    optimalCost I propose respond charge duration allowed u ρ D η = ⊤ := by
  have he : feasibleCosts I propose respond charge duration allowed u ρ D η = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨choose, output, hAllowed, hf, _⟩
    have hb := deadline_probability_le I propose choose respond output duration u b r hr
      p ρ D ℓ hℓ (H choose output hAllowed hf.1) (HT choose output hAllowed hf.1)
    exact (not_le_of_gt hη) (hf.2.2.trans hb)
  rw [optimalCost, he, sInf_empty]

/-- Primitive upper-policy envelopes and selection-only admission supply an
actual feasible fixed-budget competitor. The chosen retention decoder can differ
from the complete proposal decoder; success is derived from coverage and duration. -/
theorem retaining_feasible
    (retained : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (u a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (c ell ρ D η : ℝ) (hell : 0 ≤ ell) (hD : (u : ℝ) * ell ≤ D)
    (hη : η ≤ 1 - (ProbabilityTheory.binomial u p).real (Set.Iio r))
    (hA : Admissible I propose (retainingChoose I ρ retained select) respond
      (retainingOutput I ρ retained) duration u ρ D)
    (H : UpperBounds I ρ retained select respond charge duration u a p c ell) :
    Feasible I propose (retainingChoose I ρ retained select) respond (retainingOutput I ρ retained)
      duration u ρ D η := by
  refine ⟨hA, ?_, ?_⟩
  · intro t ht h hh
    apply (duration_bound I ρ retained select respond charge duration u a p c ell hell H
      t ht h hh).2.trans
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht) hell).trans hD
  · have hb := certified_success I ρ retained select respond charge duration u a r hr p c ell D
      hell hD H
    change η ≤ ((outputLaw (retainingChoose I ρ retained select) respond
      (fun h => PMF.pure (selected I ρ (recordProposals retained) h)) u).toOuterMeasure
        {z | CertifiedOutput I ρ D duration z.history z.returned}).toReal
    rw [outputLaw_pure, PMF.toOuterMeasure_map_apply]
    exact hη.trans hb

/-- Source token sandwich for the fixed-budget semantic infimum. Feasibility
and the actual upper expected cost are constructed from primitive envelopes. -/
theorem optimalCost_sandwich
    (retained : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (u a ra b rb : ℕ) (hra : I.ground.card ≤ a * ra)
    (hrb : ∀ k < rb, b * k < I.ground.card)
    (pL pU : Set.Icc (0 : ℝ) 1) (hpL : 0 < (pL : ℝ)) (hpU : 0 < (pU : ℝ))
    (cL cU ell ρ D η : ℝ) (hcL : 0 ≤ cL) (hcU : 0 ≤ cU) (hell : 0 ≤ ell)
    (hD : (u : ℝ) * ell ≤ D) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 - (ProbabilityTheory.binomial u pL).real (Set.Iio ra))
    (hAllowed : allowed (retainingChoose I ρ retained select) (retainingOutput I ρ retained))
    (hA : Admissible I propose (retainingChoose I ρ retained select) respond
      (retainingOutput I ρ retained) duration u ρ D)
    (HU : UpperBounds I ρ retained select respond charge duration u a pL cU ell)
    (HL : ∀ choose output, allowed choose output →
      Admissible I propose choose respond output duration u ρ D →
      LowerBounds I propose choose respond output charge duration u b pU cL ρ D) :
    ENNReal.ofReal (η * rb * cL / pU) ≤
        optimalCost I propose respond charge duration allowed u ρ D η ∧
      optimalCost I propose respond charge duration allowed u ρ D η ≤
        expectedCost (retainingChoose I ρ retained select) respond charge u ∧
      expectedCost (retainingChoose I ρ retained select) respond charge u ≤
        ENNReal.ofReal (cU * min (u : ℝ) ((ra : ℝ) / pL)) := by
  refine ⟨le_optimalCost I propose respond charge duration allowed u b rb hrb pU cL ρ D η
    hpU hcL hη0 HL, optimalCost_le I propose respond charge duration allowed u ρ D η _ _ hAllowed
      (retaining_feasible I propose respond charge duration retained select
        u a ra hra pL cU ell ρ D η
        hell hD hη hA HU), ?_⟩
  exact cost_le_mean I ρ retained select respond charge duration u a ra hra pL hpL cU ell hcU HU

/-- The source ceiling counts `ceil(n/a)` and `ceil(n/b)` need no separate
cardinality/count certificates from the caller. -/
theorem optimalCost_sandwich_ceilDiv
    (retained : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B) (u a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (pL pU : Set.Icc (0 : ℝ) 1) (hpL : 0 < (pL : ℝ)) (hpU : 0 < (pU : ℝ))
    (cL cU ell ρ D η : ℝ) (hcL : 0 ≤ cL) (hcU : 0 ≤ cU) (hell : 0 ≤ ell)
    (hD : (u : ℝ) * ell ≤ D) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 - (ProbabilityTheory.binomial u pL).real (Set.Iio (I.ground.card ⌈/⌉ a)))
    (hAllowed : allowed (retainingChoose I ρ retained select) (retainingOutput I ρ retained))
    (hA : Admissible I propose (retainingChoose I ρ retained select) respond
      (retainingOutput I ρ retained) duration u ρ D)
    (HU : UpperBounds I ρ retained select respond charge duration u a pL cU ell)
    (HL : ∀ choose output, allowed choose output →
      Admissible I propose choose respond output duration u ρ D →
      LowerBounds I propose choose respond output charge duration u b pU cL ρ D) :
    ENNReal.ofReal (η * (I.ground.card ⌈/⌉ b) * cL / pU) ≤
        optimalCost I propose respond charge duration allowed u ρ D η ∧
      optimalCost I propose respond charge duration allowed u ρ D η ≤
        expectedCost (retainingChoose I ρ retained select) respond charge u ∧
      expectedCost (retainingChoose I ρ retained select) respond charge u ≤
        ENNReal.ofReal (cU * min (u : ℝ) ((I.ground.card ⌈/⌉ a : ℕ) / pL)) := by
  apply optimalCost_sandwich I propose respond charge duration allowed retained select
    u a (I.ground.card ⌈/⌉ a) b (I.ground.card ⌈/⌉ b) ?_ ?_
    pL pU hpL hpU cL cU ell ρ D η hcL hcU hell hD hη0 hη hAllowed hA HU HL
  · exact (ceilDiv_le_iff_le_mul ha).mp le_rfl
  · intro k hk
    exact lt_of_not_ge (fun h => (not_le_of_gt hk) ((ceilDiv_le_iff_le_mul hb).mpr h))

/-- Matching progress, coverage and token envelopes give the source `1 / eta`
comparison with the infimum over every feasible actual discrete competitor. -/
theorem matching_envelope_ratio
    (retained : List (Record B R) → B → R → List (Finset J))
    (select : List (Record B R) → PMF B)
    (u a r : ℕ) (hra : I.ground.card ≤ a * r)
    (hrb : ∀ k < r, a * k < I.ground.card)
    (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ))
    (c ell ρ D η : ℝ) (hc : 0 ≤ c) (hell : 0 ≤ ell)
    (hD : (u : ℝ) * ell ≤ D) (hη : 0 < η)
    (hηU : η ≤ 1 - (ProbabilityTheory.binomial u p).real (Set.Iio r))
    (hAllowed : allowed (retainingChoose I ρ retained select) (retainingOutput I ρ retained))
    (hA : Admissible I propose (retainingChoose I ρ retained select) respond
      (retainingOutput I ρ retained) duration u ρ D)
    (HU : UpperBounds I ρ retained select respond charge duration u a p c ell)
    (HL : ∀ choose output, allowed choose output →
      Admissible I propose choose respond output duration u ρ D →
      LowerBounds I propose choose respond output charge duration u a p c ρ D) :
    optimalCost I propose respond charge duration allowed u ρ D η ≤
        expectedCost (retainingChoose I ρ retained select) respond charge u ∧
      expectedCost (retainingChoose I ρ retained select) respond charge u ≤
        ENNReal.ofReal (1 / η) * optimalCost I propose respond charge duration allowed u ρ D η := by
  have hs := optimalCost_sandwich I propose respond charge duration allowed retained
    select
    u a r a r hra hrb p p hp hp c c ell ρ D η hc hc hell hD hη.le hηU
    hAllowed hA HU HL
  refine ⟨hs.2.1, ?_⟩
  have hu : expectedCost (retainingChoose I ρ retained select) respond charge u ≤
      ENNReal.ofReal (c * ((r : ℝ) / p)) := hs.2.2.trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_right _ _) hc))
  have he : ENNReal.ofReal (c * ((r : ℝ) / p)) =
      ENNReal.ofReal (1 / η) * ENNReal.ofReal (η * r * c / p) := by
    rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hη.le)]
    congr 1
    field_simp
  rw [he] at hu
  exact hu.trans (mul_le_mul_of_nonneg_left hs.1 (show (0 : ℝ≥0∞) ≤ _ from zero_le))

end Bounds
end Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
