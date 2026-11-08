/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.NativeOneTurn
public import Complexity.Probability.StochasticOracle.ResidualPolicy
import Mathlib.Tactic

/-!
# A native one-turn residual-selector lower bound

[Wang2027], model/selection-only definition, PDF pp. 4--6, and Theorem 6, p. 13.
The actual clocked two-phase native protocol is represented by constructed
behavioral tables. Source selection-only admission constrains successful outputs
only. Unsupported or unsuccessful fabricated families are replaced by the empty
family; this preserves success, issued token expectation and physical duration.
The representation and the universal cost bound are proved, not admission fields.

This covers the concrete `NativeOneTurn` interface, not arbitrary open PTMs,
unbounded local stopping, general response alphabets or upper-selector realization.

## Main results

* `nativePolicy_law`: actual native joint-law identification.
* `normalized_success`, `normalized_cost`: harmless failure-output normalization.
* `native_one_turn_lower`: derived lower expected token cost for admitted native protocols.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ResidualCover
open Finset Cslib.Optimization.OneConstraint PartialCover
variable {z : ℕ} {T : Fin z → Block}
variable (M : NativeOneTurn (Batch z) (Option (Fin z)) (Finset (Candidate T)))
variable (input : List Bool) (P : Parameters z)

/-- The exact raw-output behavioral representation, before failure normalization. -/
@[expose] def nativePolicy : OnePolicy T where
  first := M.actionTable input
  output := M.outputTable input

/-- Exact joint law of the actual native selector and the raw behavioral policy. -/
theorem nativePolicy_law : ((nativePolicy M input).run P).toPMF = M.run input (reply P) :=
  M.behavioralRun_toPMF input (reply P)

open scoped Classical in
/-- Discard an unproposed family on failure. Successful selection-only outputs
will already satisfy provenance and therefore remain unchanged. -/
@[expose] def proposedOnly (A : Batch z) (r : Option (Fin z)) (C : Finset (Candidate T)) :
    Finset (Candidate T) := if C ⊆ payload T (received A r) then C else ∅

/-- The constructed behavioral policy with harmless failure-output normalization. -/
@[expose] def normalizedNativePolicy : OnePolicy T where
  first := M.actionTable input
  output A r := (M.outputTable input A r).map (proposedOnly (T := T) A r)

/-- Provenance of the normalized policy is derived on every supported branch. -/
theorem normalizedNativePolicy_admissible : (normalizedNativePolicy M input).Admissible P := by
  classical
  intro A r C _ _ hc
  obtain ⟨D, _, he⟩ := (Distribution.mem_support_map (M.outputTable input A r)
    (proposedOnly (T := T) A r) C).mp (mem_filter.mpr ⟨mem_univ _, hc⟩)
  rw [← he]
  unfold proposedOnly
  split_ifs with h
  · exact h
  · exact empty_subset _

/-- Admission expresses actual supported native halting and the source's
successful-output-only provenance. It contains no behavioral law or cost bound. -/
@[expose] def NativeAdmitted (hz : 0 < z) : Prop :=
  M.Halts input (reply P) ∧
    ∀ A r C, 0 < (M.run input (reply P) (A, r, C)).toReal →
      optimalOutput hz C = 1 → C ⊆ payload T (received A r)

private theorem normalized_run :
    (normalizedNativePolicy M input).run P =
      ((nativePolicy M input).run P).map
        (fun (A, r, C) => (A, r, proposedOnly (T := T) A r C)) := by
  apply Distribution.toPMF_injective
  simp [OnePolicy.run, normalizedNativePolicy, nativePolicy, Distribution.toPMF_bind,
    Distribution.toPMF_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

private theorem empty_not_optimal (hz : 0 < z) : optimalOutput (T := T) hz ∅ = 0 := by
  simp [optimalOutput, Instance.cost]

/-- Native admission preserves success under failure normalization, without
requiring provenance of failed or null-history raw outputs. -/
theorem normalized_success (hz : 0 < z) (h : NativeAdmitted M input P hz) :
    (normalizedNativePolicy M input).success P hz =
      ∑ t : Batch z × Option (Fin z) × Finset (Candidate T),
        let (A, r, C) := t;
        (M.run input (reply P) (A, r, C)).toReal * optimalOutput hz C := by
  classical
  rw [← nativePolicy_law M input P]
  simp only [Distribution.toPMF_real]
  unfold OnePolicy.success
  rw [normalized_run, Distribution.mean_map]
  apply sum_congr rfl
  rintro ⟨A, r, C⟩ _
  change ((nativePolicy M input).run P).weight (A, r, C) *
    optimalOutput hz (proposedOnly (T := T) A r C) =
      ((nativePolicy M input).run P).weight (A, r, C) * optimalOutput hz C
  by_cases hw : 0 < ((nativePolicy M input).run P).weight (A, r, C)
  · have hn : 0 < (M.run input (reply P) (A, r, C)).toReal := by
      rw [← nativePolicy_law M input P, Distribution.toPMF_real]
      exact hw
    by_cases ho : optimalOutput (T := T) hz C = 1
    · simp only [proposedOnly, h.2 A r C hn ho, ite_true]
    · have hzC : optimalOutput (T := T) hz C = 0 := by
        unfold optimalOutput at *
        split_ifs at * <;> simp_all
      by_cases hp : C ⊆ payload T (received A r)
      · simp only [proposedOnly, hp, ite_true]
      · simp [proposedOnly, hp, empty_not_optimal, hzC]
  · have he : ((nativePolicy M input).run P).weight (A, r, C) = 0 :=
      le_antisymm (le_of_not_gt hw) (((nativePolicy M input).run P).nonneg _)
    simp [he]

/-- Issued token cost is unchanged by output normalization and agrees exactly
with the actual native experiment. Local computation is not billed. -/
theorem normalized_cost : (normalizedNativePolicy M input).cost P =
    ∑ t : Batch z × Option (Fin z) × Finset (Candidate T),
      (M.run input (reply P) t).toReal * batchCost P t.1 := by
  rw [← M.mean_eq_native input (reply P) (fun t => batchCost P t.1)]
  change (normalizedNativePolicy M input).cost P = (nativePolicy M input).cost P
  rw [OnePolicy.cost_eq, OnePolicy.cost_eq]
  rfl

/-- Failure normalization also preserves physical oracle duration exactly.
Local native computation clocks contribute neither to this duration nor to cost. -/
theorem normalized_duration : ((normalizedNativePolicy M input).run P).mean
    (fun t => batchLatency t.1) =
      ∑ t : Batch z × Option (Fin z) × Finset (Candidate T),
        (M.run input (reply P) t).toReal * batchLatency t.1 := by
  rw [← M.mean_eq_native input (reply P) (fun t => batchLatency t.1)]
  change ((normalizedNativePolicy M input).run P).mean _ = ((nativePolicy M input).run P).mean _
  rw [normalized_run, Distribution.mean_map]
  rfl

/-- The source one-turn lower bound for every admitted clocked native protocol:
actual probability-one optimal success forces actual expected cost at least sum cj.
Neither representation nor the desired lower bound is an admission premise. -/
theorem native_one_turn_lower (hz : 0 < z) (h : NativeAdmitted M input P hz)
    (hS : (∑ t : Batch z × Option (Fin z) × Finset (Candidate T),
      let (A, r, C) := t;
        (M.run input (reply P) (A, r, C)).toReal * optimalOutput hz C) = 1) :
    (∑ j, P.specialistCost j) ≤
      ∑ t : Batch z × Option (Fin z) × Finset (Candidate T),
        (M.run input (reply P) t).toReal * batchCost P t.1 := by
  rw [← normalized_cost M input P]
  apply OnePolicy.lower_cost P _ hz (normalizedNativePolicy_admissible M input P)
  rwa [normalized_success M input P hz h]

/-- Physical one-turn feasibility is independent of both local machine clocks,
including their harmless padding and empty-batch halting. -/
theorem native_duration_le_one :
    ∀ t ∈ (M.run input (reply P)).support, batchLatency t.1 ≤ 1 := by
  intro t _
  exact (unit_deadlines t.1 ∅).1

end Cslib.Probability.StochasticOracle.ResidualCover
