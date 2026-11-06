/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.FullCover
import Mathlib.Tactic

/-!
# The nonempty-first-batch minimum

[Wang2027], Proposition 1, PDF p. 6 and Appendix A.1, PDF p. 14.
At maximum success, an arbitrary randomized failure-oblivious two-turn policy
has a nonempty complementary two-batch schedule of no greater expected cost.
The minimum is attained among these schedules, provided the population is nonempty
and a concurrent call to every opportunity meets the deadline.

## Main results

* `one_turn_cost`: the exact one-turn value.
* `two_batch_reduction`: the nonempty-first-batch reduction for every competing policy.
* `minimum_two_batch`: the attained minimum against all randomized competitors.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Finset Cslib.Optimization.OneConstraint
variable {ι K : Type} [Fintype ι] [Nonempty ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (I : FullCoverInstance ι K)

open scoped Classical in
/-- A nonempty first batch whose complementary second batch meets the deadline. -/
@[expose] def FullCoverInstance.TwoBatchFeasible (D : K) (A : Finset ι) : Prop :=
  A.Nonempty ∧ I.batchDuration A + I.batchDuration Aᶜ ≤ D

open scoped Classical in
/-- Expected cost of the complementary schedule, stopped on first-batch success. -/
@[expose] def FullCoverInstance.twoBatchCost (A : Finset ι) : K :=
  I.batchCost A + I.batchFailure A * I.batchCost Aᶜ

omit [Nonempty ι] in
/-- Proposition 1's one-turn value: at maximum success the full concurrent batch
is unavoidable, even with randomized selection. -/
theorem one_turn_cost (D : K) (π : Policy ι K 1) (hπ : π.Feasible I D)
    (hp : (π.execution I).mean executionSuccess = 1 - I.batchFailure univ) :
    (π.execution I).mean (executionCost I) = I.batchCost univ := by
  classical
  have hs := (maximum_success_support I π D hπ).mp hp
  have he : ∀ B ∈ π.scheduleLaw.support, B.expectedCost I = I.batchCost univ := by
    rintro ⟨A,u⟩ hB
    have hA : A = univ := by simpa [Plan.used] using hs (A,u) hB
    simp [Plan.expectedCost, hA]
  rw [(execution_equivalence I π).2]
  exact (Distribution.mean_eq_iff_of_le _ _ _ (fun B hB => (he B hB).le)).mpr he

/-- Canonicalizing empty padding does not require a nonempty first slot in the
competitor's representation. The returned first batch is nonempty. -/
theorem two_batch_reduction (D : K) (π : Policy ι K 2) (hπ : π.Feasible I D)
    (hp : (π.execution I).mean executionSuccess = 1 - I.batchFailure univ) :
    ∃ A : Finset ι, I.TwoBatchFeasible D A ∧
      I.twoBatchCost A ≤ (π.execution I).mean (executionCost I) := by
  classical
  obtain ⟨⟨A,C,u⟩,hf,hu,hc⟩ := deterministic_max_success I π D hπ hp
  have hAC : A ∪ C = univ := by
    ext i
    have hi := congrArg (i ∈ ·) hu
    simpa [Plan.used] using hi
  have hd : Disjoint A C := by simpa [Plan.NoReuse, Plan.used] using hf.1
  have hC : C = Aᶜ := by
    ext i
    have ha : i ∈ A ∨ i ∈ C := by simpa using congrArg (i ∈ ·) hAC
    have hn : ¬ (i ∈ A ∧ i ∈ C) := fun h => Finset.disjoint_left.mp hd h.1 h.2
    simp only [mem_compl]
    tauto
  subst C
  by_cases hA : A.Nonempty
  · refine ⟨A,⟨hA,?_⟩,?_⟩
    · simpa [Plan.duration] using hf.2
    · simpa [Plan.expectedCost, FullCoverInstance.twoBatchCost] using hc
  · have hA' : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    subst A
    refine ⟨univ,⟨univ_nonempty,?_⟩,?_⟩
    · simpa [Plan.duration, FullCoverInstance.batchDuration] using hf.2
    · simpa [Plan.expectedCost, FullCoverInstance.twoBatchCost, FullCoverInstance.batchCost,
        FullCoverInstance.batchFailure] using hc

open scoped Classical in
/-- The displayed minimum in Proposition 1 is attained. This theorem compares
with every feasible randomized maximum-success policy, rather than assuming an
optimizer or only comparing with deterministic schedules. -/
theorem minimum_two_batch (D : K) (hD : I.batchDuration univ ≤ D) :
    ∃ A : Finset ι, I.TwoBatchFeasible D A ∧
      (followPlan (K := K) (n := 2) (A,(Aᶜ,()))).Feasible I D ∧
      ((followPlan (K := K) (n := 2) (A,(Aᶜ,()))).execution I).mean executionSuccess =
        1 - I.batchFailure univ ∧
      ((followPlan (K := K) (n := 2) (A,(Aᶜ,()))).execution I).mean (executionCost I) =
        I.twoBatchCost A ∧
      ∀ π : Policy ι K 2, π.Feasible I D →
        (π.execution I).mean executionSuccess = 1 - I.batchFailure univ →
        I.twoBatchCost A ≤ (π.execution I).mean (executionCost I) := by
  classical
  let candidates := univ.filter (I.TwoBatchFeasible D)
  have hu : (univ : Finset ι) ∈ candidates := by
    simp only [candidates, mem_filter, mem_univ, true_and,
      FullCoverInstance.TwoBatchFeasible, compl_univ]
    refine ⟨univ_nonempty,?_⟩
    have he : I.batchDuration ∅ = 0 := by simp [FullCoverInstance.batchDuration]
    rwa [he, add_zero]
  obtain ⟨A,hA,hmin⟩ := candidates.exists_min_image I.twoBatchCost ⟨univ,hu⟩
  have hAf : I.TwoBatchFeasible D A := (mem_filter.mp hA).2
  refine ⟨A,hAf,?_,?_,?_,?_⟩
  · intro B hB
    rw [followPlan_law, Distribution.mem_support_pure] at hB
    subst B
    constructor
    · simpa [Plan.NoReuse, Plan.used] using
        (show Disjoint A Aᶜ from disjoint_compl_right)
    · simpa [Plan.duration] using hAf.2
  · rw [(execution_equivalence I _).1, followPlan_law, Distribution.mean_pure]
    exact (two_batch_values I A).1
  · rw [(execution_equivalence I _).2, followPlan_law, Distribution.mean_pure]
    exact (two_batch_values I A).2
  · intro π hπ hp
    obtain ⟨B,hB,hc⟩ := two_batch_reduction I D π hπ hp
    exact (hmin B (mem_filter.mpr ⟨mem_univ _,hB⟩)).trans hc

open scoped Classical in
omit [Nonempty ι] in
/-- The product–sum savings objective is exactly the reduction in expected cost. -/
theorem twoBatchCost_eq_total_sub (A : Finset ι) :
    I.twoBatchCost A = I.batchCost univ -
      (1 - I.batchFailure A) * I.batchCost Aᶜ := by
  classical
  have hsum : I.batchCost A + I.batchCost Aᶜ = I.batchCost univ := by
    exact sum_add_sum_compl A I.cost
  unfold FullCoverInstance.twoBatchCost
  linear_combination hsum

end Cslib.Probability.StochasticOracle
