/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Optimization.OneConstraint
public import Complexity.Algorithms.Lean.Submodular.OracleSavings
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Full-cover stochastic-oracle policies

[Wang2027], Section 4, Proposition 1 and Theorem 1, PDF pp. 6–7.
A policy selects a concurrent batch, halts on success and, only after failure,
selects its next batch. Its conditional randomization may depend on the entire
sequence of previous batch identities. Failed texts, costs and response times are
not observations of this policy. The batch failure probability is the product of
individual failure probabilities; future calls have failure-invariant laws.

`Plan` uses a fixed number of slots. Empty slots issue no calls, cost zero and
have failure probability one; they can be erased to recover the paper's sequence
of nonempty batches. `Feasible` prohibits reuse and sums the maximum cutoff of
each batch, so all policies under consideration are nontruncating. Each finite
turn bound is covered; there is no fixed population or deadline in the theorems.

The execution law records success and the batches actually issued, padded with
empty batches after success. `execution_equivalence` derives the exact probability
and expected cost from that law, and `optimal_two_schedules` constructs an attained
LP optimum. Rational tables are covered by the same field-parametric proof.
No FPTAS, bit complexity or partial-cover assertion is made in this module.

## Main results

* `cost_success_frontier`: equality of the complete policy and LP frontiers.
* `optimal_two_schedules`: an attained optimum supported on at most two schedules.
* `maximum_success_support`: all positive schedules use every opportunity.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Finset Cslib.Optimization.OneConstraint
variable {ι K : Type} [Fintype ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Oracle parameters. A call succeeds strictly between probability zero and one;
its positive expected cost includes response or cancellation at its positive cutoff. -/
structure FullCoverInstance (ι K : Type) [Field K] [LinearOrder K] where
  /-- Probability of an accepted full cover by the cutoff. -/
  success : ι → K
  /-- Positive success probability. -/
  success_pos : ∀ i, 0 < success i
  /-- Certain-success opportunities are excluded, as in the source. -/
  success_lt_one : ∀ i, success i < 1
  /-- Expected charged tokens for the entire concurrent call. -/
  cost : ι → K
  /-- Positive expected token cost. -/
  cost_pos : ∀ i, 0 < cost i
  /-- Prescribed cutoff, excluding local computation time. -/
  cutoff : ι → K
  /-- Positive cutoff. -/
  cutoff_pos : ∀ i, 0 < cutoff i

omit [Fintype ι] [IsStrictOrderedRing K] in
/-- Oracle instances are determined by their probabilities, costs and cutoffs. -/
@[ext] theorem FullCoverInstance.ext (I J : FullCoverInstance ι K)
    (hp : ∀ i, I.success i = J.success i) (hc : ∀ i, I.cost i = J.cost i)
    (hl : ∀ i, I.cutoff i = J.cutoff i) : I = J := by
  have hp := funext hp
  have hc := funext hc
  have hl := funext hl
  cases I
  cases J
  cases hp
  cases hc
  cases hl
  rfl

/-- A bounded batch sequence, padded with empty slots. -/
abbrev Plan (ι : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => Finset ι × Plan ι n

instance planFintype (n : ℕ) : Fintype (Plan ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (Finset ι × Plan ι n))

noncomputable instance planDecidableEq (n : ℕ) : DecidableEq (Plan ι n) := by
  classical
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Finset ι × Plan ι n))

/-- The padded empty schedule. -/
@[expose] def Plan.empty : (n : ℕ) → Plan ι n
  | 0 => ()
  | n + 1 => (∅, Plan.empty n)

open scoped Classical in
/-- The call opportunities used by a plan, irrespective of stopping. -/
@[expose] def Plan.used : {n : ℕ} → Plan ι n → Finset ι
  | 0, _ => ∅
  | _ + 1, (A, B) => A ∪ B.used

/-- No call opportunity is used twice on the all-failure path. -/
@[expose] def Plan.NoReuse : {n : ℕ} → Plan ι n → Prop
  | 0, _ => True
  | _ + 1, (A, B) => Disjoint A B.used ∧ B.NoReuse

variable (I : FullCoverInstance ι K)

/-- Independent all-failure probability within a concurrent batch. -/
@[expose] def FullCoverInstance.batchFailure (A : Finset ι) : K :=
  ∏ i ∈ A, (1 - I.success i)

/-- Expected token costs add within a batch, including after its first success. -/
@[expose] def FullCoverInstance.batchCost (A : Finset ι) : K := ∑ i ∈ A, I.cost i

open scoped Classical in
/-- A concurrent batch is allotted the largest prescribed cutoff, or zero if empty. -/
@[expose] def FullCoverInstance.batchDuration (A : Finset ι) : K :=
  (insert 0 (A.image I.cutoff)).max' (by simp)

/-- Sum of allotted batch durations. -/
@[expose] def Plan.duration (I : FullCoverInstance ι K) : {n : ℕ} → Plan ι n → K
  | 0, _ => 0
  | _ + 1, (A, B) => I.batchDuration A + B.duration I

/-- Nontruncating deadline feasibility and single use of every opportunity. -/
@[expose] def Plan.Feasible {n : ℕ} (B : Plan ι n) (D : K) : Prop :=
  B.NoReuse ∧ B.duration I ≤ D

/-- All batches fail with this probability. -/
@[expose] def Plan.failure (I : FullCoverInstance ι K) : {n : ℕ} → Plan ι n → K
  | 0, _ => 1
  | _ + 1, (A, B) => I.batchFailure A * B.failure I

/-- Probability that at least one issued batch succeeds. -/
@[expose] def Plan.success {n : ℕ} (B : Plan ι n) : K := 1 - B.failure I

/-- Expected cost of a schedule stopped after its first successful batch. -/
@[expose] def Plan.expectedCost (I : FullCoverInstance ι K) : {n : ℕ} → Plan ι n → K
  | 0, _ => 0
  | _ + 1, (A, B) => I.batchCost A + I.batchFailure A * B.expectedCost I

/-- Cost of all batches appearing in an execution trace, including the successful batch. -/
@[expose] def Plan.traceCost (I : FullCoverInstance ι K) : {n : ℕ} → Plan ι n → K
  | 0, _ => 0
  | _ + 1, (A, B) => I.batchCost A + B.traceCost I

/-- A failure-oblivious randomized policy. A random node may remember its choice in its
continuation. An issue node sees only whether an accepted full cover was obtained;
its continuation runs exclusively on failure. Randomization is semantic here, allowing
real probabilities; rational tables have the same definitions and theorems. -/
inductive Policy (ι K : Type) [Fintype ι] [Field K] [LinearOrder K] : ℕ → Type 1
  | halt (n : ℕ) : Policy ι K n
  | issue {n : ℕ} (batch : Finset ι) (afterFailure : Policy ι K n) : Policy ι K (n+1)
  | random {n : ℕ} {α : Type} [Fintype α] (law : Distribution α K)
      (continuation : α → Policy ι K n) : Policy ι K n

/-- Hypothetical all-failure execution: private randomness is sampled, but the oracle
is never consulted. This is the schedule distribution induced by the original policy. -/
@[expose] def Policy.scheduleLaw : {n : ℕ} → Policy ι K n → Distribution (Plan ι n) K
  | n, .halt _ => Distribution.pure (Plan.empty n)
  | n + 1, .issue A π => π.scheduleLaw.map (fun B : Plan ι n => ((A,B) : Plan ι (n+1)))
  | _, @Policy.random _ _ _ _ _ _ _ hα w next =>
      letI := hα
      w.bind fun i => (next i).scheduleLaw

/-- The batch reply law, with `true` meaning that some call returned an accepted cover.
The product within the batch expresses conditionally independent successes. -/
@[expose] def FullCoverInstance.batchReply (A : Finset ι) : Distribution Bool K :=
  ⟨fun b => if b then 1 - I.batchFailure A else I.batchFailure A,
    fun b => by
      have h₀ : 0 ≤ I.batchFailure A := prod_nonneg fun i _ => by linarith [I.success_lt_one i]
      have h₁ : I.batchFailure A ≤ 1 := prod_le_one₀
        (fun i _ => by linarith [I.success_lt_one i])
        (fun i _ => by linarith [I.success_pos i])
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith,
    by simp⟩

omit [Fintype ι] in
/-- An empty virtual batch makes no call and cannot succeed. -/
@[simp] theorem FullCoverInstance.batchReply_empty :
    I.batchReply ∅ = Distribution.pure false := by
  classical
  ext b
  cases b <;> simp [FullCoverInstance.batchReply, FullCoverInstance.batchFailure,
    Distribution.pure]

/-- Actual stopped execution. Each reached batch incurs all its call costs, then either
succeeds and halts or continues with a fresh failure-invariant batch law. -/
@[expose] def Policy.execution (I : FullCoverInstance ι K) :
    {n : ℕ} → Policy ι K n → Distribution (Bool × Plan ι n) K
  | n, .halt _ => Distribution.pure (false, Plan.empty n)
  | n + 1, .issue A π => (I.batchReply A).bind fun b =>
      if b then Distribution.pure (true, (A, Plan.empty n))
      else (π.execution I).map fun (success, B) => (success, (A, B))
  | _, @Policy.random _ _ _ _ _ _ _ hα w next =>
      letI := hα
      w.bind fun i => (next i).execution I

/-- Success indicator on the execution's observed terminal result. -/
@[expose] def executionSuccess {n : ℕ} : Bool × Plan ι n → K :=
  fun (success, _) => if success then 1 else 0

/-- Token cost determined by the batches actually issued. This charges expected call
costs; the tower identity transfers it to random billed costs under the FICA. -/
@[expose] def executionCost {n : ℕ} : Bool × Plan ι n → K :=
  fun (_, B) => B.traceCost I

omit [Fintype ι] [IsStrictOrderedRing K] in
private theorem empty_values (n : ℕ) :
    (Plan.empty (ι := ι) n).failure I = 1 ∧
      (Plan.empty (ι := ι) n).traceCost I = 0 ∧
      (Plan.empty (ι := ι) n).expectedCost I = 0 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih => simp [Plan.empty, Plan.failure, Plan.traceCost, Plan.expectedCost,
      FullCoverInstance.batchFailure, FullCoverInstance.batchCost, ih]

omit [Fintype ι] in
private theorem batchReply_mean (A : Finset ι) (f : Bool → K) :
    (I.batchReply A).mean f = (1 - I.batchFailure A) * f true + I.batchFailure A * f false := by
  simp [Distribution.mean, FullCoverInstance.batchReply]

/-- The exact policy-to-schedule probability and cost identity. Neither expectation
is supplied as a hypothesis: both come from the law of the actual stopped execution. -/
theorem execution_equivalence {n : ℕ} (π : Policy ι K n) :
    (π.execution I).mean executionSuccess = π.scheduleLaw.mean (Plan.success I) ∧
      (π.execution I).mean (executionCost I) = π.scheduleLaw.mean (Plan.expectedCost I) := by
  induction π with
  | halt n => simp [Policy.execution, Policy.scheduleLaw, Distribution.mean_pure,
      executionSuccess, executionCost, Plan.success, empty_values]
  | @issue n A π ih =>
    constructor
    · rw [Policy.execution, Distribution.mean_bind, batchReply_mean]
      simp only [Bool.false_eq_true, ↓reduceIte, Distribution.mean_pure,
        Distribution.mean_map, Function.comp_def]
      change (1 - I.batchFailure A) * 1 + I.batchFailure A *
        (π.execution I).mean executionSuccess = _
      rw [ih.1, Policy.scheduleLaw, Distribution.mean_map]
      change _ = π.scheduleLaw.mean (fun B => 1 - I.batchFailure A * B.failure I)
      have hs : π.scheduleLaw.mean (Plan.success I) =
          1 - π.scheduleLaw.mean (Plan.failure I) := by
        simp only [Plan.success, Distribution.mean, mul_sub, mul_one, sum_sub_distrib,
          Distribution.total]
      rw [hs]
      simp only [Distribution.mean, mul_sub, sum_sub_distrib, mul_one,
        Distribution.total]
      have hm : (∑ x, π.scheduleLaw.weight x * (I.batchFailure A * Plan.failure I x)) =
          I.batchFailure A * ∑ x, π.scheduleLaw.weight x * Plan.failure I x := by
        simp only [mul_left_comm (π.scheduleLaw.weight _), mul_sum]
      rw [hm]
      ring
    · rw [Policy.execution, Distribution.mean_bind, batchReply_mean]
      simp only [Bool.false_eq_true, ↓reduceIte, Distribution.mean_pure,
        Distribution.mean_map, Function.comp_def]
      change (1 - I.batchFailure A) * (I.batchCost A + (Plan.empty n).traceCost I) +
        I.batchFailure A * (π.execution I).mean
          (fun x => I.batchCost A + executionCost I x) = _
      rw [(empty_values I n).2.1, add_zero, Distribution.mean_add, Distribution.mean_const, ih.2,
        Policy.scheduleLaw, Distribution.mean_map]
      change _ = π.scheduleLaw.mean (fun B => I.batchCost A + I.batchFailure A * B.expectedCost I)
      rw [Distribution.mean_add, Distribution.mean_const, Distribution.mean_mul]
      ring
  | random w next ih =>
    simp only [Policy.execution, Policy.scheduleLaw, Distribution.mean_bind]
    exact ⟨congrArg (Distribution.mean w) (funext fun i => (ih i).1),
      congrArg (Distribution.mean w) (funext fun i => (ih i).2)⟩

/-- Follow a fixed schedule, stopping immediately after a successful batch. -/
@[expose] def followPlan : {n : ℕ} → Plan ι n → Policy ι K n
  | 0, _ => .halt 0
  | _ + 1, (A, B) => .issue A (followPlan B)

/-- A fixed schedule's hypothetical all-failure law is deterministic. -/
theorem followPlan_law {n : ℕ} (B : Plan ι n) :
    (followPlan (K := K) B).scheduleLaw = Distribution.pure B := by
  induction n with
  | zero => cases B; rfl
  | succ n ih =>
    rcases B with ⟨A,B⟩
    simp only [followPlan, Policy.scheduleLaw, ih]
    apply Distribution.ext
    funext C
    simp only [Distribution.map, Distribution.pure]
    rw [sum_eq_single B]
    · by_cases h : C = (A, B)
      · subst C; simp
      · simp [h, Ne.symm h]
    · intro i _ hi
      split_ifs <;> simp_all
    · simp

/-- Sample an entire schedule before the first call, then follow it. -/
@[expose] def preselect {n : ℕ} (w : Distribution (Plan ι n) K) : Policy ι K n :=
  .random w followPlan

/-- Preselection realizes exactly the specified schedule table. -/
theorem preselect_law {n : ℕ} (w : Distribution (Plan ι n) K) :
    (preselect w).scheduleLaw = w := by
  simp only [preselect, Policy.scheduleLaw, followPlan_law]
  apply Distribution.ext
  funext B
  simp [Distribution.bind, Distribution.pure]

/-- Theorem 1(1): moving every selection choice before the first oracle call preserves
both success probability and expected cost. -/
theorem preselection_equivalent {n : ℕ} (π : Policy ι K n) :
    ((preselect π.scheduleLaw).execution I).mean executionSuccess =
        (π.execution I).mean executionSuccess ∧
      ((preselect π.scheduleLaw).execution I).mean (executionCost I) =
        (π.execution I).mean (executionCost I) := by
  rw [(execution_equivalence I _).1, (execution_equivalence I _).2, preselect_law,
    (execution_equivalence I π).1, (execution_equivalence I π).2]
  exact ⟨rfl, rfl⟩

open scoped Classical in
/-- All nontruncating, nonrepeating schedules within the given deadline and turn bound. -/
@[expose] def feasiblePlans (n : ℕ) (D : K) : Finset (Plan ι n) :=
  univ.filter fun B => B.Feasible I D

/-- Every possible all-failure execution satisfies the deadline and no-reuse constraints. -/
@[expose] def Policy.Feasible {n : ℕ} (π : Policy ι K n) (D : K) : Prop :=
  ∀ B ∈ π.scheduleLaw.support, B.Feasible I D

private theorem infeasible_weight_zero {n : ℕ} (π : Policy ι K n) (D : K)
    (hπ : π.Feasible I D) (B : Plan ι n) (hB : B ∉ feasiblePlans I n D) :
    π.scheduleLaw.weight B = 0 := by
  classical
  have hn : ¬ 0 < π.scheduleLaw.weight B := by
    intro h
    exact hB (mem_filter.mpr ⟨mem_univ B, hπ B (mem_filter.mpr ⟨mem_univ B, h⟩)⟩)
  exact le_antisymm (le_of_not_gt hn) (π.scheduleLaw.nonneg B)

/-- The feasible LP table induced by a deadline-feasible policy, with no normalization
loss: infeasible schedules have zero mass. -/
@[expose] def Policy.feasibleLaw {n : ℕ} (π : Policy ι K n) (D : K)
    (hπ : π.Feasible I D) : Distribution (feasiblePlans I n D) K :=
  π.scheduleLaw.restrict (feasiblePlans I n D) (by exact infeasible_weight_zero I π D hπ)

/-- The induced feasible LP table preserves each observable of the schedule. -/
theorem Policy.feasibleLaw_mean {n : ℕ} (π : Policy ι K n) (D : K)
    (hπ : π.Feasible I D) (f : Plan ι n → K) :
    (π.feasibleLaw I D hπ).mean (fun B => f B) = π.scheduleLaw.mean f :=
  Distribution.mean_restrict _ _ _ _

/-- Preselecting only feasible schedules defines a feasible policy. -/
theorem preselect_feasible {n : ℕ} (D : K) (w : Distribution (feasiblePlans I n D) K) :
    (preselect (w.map Subtype.val)).Feasible I D := by
  classical
  intro B hB
  rw [preselect_law] at hB
  by_contra h
  have hz : (w.map Subtype.val).weight B = 0 := by
    apply sum_eq_zero
    intro C _
    have hCB : C.val ≠ B := by
      intro hCB
      have := (mem_filter.mp C.property).2
      exact h (hCB ▸ this)
    simp [hCB]
  have : 0 < (w.map Subtype.val).weight B := (mem_filter.mp hB).2
  rw [hz] at this
  exact lt_irrefl _ this

/-- Full-cover policy feasibility is exactly feasibility of the finite LP. This also
identifies the infeasible case, without assuming an optimizer or a feasible policy. -/
theorem policy_iff_lp {n : ℕ} (D η : K) :
    (∃ π : Policy ι K n, π.Feasible I D ∧
      η ≤ (π.execution I).mean executionSuccess) ↔
    ∃ w : Distribution (feasiblePlans I n D) K, η ≤ w.mean (fun B => B.val.success I) := by
  constructor
  · rintro ⟨π,hπ,hη⟩
    refine ⟨π.feasibleLaw I D hπ, ?_⟩
    rwa [Policy.feasibleLaw_mean, ← (execution_equivalence I π).1]
  · rintro ⟨w,hw⟩
    refine ⟨preselect (w.map Subtype.val), preselect_feasible I D w, ?_⟩
    rw [(execution_equivalence I _).1, preselect_law, Distribution.mean_map]
    exact hw

/-- The entire achievable cost–success frontier equals the LP frontier, including
both coordinates. In particular, taking infima over a required success threshold
preserves the objective and infeasibility, rather than merely feasibility. -/
theorem cost_success_frontier {n : ℕ} (D P C : K) :
    (∃ π : Policy ι K n, π.Feasible I D ∧
      (π.execution I).mean executionSuccess = P ∧
      (π.execution I).mean (executionCost I) = C) ↔
    ∃ w : Distribution (feasiblePlans I n D) K,
      w.mean (fun B => B.val.success I) = P ∧
      w.mean (fun B => B.val.expectedCost I) = C := by
  constructor
  · rintro ⟨π,hπ,hp,hc⟩
    refine ⟨π.feasibleLaw I D hπ,?_,?_⟩
    · rwa [Policy.feasibleLaw_mean, ← (execution_equivalence I π).1]
    · rwa [Policy.feasibleLaw_mean, ← (execution_equivalence I π).2]
  · rintro ⟨w,hp,hc⟩
    refine ⟨preselect (w.map Subtype.val),preselect_feasible I D w,?_,?_⟩
    · rwa [(execution_equivalence I _).1,preselect_law,Distribution.mean_map]
    · rwa [(execution_equivalence I _).2,preselect_law,Distribution.mean_map]

/-- A success target is feasible exactly when some feasible schedule attains it.
This is the maximum-success threshold condition, with the empty feasible set handled
without choosing a spurious maximizer. -/
theorem target_feasible_iff_schedule {n : ℕ} (D η : K) :
    (∃ π : Policy ι K n, π.Feasible I D ∧
      η ≤ (π.execution I).mean executionSuccess) ↔
    ∃ B ∈ feasiblePlans I n D, η ≤ B.success I := by
  classical
  rw [policy_iff_lp I D η]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨B,_,hB⟩ := w.exists_support_le_mean (fun B => -B.val.success I)
    have hm : w.mean (fun B => -B.val.success I) = -w.mean (fun B => B.val.success I) := by
      simp [Distribution.mean, mul_neg, sum_neg_distrib]
    rw [hm] at hB
    exact ⟨B.val,B.property,by linarith⟩
  · rintro ⟨B,hB,hp⟩
    exact ⟨Distribution.pure ⟨B,hB⟩,by simpa only [Distribution.mean_pure] using hp⟩

/-- Theorems 1(2)–(3), at the level of exact semantic selection policies: whenever
the LP is feasible, an optimal deadline-feasible policy exists and preselects at most
two schedules. This constructs the optimizer over any linear ordered field, including
rational input/probability tables, rather than accepting optimality as an assumption. -/
theorem optimal_two_schedules {n : ℕ} (D η : K)
    (hfeas : ∃ π : Policy ι K n, π.Feasible I D ∧
      η ≤ (π.execution I).mean executionSuccess) :
    ∃ π : Policy ι K n, π.Feasible I D ∧ π.scheduleLaw.support.card ≤ 2 ∧
      η ≤ (π.execution I).mean executionSuccess ∧
      ∀ ψ : Policy ι K n, ψ.Feasible I D →
        η ≤ (ψ.execution I).mean executionSuccess →
        (π.execution I).mean (executionCost I) ≤ (ψ.execution I).mean (executionCost I) := by
  classical
  obtain ⟨w,hw⟩ := (policy_iff_lp I D η).mp hfeas
  obtain ⟨v,hv,hvp,hvc⟩ := exists_optimal_two
    (fun B : feasiblePlans I n D => B.val.success I)
    (fun B : feasiblePlans I n D => B.val.expectedCost I) η ⟨w,hw⟩
  refine ⟨preselect (v.map Subtype.val), preselect_feasible I D v, ?_, ?_, ?_⟩
  · rw [preselect_law]
    exact (Distribution.support_map_card v Subtype.val).trans hv
  · rw [(execution_equivalence I _).1, preselect_law, Distribution.mean_map]
    exact hvp
  · intro ψ hψ hη
    rw [(execution_equivalence I _).2, preselect_law, Distribution.mean_map,
      (execution_equivalence I ψ).2]
    have hψp : η ≤ (ψ.feasibleLaw I D hψ).mean (fun B => B.val.success I) := by
      rwa [Policy.feasibleLaw_mean, ← (execution_equivalence I ψ).1]
    have := hvc (ψ.feasibleLaw I D hψ) hψp
    rwa [Policy.feasibleLaw_mean] at this

omit [Fintype ι] [IsStrictOrderedRing K] in
/-- The schedule failure probability depends only on the opportunities used, provided
none is reused. This connects the stopped experiment to independent call opportunities. -/
theorem Plan.failure_eq_batchFailure {n : ℕ} (B : Plan ι n) (hB : B.NoReuse) :
    B.failure I = I.batchFailure B.used := by
  classical
  induction n with
  | zero => simp [Plan.failure, Plan.used, FullCoverInstance.batchFailure]
  | succ n ih =>
    rcases B with ⟨A,B⟩
    change I.batchFailure A * B.failure I = I.batchFailure (A ∪ B.used)
    rw [ih B hB.2]
    exact (prod_union hB.1).symm

omit [Fintype ι] in
/-- Strictly positive probability of every all-failure batch. -/
theorem FullCoverInstance.batchFailure_pos (A : Finset ι) : 0 < I.batchFailure A :=
  prod_pos fun i _ => sub_pos.mpr (I.success_lt_one i)

omit [Fintype ι] in
/-- The probability that every call in a batch fails is at most one. -/
theorem FullCoverInstance.batchFailure_le_one (A : Finset ι) : I.batchFailure A ≤ 1 :=
  prod_le_one₀ (fun i _ => (sub_pos.mpr (I.success_lt_one i)).le)
    (fun i _ => by linarith [I.success_pos i])

/-- Missing any opportunity strictly lowers success. The strict success-probability
hypotheses are essential for this characterization. -/
theorem batchFailure_eq_total_iff (A : Finset ι) :
    I.batchFailure A = I.batchFailure univ ↔ A = univ := by
  classical
  constructor
  · intro h
    by_contra hn
    have hex : ∃ i, i ∉ A := by
      by_contra h
      apply hn
      ext i
      simp_all
    obtain ⟨i,hi⟩ := hex
    have hle : I.batchFailure univ ≤ I.batchFailure (insert i A) :=
      prod_le_prod_of_subset_of_le_one₀ (subset_univ _)
        (fun i _ => (sub_pos.mpr (I.success_lt_one i)).le)
        (fun i _ _ => by linarith [I.success_pos i])
    have hins : I.batchFailure (insert i A) = (1 - I.success i) * I.batchFailure A :=
      prod_insert hi
    rw [hins, ← h] at hle
    nlinarith [I.batchFailure_pos A, I.success_pos i]
  · rintro rfl; rfl

/-- No single-use schedule can exceed the success probability of querying every call. -/
theorem Plan.success_le_total {n : ℕ} (B : Plan ι n) (hB : B.NoReuse) :
    B.success I ≤ 1 - I.batchFailure univ := by
  classical
  unfold Plan.success
  rw [B.failure_eq_batchFailure I hB]
  apply sub_le_sub_left
  exact prod_le_prod_of_subset_of_le_one₀ (subset_univ _)
    (fun i _ => (sub_pos.mpr (I.success_lt_one i)).le)
    (fun i _ _ => by linarith [I.success_pos i])

/-- A deterministic schedule attains maximum success exactly when it uses every
opportunity on its all-failure path. -/
theorem Plan.success_eq_total_iff {n : ℕ} (B : Plan ι n) (hB : B.NoReuse) :
    B.success I = 1 - I.batchFailure univ ↔ B.used = univ := by
  rw [Plan.success, B.failure_eq_batchFailure I hB, sub_right_inj,
    batchFailure_eq_total_iff]

omit [Fintype ι] [IsStrictOrderedRing K] in
/-- Exact one-batch cost and success, including an empty population. -/
theorem one_batch_values (A : Finset ι) :
    Plan.success I (n := 1) ((A, ()) : Plan ι 1) = 1 - I.batchFailure A ∧
      Plan.expectedCost I (n := 1) ((A, ()) : Plan ι 1) = I.batchCost A := by
  simp [Plan.success, Plan.failure, Plan.expectedCost]

open scoped Classical in
/-- Exact complementary two-batch cost and maximum success. The second batch is
queried only after the first fails. -/
theorem two_batch_values (A : Finset ι) :
    Plan.success I (n := 2) ((A, (Aᶜ, ())) : Plan ι 2) = 1 - I.batchFailure univ ∧
      Plan.expectedCost I (n := 2) ((A, (Aᶜ, ())) : Plan ι 2) =
        I.batchCost A + I.batchFailure A * I.batchCost Aᶜ := by
  classical
  constructor
  · apply (Plan.success_eq_total_iff I _ ?_).mpr
    · simp [Plan.used]
    · simpa [Plan.NoReuse, Plan.used] using
        (show Disjoint A Aᶜ from disjoint_compl_right)
  · simp [Plan.expectedCost]

/-- A randomized maximum-success policy puts positive weight only on schedules
using every opportunity. This uses strict call probabilities, not an optimality premise. -/
theorem maximum_success_support {n : ℕ} (π : Policy ι K n) (D : K)
    (hπ : π.Feasible I D) :
    (π.execution I).mean executionSuccess = 1 - I.batchFailure univ ↔
      ∀ B ∈ π.scheduleLaw.support, B.used = univ := by
  rw [(execution_equivalence I π).1,
    Distribution.mean_eq_iff_of_le _ _ _ (fun B hB =>
      Plan.success_le_total I B (hπ B hB).1)]
  exact forall₂_congr fun B hB => Plan.success_eq_total_iff I B (hπ B hB).1

/-- Randomization cannot lower the optimum among maximum-success policies:
some deterministic feasible schedule attains the same success at no greater cost. -/
theorem deterministic_max_success {n : ℕ} (π : Policy ι K n) (D : K)
    (hπ : π.Feasible I D)
    (hmax : (π.execution I).mean executionSuccess = 1 - I.batchFailure univ) :
    ∃ B : Plan ι n, B.Feasible I D ∧ B.used = univ ∧
      B.expectedCost I ≤ (π.execution I).mean (executionCost I) := by
  obtain ⟨B,hB,hcost⟩ := π.scheduleLaw.exists_support_le_mean (Plan.expectedCost I)
  refine ⟨B,hπ B hB,(maximum_success_support I π D hπ).mp hmax B hB,?_⟩
  rwa [← (execution_equivalence I π).2] at hcost

end Cslib.Probability.StochasticOracle
