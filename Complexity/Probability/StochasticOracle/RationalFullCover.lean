/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.Programs
import Mathlib.Tactic

/-!
# Rational full-cover inputs and unrestricted real randomization

The rational-input part of [Wang2027], Theorem 1(2)–(3), PDF p. 7.
Input probabilities, expected costs, cutoffs, deadline and target are rational,
but competing policies may use arbitrary real randomization. Rational-to-real
interpretation preserves the product probabilities, stopped costs and deadline
constraints. An attained optimal two-schedule table has an exact `ProbComp`
sampler and `ProbOracleComp` execution, rather than an assumed implementation.
No running-time bound for the LP enumeration is claimed.

## Main results

* `optimal_rational_program`: implemented rational optimum against real competitors.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Finset Cslib.Optimization.OneConstraint
variable {ι : Type} [Fintype ι]

/-- Interpret the supplied rational oracle parameters as real numbers. -/
@[expose] def FullCoverInstance.realify (I : FullCoverInstance ι ℚ) : FullCoverInstance ι ℝ :=
  ⟨fun i => (I.success i : ℝ), fun i => by exact_mod_cast I.success_pos i,
    fun i => by exact_mod_cast I.success_lt_one i,
    fun i => (I.cost i : ℝ), fun i => by exact_mod_cast I.cost_pos i,
    fun i => (I.cutoff i : ℝ), fun i => by exact_mod_cast I.cutoff_pos i⟩

variable (I : FullCoverInstance ι ℚ)

omit [Fintype ι] in
/-- Concurrent independent-failure products survive rational interpretation. -/
theorem FullCoverInstance.batchFailure_realify (A : Finset ι) :
    I.realify.batchFailure A = ((I.batchFailure A : ℚ) : ℝ) := by
  simp [FullCoverInstance.batchFailure, FullCoverInstance.realify]

omit [Fintype ι] in
/-- Expected batch costs survive rational interpretation. -/
theorem FullCoverInstance.batchCost_realify (A : Finset ι) :
    I.realify.batchCost A = ((I.batchCost A : ℚ) : ℝ) := by
  simp [FullCoverInstance.batchCost, FullCoverInstance.realify]

omit [Fintype ι] in
/-- Concurrent batch cutoff maxima survive rational interpretation. -/
theorem FullCoverInstance.batchDuration_realify (A : Finset ι) :
    I.realify.batchDuration A = ((I.batchDuration A : ℚ) : ℝ) := by
  classical
  have hm : Monotone (fun q : ℚ => (q : ℝ)) := fun a b h => by
    change (a : ℝ) ≤ (b : ℝ)
    exact_mod_cast h
  have h := hm.map_finset_max' (show (insert 0 (A.image I.cutoff)).Nonempty by simp)
  simpa [FullCoverInstance.batchDuration, FullCoverInstance.realify, image_image,
    Function.comp_def] using h.symm

omit [Fintype ι] in
/-- Full schedule probabilities survive rational interpretation. -/
theorem Plan.success_realify {n : ℕ} (B : Plan ι n) :
    B.success I.realify = ((B.success I : ℚ) : ℝ) := by
  have hf : ∀ {n : ℕ} (B : Plan ι n), B.failure I.realify = ((B.failure I : ℚ) : ℝ) := by
    intro n B
    induction n with
    | zero => simp [Plan.failure]
    | succ n ih =>
      rcases B with ⟨A,B⟩
      simp [Plan.failure, FullCoverInstance.batchFailure_realify, ih]
  simp [Plan.success, hf]

omit [Fintype ι] in
/-- Stopped expected costs survive rational interpretation. -/
theorem Plan.expectedCost_realify {n : ℕ} (B : Plan ι n) :
    B.expectedCost I.realify = ((B.expectedCost I : ℚ) : ℝ) := by
  induction n with
  | zero => simp [Plan.expectedCost]
  | succ n ih =>
    rcases B with ⟨A,B⟩
    simp [Plan.expectedCost, FullCoverInstance.batchCost_realify,
      FullCoverInstance.batchFailure_realify, ih]

omit [Fintype ι] in
/-- Allotted schedule durations survive rational interpretation. -/
theorem Plan.duration_realify {n : ℕ} (B : Plan ι n) :
    B.duration I.realify = ((B.duration I : ℚ) : ℝ) := by
  induction n with
  | zero => simp [Plan.duration]
  | succ n ih =>
    rcases B with ⟨A,B⟩
    simp [Plan.duration, FullCoverInstance.batchDuration_realify, ih]

/-- Exactly the same schedules are feasible before and after interpreting the input. -/
theorem feasiblePlans_realify_iff {n : ℕ} (D : ℚ) (B : Plan ι n) :
    B ∈ feasiblePlans I.realify n (D : ℝ) ↔ B ∈ feasiblePlans I n D := by
  classical
  constructor
  · intro h
    have hf := (mem_filter.mp h).2
    apply mem_filter.mpr
    refine ⟨mem_univ B,hf.1,?_⟩
    have hd := hf.2
    rw [Plan.duration_realify] at hd
    exact_mod_cast hd
  · intro h
    have hf := (mem_filter.mp h).2
    apply mem_filter.mpr
    refine ⟨mem_univ B,hf.1,?_⟩
    change B.duration I.realify ≤ (D : ℝ)
    rw [Plan.duration_realify]
    exact_mod_cast hf.2

private theorem real_policy_restriction {n : ℕ} (D : ℚ) (π : Policy ι ℝ n)
    (hπ : π.Feasible I.realify (D : ℝ)) :
    ∀ B ∉ feasiblePlans I n D, π.scheduleLaw.weight B = 0 := by
  classical
  intro B hB
  have hn : ¬ 0 < π.scheduleLaw.weight B := by
    intro hp
    have hf := hπ B (mem_filter.mpr ⟨mem_univ B,hp⟩)
    exact hB ((feasiblePlans_realify_iff I D B).mp (mem_filter.mpr ⟨mem_univ B,hf⟩))
  exact le_antisymm (le_of_not_gt hn) (π.scheduleLaw.nonneg B)

/-- The finite LP table of an arbitrary real-randomized feasible policy, indexed by
rational-input feasible schedules. -/
@[expose] def rationalInputLaw {n : ℕ} (D : ℚ) (π : Policy ι ℝ n)
    (hπ : π.Feasible I.realify (D : ℝ)) : Distribution (feasiblePlans I n D) ℝ :=
  π.scheduleLaw.restrict (feasiblePlans I n D) (by exact real_policy_restriction I D π hπ)

private theorem rationalInputLaw_success {n : ℕ} (D : ℚ) (π : Policy ι ℝ n)
    (hπ : π.Feasible I.realify (D : ℝ)) :
    (rationalInputLaw I D π hπ).mean (fun B => ((B.val.success I : ℚ) : ℝ)) =
      (π.execution I.realify).mean executionSuccess := by
  simp_rw [← Plan.success_realify I]
  rw [rationalInputLaw, Distribution.mean_restrict, (execution_equivalence I.realify π).1]

private theorem rationalInputLaw_cost {n : ℕ} (D : ℚ) (π : Policy ι ℝ n)
    (hπ : π.Feasible I.realify (D : ℝ)) :
    (rationalInputLaw I D π hπ).mean (fun B => ((B.val.expectedCost I : ℚ) : ℝ)) =
      (π.execution I.realify).mean (executionCost I.realify) := by
  simp_rw [← Plan.expectedCost_realify I]
  rw [rationalInputLaw, Distribution.mean_restrict, (execution_equivalence I.realify π).2]

/-- Rational-input full-cover optimum, against arbitrary real-randomized policies.
The returned program samples at most two feasible schedules before calling an oracle;
its actual stopped law equals the optimal policy's law. -/
theorem optimal_rational_program {n : ℕ} (D η : ℚ)
    (hfeas : ∃ π : Policy ι ℝ n, π.Feasible I.realify (D : ℝ) ∧
      (η : ℝ) ≤ (π.execution I.realify).mean executionSuccess) :
    ∃ π : Policy ι ℝ n,
      ∃ program : ProbOracleComp (fun _ : Finset ι => Bool) (Bool × Plan ι n),
        programLaw I.realify program = (π.execution I.realify).toPMF ∧
        π.Feasible I.realify (D : ℝ) ∧ π.scheduleLaw.support.card ≤ 2 ∧
        (η : ℝ) ≤ (π.execution I.realify).mean executionSuccess ∧
        ∀ ψ : Policy ι ℝ n, ψ.Feasible I.realify (D : ℝ) →
          (η : ℝ) ≤ (ψ.execution I.realify).mean executionSuccess →
          (π.execution I.realify).mean (executionCost I.realify) ≤
            (ψ.execution I.realify).mean (executionCost I.realify) := by
  classical
  have hLP : ∃ w : Distribution (feasiblePlans I n D) ℝ,
      (η : ℝ) ≤ w.mean (fun B => ((B.val.success I : ℚ) : ℝ)) := by
    obtain ⟨π,hπ,hη⟩ := hfeas
    exact ⟨rationalInputLaw I D π hπ, by rwa [rationalInputLaw_success]⟩
  obtain ⟨w,sampler,hs,hw,hwp,hwc⟩ := optimal_schedule_sampler I D η hLP
  let law := w.realify.map Subtype.val
  let π := preselect law
  refine ⟨π, preselectProgram (Subtype.val <$> sampler), ?_, ?_, ?_, ?_, ?_⟩
  · apply preselect_program_law
    rw [ProbComp.eval_map, hs, ← Distribution.toPMF_map]
  · intro B hB
    have hzero : ∀ B ∉ feasiblePlans I n D, law.weight B = 0 := by
      intro B hB
      apply sum_eq_zero
      intro C _
      have hCB : C.val ≠ B := fun h => hB (h ▸ C.property)
      simp [hCB]
    rw [preselect_law] at hB
    have hp := (mem_filter.mp hB).2
    have hmem : B ∈ feasiblePlans I n D := by
      by_contra hn
      rw [hzero B hn] at hp
      exact lt_irrefl _ hp
    exact (mem_filter.mp ((feasiblePlans_realify_iff I D B).mpr hmem)).2
  · rw [preselect_law]
    have hcard : w.realify.support.card = w.support.card := by
      simp only [Distribution.support, Distribution.realify, Rat.cast_pos]
    exact (Distribution.support_map_card w.realify Subtype.val).trans (hcard.le.trans hw)
  · rw [(execution_equivalence I.realify π).1, preselect_law, Distribution.mean_map]
    change (η : ℝ) ≤ w.realify.mean (fun B => B.val.success I.realify)
    simp_rw [Plan.success_realify I]
    rw [Distribution.mean_realify]
    exact_mod_cast hwp
  · intro ψ hψ hη
    rw [(execution_equivalence I.realify π).2, preselect_law, Distribution.mean_map]
    change w.realify.mean (fun B => B.val.expectedCost I.realify) ≤ _
    simp_rw [Plan.expectedCost_realify I]
    rw [Distribution.mean_realify]
    have hp : (η : ℝ) ≤ (rationalInputLaw I D ψ hψ).mean
        (fun B => ((B.val.success I : ℚ) : ℝ)) := by rwa [rationalInputLaw_success]
    have := hwc (rationalInputLaw I D ψ hψ) hp
    rwa [rationalInputLaw_cost] at this

end Cslib.Probability.StochasticOracle
