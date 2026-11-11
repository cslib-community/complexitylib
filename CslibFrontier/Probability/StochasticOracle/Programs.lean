/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.FullCover
public import CslibFrontier.Probability.FiniteTable
public import CslibFrontier.Languages.Probabilistic.RationalCoin
public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Foundations.Optimization.RationalOneConstraint
import Mathlib.Tactic

/-!
# Programs realizing full-cover schedules

The selection phase is an actual `ProbOracleComp` program. Its external query is
a concurrent batch; the handler runs its calls through their prescribed cutoffs.
The empty batch is a virtual no-op. The batch's Boolean reply reports whether an
accepted full cover was found. Failure-invariant independent calls give the
`batchReply` law from `FullCover`.

`sample_two` realizes every rational two-schedule table exactly, including pure
endpoints. It uses finite-uniform sampling and asserts no strict worst-case
fair-coin runtime. `follow_program_law` connects execution of an actual program
to the stopped-trace semantics, rather than postulating the desired cost or
success of an optimizer. Source: [Wang2027], Theorem 1, PDF pp. 6–7.

## Main results

* `follow_program_law`, `preselect_program_law`: actual program execution laws.
* `optimal_schedule_sampler`: exact sampling of a rational LP optimum.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Cslib.Optimization.OneConstraint Finset
variable {ι : Type} [Fintype ι]

/-- Select between two schedules using an exact rational probability. -/
@[expose] def samplePair {α : Type} (a b : α) (q : ℚ) (h₀ : 0 ≤ q) (h₁ : q ≤ 1) :
    ProbComp α := do
  let chooseFirst ← ProbComp.rationalCoin q h₀ h₁
  return if chooseFirst then a else b

/-- The sampler's exact mass function agrees with the interpreted two-index table. -/
theorem samplePair_law {α : Type} [Fintype α] (a b : α) (q : ℚ)
    (h₀ : 0 ≤ q) (h₁ : q ≤ 1) :
    ProbComp.eval (samplePair a b q h₀ h₁) = (pair a b q h₀ h₁).realify.toPMF := by
  classical
  ext i
  apply (ENNReal.toReal_eq_toReal_iff' ((ProbComp.eval _).apply_ne_top i)
    (((pair a b q h₀ h₁).realify.toPMF).apply_ne_top i)).mp
  rw [samplePair, ProbComp.eval_bind, PMF.bind_apply_toReal, Distribution.toPMF_real]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
    _root_.PMF.pure_apply, ProbComp.rationalCoin_true, ProbComp.rationalCoin_false,
    Distribution.realify, pair]
  by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all

/-- Every rational table on at most two schedules has an exact probabilistic sampler. -/
theorem sample_two {α : Type} [Fintype α] (w : Distribution α ℚ)
    (hw : w.support.card ≤ 2) :
    ∃ sampler : ProbComp α, ProbComp.eval sampler = w.realify.toPMF := by
  obtain ⟨a,b,q,h₀,h₁,rfl⟩ := exists_eq_pair w hw
  exact ⟨samplePair a b q h₀ h₁, samplePair_law a b q h₀ h₁⟩

open scoped Classical in
/-- Run a schedule through concurrent-batch oracle calls, stopping on the first
accepted cover. Empty padded batches cause no underlying call. -/
@[expose] def followProgram : {n : ℕ} → Plan ι n →
    ProbOracleComp (fun _ : Finset ι => Bool) (Bool × Plan ι n)
  | 0, _ => pure (false, ())
  | n+1, (A,B) =>
      if A = ∅ then
        (fun (accepted,trace) => (accepted,(A,trace))) <$> followProgram B
      else do
        let success ← ProbOracleComp.query A
        if success then return (true, (A, Plan.empty n))
        else (fun (accepted,trace) => (accepted,(A,trace))) <$> followProgram B

/-- Interpret private uniform sampling and fresh concurrent-batch responses separately. -/
@[expose] def programLaw (I : FullCoverInstance ι ℝ) {α : Type}
    (program : ProbOracleComp (fun _ : Finset ι => Bool) α) : PMF α :=
  OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
    (fun A => (I.batchReply A).toPMF)) program

/-- Actual program execution has exactly the stopped-trace distribution already
used in the policy/LP theorem. -/
theorem follow_program_law (I : FullCoverInstance ι ℝ) {n : ℕ} (B : Plan ι n) :
    programLaw I (followProgram B) = ((followPlan (K := ℝ) B).execution I).toPMF := by
  induction n with
  | zero => cases B; simp [programLaw, followProgram, followPlan, Policy.execution,
      Distribution.toPMF_pure]
  | succ n ih =>
    rcases B with ⟨A,B⟩
    by_cases hA : A = ∅
    · subst A
      simp only [programLaw, followProgram, ↓reduceIte, OracleComp.interpret_map,
        followPlan, Policy.execution, FullCoverInstance.batchReply_empty,
        Distribution.toPMF_bind, Distribution.toPMF_pure, _root_.PMF.pure_bind,
        Bool.false_eq_true, Distribution.toPMF_map]
      exact congrArg (fun p : PMF (Bool × Plan ι n) =>
        p.map (fun (accepted,trace) => (accepted,((∅ : Finset ι),trace)))) (ih B)
    · simp only [programLaw, followProgram, hA, ↓reduceIte, OracleComp.interpret_bind,
        ProbOracleComp.interpret_query, followPlan, Policy.execution, Distribution.toPMF_bind]
      congr 1
      funext b
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_map,
          Distribution.toPMF_map]
        exact congrArg (fun p => p.map (fun (accepted,trace) => (accepted,(A,trace)))) (ih B)
      · simp only [↓reduceIte, OracleComp.interpret_pure, Distribution.toPMF_pure,
          PMF.monad_pure_eq_pure]

/-- Sample a full schedule before the first call and then execute it. -/
@[expose] def preselectProgram {n : ℕ} (sampler : ProbComp (Plan ι n)) :
    ProbOracleComp (fun _ : Finset ι => Bool) (Bool × Plan ι n) := do
  let B ← ProbOracleComp.sample sampler
  followProgram B

/-- The program realizes the specified schedule mixture, with the same stopping rule. -/
theorem preselect_program_law (I : FullCoverInstance ι ℝ) {n : ℕ}
    (w : Distribution (Plan ι n) ℝ) (sampler : ProbComp (Plan ι n))
    (hs : ProbComp.eval sampler = w.toPMF) :
    programLaw I (preselectProgram sampler) = ((preselect w).execution I).toPMF := by
  simp only [programLaw, preselectProgram, OracleComp.interpret_bind,
    ProbOracleComp.interpret_sample, Policy.execution, preselect, Distribution.toPMF_bind]
  change (ProbComp.eval sampler).bind (fun B => programLaw I (followProgram B)) = _
  rw [hs]
  exact congrArg (fun k => w.toPMF.bind k) (funext fun B => follow_program_law I B)

/-- The rational LP optimum is implementable as an actual schedule-selection program
and is optimal even against feasible real probability tables. -/
theorem optimal_schedule_sampler {n : ℕ} (I : FullCoverInstance ι ℚ) (D η : ℚ)
    (hfeas : ∃ w : Distribution (feasiblePlans I n D) ℝ,
      (η : ℝ) ≤ w.mean (fun B => ((B.val.success I : ℚ) : ℝ))) :
    ∃ w : Distribution (feasiblePlans I n D) ℚ,
      ∃ sampler : ProbComp (feasiblePlans I n D),
        ProbComp.eval sampler = w.realify.toPMF ∧ w.support.card ≤ 2 ∧
        η ≤ w.mean (fun B => B.val.success I) ∧
        ∀ v : Distribution (feasiblePlans I n D) ℝ,
          (η : ℝ) ≤ v.mean (fun B => ((B.val.success I : ℚ) : ℝ)) →
          (w.mean (fun B => B.val.expectedCost I) : ℝ) ≤
            v.mean (fun B => ((B.val.expectedCost I : ℚ) : ℝ)) := by
  obtain ⟨w,hw,hwp,hwc⟩ := exists_rational_optimal_two
    (fun B : feasiblePlans I n D => B.val.success I)
    (fun B : feasiblePlans I n D => B.val.expectedCost I) η hfeas
  obtain ⟨sampler,hs⟩ := sample_two w hw
  exact ⟨w,sampler,hs,hw,hwp,hwc⟩

end Cslib.Probability.StochasticOracle
