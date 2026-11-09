/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontierTests.NativeBatchPolicy
import CslibFrontier.Computability.Probabilistic.NativeBatch.Retained
import Mathlib.Tactic

/-!
# Nonempty actual retained cover from a correlated concurrent native batch

The actual machine writes its whole first batch. Two simultaneous responses share
one private bit; one completes and one is canceled with a positive bill. The
nonempty ground is covered and locally certified with probability one half. The
postselection envelope is computed from the actual native posterior, not supplied.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle ConcurrentBatch PartialCover AdaptiveSelection
open Cslib.Probability.NativeBatch
open scoped ENNReal
namespace CslibFrontierTests.NativeBatchProgress
open CslibFrontierTests.NativeBatchPolicy
open CslibFrontierTests.ConcurrentBatch (limits sample paths)

/-- A satisfiable nonempty ground with a feasible positive dual. -/
def coverInstance : Instance Unit (Fin 1) where
  ground := {()}
  sets _ := {()}
  sets_subset := by intro _; exact Finset.Subset.rfl
  weight _ := 1
  weight_nonneg := by intro _; norm_num
  dual _ := 1
  dual_nonneg := by intro _; norm_num
  dual_feasible := by intro _; norm_num

/-- Completed proposals from the actual first batch, excluding its canceled call. -/
theorem first_proposals (u : Bool) :
    proposals 1 (firstReceipt u).report = [if u then {0} else ∅] := by
  cases u <;> norm_num [proposals, firstReceipt, ConcurrentBatch.observe, paths,
    CallTrace.report, CallTrace.response, limits, first, List.ofFn_succ,
    encodeFamily, decodeFamily, Finset.mem_filter, List.filterMap_cons, List.filterMap_nil]

private theorem actual_productivity (u : Bool) :
    productive coverInstance 1 (Coverage.proposal 1) 1 [] (some (firstReceipt u)) = u := by
  cases u <;> norm_num [productive, AdaptiveSelection.residual, selected,
    Coverage.proposal, first_proposals,
    Instance.retain, Instance.Certified, coverInstance, Instance.covered, Instance.cost]

/-- The local dual test actually accepts the covering proposal; the canceled
concurrent call does not manufacture a second proposal. -/
example (u : Bool) : Retained.complete coverInstance 1 (traceOne u).records = u := by
  cases u <;> norm_num [Retained.complete, traceOne, selected, Coverage.proposal,
    first_proposals, Instance.retain, Instance.Certified, coverInstance,
    Instance.covered, Instance.cost]

private def picked : Quantitative.Selected 3 0 Bool (Fin 12) [] :=
  ⟨Trace.initial start, some (.pending
    (.query (atState 5 (encodeBatch first) [] start.memory) () 6))⟩

private def observation : Quantitative.Observation 3 := Quantitative.observe limits picked

private theorem selection : Quantitative.select limits sample machine
    (PMF.pure (Trace.initial start)) = PMF.pure picked := by
  simp [Quantitative.select, Trace.initial, first_seek, picked]

private theorem observation_law : (Quantitative.select limits sample machine
    (PMF.pure (Trace.initial start))).map (Quantitative.observe limits) = PMF.pure observation := by
  rw [selection, PMF.pure_map]
  rfl

/-- The true selected conditional law retains all hidden-state/resource correlation. -/
private theorem conditional_law : Quantitative.conditional limits sample machine
    (PMF.pure (Trace.initial start)) observation = (PMF.uniformOfFintype Bool).map traceOne := by
  have h := Quantitative.selection_factor limits sample machine (PMF.pure (Trace.initial start))
  rw [observation_law, PMF.pure_bind, PMF.pure_bind] at h
  apply h.trans
  simpa only [Trace.law, ObservedProcess.stateLaw, PMF.pure_bind] using law_one

/-- Nontrivial productivity is derived from the same actual oracle and machine. -/
theorem productivity_envelope : ∀ t < 1, ∀ o ∈ ((Quantitative.select limits sample machine
      (Trace.law limits sample machine t start)).map (Quantitative.observe limits)).support,
    ENNReal.ofReal (1 / 2 : ℝ) ≤ History.conditionalMean limits sample machine
      (Trace.law limits sample machine t start) o
      (fun h x => if productive coverInstance 1 (Coverage.proposal 1) 1 h x then 1 else 0) := by
  intro t ht o ho
  have ht0 : t = 0 := by omega
  subst t
  change o ∈ ((Quantitative.select limits sample machine
    (PMF.pure (Trace.initial start))).map (Quantitative.observe limits)).support at ho
  rw [observation_law, PMF.mem_support_pure_iff] at ho
  subst o
  change _ ≤ Quantitative.mean (Quantitative.conditional limits sample machine
    (PMF.pure (Trace.initial start)) observation) _
  rw [conditional_law]
  simp only [Quantitative.mean, PMF.tsum_map_mul, History.newest, traceOne,
    List.tail_cons, List.headD_cons, actual_productivity]
  norm_num [tsum_bool, PMF.uniformOfFintype_apply, ENNReal.ofReal_div_of_pos]

/-- The generalized native comparison applies to a genuine nonempty cover,
not only a resource-only or zero-ground fixture. -/
example : ENNReal.ofReal (∫ j, (if 1 ≤ j then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial 1 ⟨1 / 2, by norm_num⟩) ≤
    (Trace.law limits sample machine 1 start).map
      (fun state => Retained.complete coverInstance 1 state.records) true :=
  Retained.completion limits sample machine coverInstance 1 1 1 1 (by simp [coverInstance])
    ⟨1 / 2, by norm_num⟩ start productivity_envelope

/-- Source per-selected-batch cost is computed from both correlated branches. -/
private theorem cost_envelope : ∀ t < 1, ∀ o ∈ ((Quantitative.select limits sample machine
      (Trace.law limits sample machine t start)).map (Quantitative.observe limits)).support,
    o.issued = true → Quantitative.conditionalMean limits sample machine
      (Trace.law limits sample machine t start) o Trace.charge ≤ 7 := by
  intro t ht o ho _
  have ht0 : t = 0 := by omega
  subst t
  change o ∈ ((Quantitative.select limits sample machine
    (PMF.pure (Trace.initial start))).map (Quantitative.observe limits)).support at ho
  rw [observation_law, PMF.mem_support_pure_iff] at ho
  subst o
  change Quantitative.mean (Quantitative.conditional limits sample machine
    (PMF.pure (Trace.initial start)) observation) _ ≤ _
  rw [conditional_law]
  simp only [Quantitative.mean, PMF.tsum_map_mul, Quantitative.newest, traceOne,
    List.headD_cons, Trace.charge]
  norm_num [tsum_bool, PMF.uniformOfFintype_apply,
    (first_resources true).2, (first_resources false).2]
  have hhalf : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    _ = (2 : ℝ≥0∞)⁻¹ * (2 * 7) := by norm_num [← mul_add]
    _ ≤ 7 := by rw [← mul_assoc, hhalf, one_mul]

private theorem stop_envelope : ∀ t < 1, ∀ o ∈ ((Quantitative.select limits sample machine
      (Trace.law limits sample machine t start)).map (Quantitative.observe limits)).support,
    o.issued = true → Retained.complete coverInstance 1 o.history = false := by
  intro t ht o ho _
  have ht0 : t = 0 := by omega
  subst t
  change o ∈ ((Quantitative.select limits sample machine
    (PMF.pure (Trace.initial start))).map (Quantitative.observe limits)).support at ho
  rw [observation_law, PMF.mem_support_pure_iff] at ho
  subst o
  norm_num [observation, Quantitative.observe, picked, Trace.initial, Retained.complete,
    selected, coverInstance, Instance.covered]

/-- The stopped survival-sum result applies to real native receipts and a nonzero
cost. The later policy is not claimed to be a uniform stopping selector. -/
example : Quantitative.expected limits sample machine Trace.charge 1 start ≤ 7 := by
  have h := Retained.cost_tail_sum limits sample machine coverInstance 1 1 1 1
    (by simp [coverInstance]) ⟨1 / 2, by norm_num⟩ 7 start
    productivity_envelope stop_envelope cost_envelope
  simpa [binomialFailure, bernoulliExpectation] using h

/-- Caps are genuine: revealing the singleton cannot satisfy a zero-new-coverage cap. -/
example : (revealed coverInstance (Coverage.proposal 1) [some (firstReceipt true)] \
    revealed coverInstance (Coverage.proposal (n := 3) 1) []).card = 1 := by
  norm_num [revealed, Coverage.proposal, first_proposals, coverInstance, Instance.covered]

/-- The actual returned-proposal cover is satisfiable, and its cost equals the dual. -/
example : coverInstance.covered {0} = coverInstance.ground ∧ coverInstance.cost {0} = 1 := by
  norm_num [coverInstance, Instance.covered, Instance.cost]

/-- A later deadline-canceled batch does not create progress on the correlated
failure branch. The resource-only two-batch code is not silently treated as an
upper selector satisfying a positive productivity envelope at every reached turn. -/
example : productive coverInstance 1 (Coverage.proposal 1) 1
    [some (firstReceipt false)] (some (secondReceipt false)) = false := by
  have hs : proposals 1 (secondReceipt false).report = [] := by
    norm_num [proposals, secondReceipt, ConcurrentBatch.observe, paths, second,
      CslibFrontierTests.ConcurrentBatch.second,
      CallTrace.report, CallTrace.response, limits, List.ofFn_succ,
      Finset.mem_filter, List.filterMap_cons, List.filterMap_nil]
  norm_num [productive, AdaptiveSelection.residual, selected, Coverage.proposal,
    first_proposals, hs, Instance.retain, Instance.Certified, coverInstance,
    Instance.covered, Instance.cost]

/-- Empty ground is a distinct, satisfiable set-cover instance. -/
def emptyInstance : Instance Unit (Fin 1) where
  ground := ∅
  sets _ := ∅
  sets_subset := by intro _; exact Finset.Subset.rfl
  weight _ := 1
  weight_nonneg := by intro _; norm_num
  dual _ := 0
  dual_nonneg := by intro _; norm_num
  dual_feasible := by intro _; norm_num

/-- The native initial receipt history already covers empty ground at zero epochs,
with zero required productive turns, including the certain-progress edge parameter. -/
example : ENNReal.ofReal (∫ j, (if 0 ≤ j then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial 0 ⟨1, by norm_num⟩) ≤
    (Trace.law limits sample machine 0 start).map
      (fun state => Retained.complete emptyInstance 1 state.records) true :=
  Retained.completion limits sample machine emptyInstance 1 1 0 0 (by simp [emptyInstance])
    ⟨1, by norm_num⟩ start (by intro t ht; omega)

/-- Zero ground and `p = 1` are admitted without a positive target-count premise. -/
example : ENNReal.ofReal (∫ j, (if 0 ≤ j then (1 : ℝ) else 0)
      ∂ProbabilityTheory.binomial 0 ⟨1, by norm_num⟩) = 1 := by
  norm_num

end CslibFrontierTests.NativeBatchProgress
