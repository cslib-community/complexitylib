/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOptimum
import CslibFrontierTests.NativeBatchSuccess
import Mathlib.Tactic

/-!
# Native necessary deadline success: positive output and universal failure edges

The positive client uses the actual successful packet-writing machine's terminal
law to check certified-to-cover readback. The deadline edge has nonempty ground,
one available turn and arbitrary correlated source randomness: zero oracle time
makes every positive success target infeasible for every admitted native machine.
The positive-duration source theorem is also exercised by NativeBatchSuccess's
existing nonempty one-turn client; no elapsed-turn conclusion is supplied there.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution StochasticOracle NativeRetention
open ConcurrentBatch NativeBatch Trace Quantitative PartialCover
open scoped NNReal ENNReal
open MeasureTheory

private abbrev data : GuardedStartup.Input := ⟨⟨⟨[[0]], [1], [1], 1, []⟩, 1, 1, []⟩, 1⟩
private theorem valid : Valid data.startup.system := by
  constructor
  · intro j; cases j <;> norm_num [data]
  · intro e; cases e <;> norm_num [data]
  · intro j; cases j <;> norm_num [data, elements, ground, List.range_succ]

open CslibFrontierTests.NativeBatchSuccess in
/-- The event bridge also applies to a concrete successful native program on
its actual unbounded terminal law, independently of the startup input format. -/
example :
    let μ := NativeUnboundedExecution.terminal machine
      (environment limits
        sample) start
    (μ.map (BatchOutput.certified limits
      data.startup.system valid)) true = 1 ∧
    (μ.map (Coverage.nativeSuccess
      (BatchOutput.accept data.startup.system valid))) true =
      1 := by
  classical
  have hread : NativeOpenSelection.result (decodeFamily data.startup.system.rows.length)
      done = some ({0} : Finset (Fin 1)) := by
    change decodeFamily 1 [true] = some {0}
    simpa [encodeFamily, List.ofFn_succ] using
      (decodeFamily_encode ({0} : Finset (Fin 1)))
  have himage : (({0} : Finset (Fin data.startup.system.rows.length)).image Fin.val) =
      ({0} : Finset ℕ) := by simp
  have hi := NativeBatch.terminal_invariant limits
    sample machine
    start done
    (NativeBatch.initial_invariant _ ())
    (by simp [terminal_law])
  obtain ⟨hwell, _, _, _⟩ := hi
  obtain ⟨_, _, hd, _, _⟩ := hwell
  have hcert : BatchOutput.certified limits
      data.startup.system valid (some done) = true := by
    dsimp only [data] at hread ⊢
    simp only [BatchOutput.certified, Option.any_some, hread]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true ⟨?_, ?_⟩, decide_eq_true hd⟩ <;> rw [himage] <;>
      norm_num [instanceOf, Instance.covered, Instance.cost, data, elements, ground]
  have hcov := BatchOptimum.certified_le_accepted limits
    data.startup.system valid (PMF.pure (some done))
  simp only [PMF.pure_map, PMF.pure_apply, hcert, ↓reduceIte] at hcov
  dsimp only
  rw [terminal_law]
  constructor
  · simp [PMF.pure_map, PMF.pure_apply, hcert]
  · apply le_antisymm (PMF.coe_le_one _ _)
    simpa only [PMF.pure_map, PMF.pure_apply] using hcov

private def zeroLimits : Limits 1 := ⟨fun _ => 1, by intro _; norm_num, 0, 1⟩

/-- Positive conditional progress/cost envelopes are not used on null issued
signals: source byte-level deadline admission proves there are no such signals. -/
private theorem envelopes {Private : Type} (sample : Sampler 1 Private) (seed : Private) :
    BatchOptimum.LowerEnvelopes zeroLimits sample data seed valid 1 1 1 := by
  constructor
  intro k Control _ machine
  dsimp only
  intro _ t _ o ho
  have hz := Deadline.no_call_zero_deadline zeroLimits sample machine rfl _ o ho
  constructor
  · intro next _
    have hs : AdaptiveSelection.revealed (BatchOptimum.finiteInstance data.startup.system valid)
        (Coverage.proposal data.startup.system.rows.length) next.records ⊆
        (BatchOptimum.finiteInstance data.startup.system valid).ground := by
      rw [Coverage.revealed_source]
      exact Instance.covered_subset _ _
    calc
      _ ≤ (BatchOptimum.finiteInstance data.startup.system valid).ground.card :=
        Finset.card_le_card (Finset.sdiff_subset.trans hs)
      _ = 1 := by norm_num [BatchOptimum.finiteInstance, instanceOf, data, ground,
        List.range_succ]
  constructor <;> intro hi <;> simp [hz] at hi

/-- Even one advertised turn cannot overcome zero actual oracle time on a
nonempty instance; every positive success target has OPT = infinity. -/
example {Private : Type} (sample : Sampler 1 Private) (seed : Private) :
    BatchOptimum.costs zeroLimits sample data seed valid 1 = ∅ ∧
    BatchOptimum.optimum zeroLimits sample data seed valid 1 = ∞ := by
  have hb := BatchOptimum.feasible_success_le zeroLimits sample data seed valid 1 1 1
    (by intro q hq; have hq0 : q = 0 := by omega
        subst q; norm_num [instanceOf, data, ground, List.range_succ])
    ⟨1, by norm_num⟩ 1 1 (by norm_num) (by simpa using envelopes sample seed)
    (by
      intro k Control _ machine
      dsimp only
      intro _ t _ o ho hi
      have hz := Deadline.no_call_zero_deadline zeroLimits sample machine rfl _ o ho
      simp [hz] at hi)
  have he : BatchOptimum.costs zeroLimits sample data seed valid 1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have h := hb ⟨v, hv⟩
    norm_num [Deadline.effectiveTurns, zeroLimits, ProbabilityTheory.binomial_zero] at h
  exact ⟨he, by simp [BatchOptimum.optimum, he]⟩
