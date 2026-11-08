/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Probabilistic.NativeInterface
import ComplexityTests.NativeOpenExecution
import ComplexityTests.NativeUnboundedExecution
import Complexity.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Actual open PTM coin/interface/stopped-law connection

The complete native fixtures execute work-tape storage with two correlated oracle
calls and a geometric private-coin waiting loop. These clients check the actual
query buffer before dispatch, saved random-tape replay, hidden memory after a
correlated reply, and the full unbounded interface/behavioral outcome law.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution
open scoped ENNReal NNReal
namespace ComplexityTests.NativeInterface

open ComplexityTests.NativeOpenExecution in
/-- The actual first query is selected from the written buffer before any
response is sampled; its work tape and private state remain inside `drawn b`. -/
example (b bit : Bool) : Cslib.Probability.NativeInterface.instruction machine (drawn b) bit =
    .query (drawn b) () .decide := rfl

open ComplexityTests.NativeOpenExecution in
example (b bit : Bool) : Cslib.Probability.NativeInterface.signal
      (Cslib.Probability.NativeInterface.instruction machine (drawn b) bit) =
    .query [] () [false] := rfl

open ComplexityTests.NativeOpenExecution in
/-- The second actual selected query depends on the private work-tape bit and
first reply, without revealing a later reply. Its prior record is retained. -/
example (b u bit : Bool) : Cslib.Probability.NativeInterface.signal
      (Cslib.Probability.NativeInterface.instruction machine (prepared b u) bit) =
    .query [⟨(), [false], firstReply u⟩] () [b ^^ u] := rfl

open ComplexityTests.NativeOpenExecution in
/-- Dispatch shares the same oracle bit across calls and keeps the private
native work tape, raw answer, history and response-dependent resources jointly. -/
example (b u : Bool) : Cslib.Probability.NativeInterface.dispatch env
      (.query (prepared b u) () .finish) = PMF.pure (answeredAgain b u) := by
  simp [Cslib.Probability.NativeInterface.dispatch, env, prepared, answered, drawn, start,
    machine, action, Turing.Action.apply, Turing.MultiTapeMachine.Config.step,
    Turing.MultiTapeMachine.Config.receive, Memory.record, answeredAgain, laterReply,
    Turing.MultiTapeMachine.initialConfig]

open ComplexityTests.NativeOpenExecution in
/-- Averaging actual saved private coin tapes preserves the full world law,
including the native early halt and both correlated oracle calls. -/
example : (BitString.uniformList 5).bind
      (fun coins => Cslib.Probability.NativeInterface.replay machine env coins start) =
    (PMF.uniformOfFintype Bool).bind (fun b =>
      (PMF.uniformOfFintype Bool).map (finalWorld b)) := by
  rw [← Cslib.Probability.NativeInterface.execute_coins, native_joint_law]

section Conditional
open ComplexityTests.NativeUnboundedExecution
open Cslib.Probability.NativeInterface

private def q : Instruction 0 Control Unit Bool [] := .query start () .finish

private def querySignal : Signal Unit := .query [] () []

/-- The actual native private coin selects a query with probability one half,
measured before the oracle samples its correlated reply and charges. -/
private theorem selected_query_mass :
    (prepare machine start).map signal querySignal = (2 : ℝ≥0∞)⁻¹ := by
  norm_num [prepare, PMF.map_comp, PMF.map_apply, tsum_bool, instruction, machine, start,
    Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init, signal, querySignal,
    PMF.uniformOfFintype_apply]

private theorem selected_instruction_mass : prepare machine start q = (2 : ℝ≥0∞)⁻¹ := by
  norm_num [prepare, PMF.map_apply, tsum_bool, instruction, machine, start,
    Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init, q, PMF.uniformOfFintype_apply]

/-- The positive-probability selected query has its derived actual hidden
posterior; this is not a supplied response-law or representation hypothesis. -/
private theorem query_posterior : PMF.posterior (prepare machine start) signal querySignal =
    PMF.pure q := by
  classical
  have hf := PMF.posterior_factor (prepare machine start) signal querySignal q
  rw [selected_query_mass, selected_instruction_mass] at hf
  have hs : signal q = querySignal := rfl
  rw [ite_eq_left hs] at hf
  have he : PMF.posterior (prepare machine start) signal querySignal q = 1 :=
    (ENNReal.mul_right_inj (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0) (by norm_num)).mp
      (by simpa only [mul_one] using hf)
  have hsupport := (PMF.apply_eq_one_iff _ _).mp he
  ext chosen
  by_cases hc : chosen = q
  · subst chosen
    simpa using he
  · have hz : chosen ∉ (PMF.posterior (prepare machine start) signal querySignal).support := by
      simpa only [hsupport, Set.mem_singleton_iff] using hc
    rw [(PMF.apply_eq_zero_iff _ _).mpr hz]
    simp [PMF.pure_apply, hc]

/-- Conditional dispatch is the actual raw reply law, with the same native
answer buffer, private oracle bit and jointly correlated cost/duration receipt. -/
example : conditionalResponse machine env (PMF.pure start) querySignal =
    (PMF.uniformOfFintype Bool).map answered := by
  simp only [conditionalResponse, PMF.pure_bind, query_posterior, dispatch, q, env,
    PMF.map_comp]
  rfl

end Conditional

open ComplexityTests.NativeUnboundedExecution in
/-- A fully derived unbounded native stopped law survives the actual two-phase
interface refinement. There is no uniformly sufficient local instruction clock. -/
example : Cslib.Probability.NativeInterface.terminal machine env start =
    (PMF.uniformOfFintype Bool).map (fun u => some
      (Cslib.Probability.NativeInterface.Phase.ready (done u))) := by
  rw [Cslib.Probability.NativeInterface.terminal_native, terminal_law, PMF.map_comp]
  rfl

open ComplexityTests.NativeUnboundedExecution in
/-- End-to-end actual interface law agrees with the constructed unbounded
behavioral selector, preserving the complete stopped public view. -/
example : (Cslib.Probability.NativeInterface.terminal machine env start).map
      (Option.map fun phase => NativeOpenSelection.view parse decode
        (Cslib.Probability.NativeInterface.worldOf phase)) =
    NativeUnboundedExecution.behavioral machine env parse decode start :=
  Cslib.Probability.NativeInterface.terminal_behavioral machine env parse decode start

open ComplexityTests.NativeUnboundedExecution in
example : (Cslib.Probability.NativeInterface.terminal machine env start).map
      (Option.map fun phase => NativeOpenSelection.outcome accept
        (NativeOpenSelection.view parse decode
          (Cslib.Probability.NativeInterface.worldOf phase))) =
    (PMF.uniformOfFintype Bool).map (fun u => some (NativeOpenSelection.outcome accept
      ⟨(done u).memory.events, true, NativeOpenSelection.result decode (done u)⟩)) := by
  rw [Cslib.Probability.NativeInterface.terminal_outcome machine env parse decode accept
    start selection_only, terminal_law, PMF.map_comp]
  rfl

open ComplexityTests.NativeUnboundedExecution in
/-- Sure divergence remains divergence under the actual interface connection. -/
example : Cslib.Probability.NativeInterface.terminal diverging env start = PMF.pure none := by
  rw [Cslib.Probability.NativeInterface.terminal_native, diverging_terminal]
  simp

open ComplexityTests.NativeUnboundedExecution in
example : (∑' phase, Cslib.Probability.NativeInterface.terminal machine env start phase *
      phase.elim 0 (fun phase => (tokenBill
        (Cslib.Probability.NativeInterface.worldOf phase).memory.events : ℝ≥0∞))) = 4 := by
  rw [Cslib.Probability.NativeInterface.terminal_native, PMF.tsum_map_mul]
  convert expected_terminal_bill using 1
  apply tsum_congr
  intro next
  cases next <;> rfl

end ComplexityTests.NativeInterface
