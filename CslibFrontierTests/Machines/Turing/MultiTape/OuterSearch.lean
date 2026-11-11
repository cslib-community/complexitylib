/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native increasing-guess simulation)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.BalancedParameters
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DriverCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluatorCorrect

/-!
# Balanced parameters and increasing-guess regressions

These tests exercise actual parameter values, both Boolean returns, live resumption, the empty
input starting guess and the fixed scanner phase, using Williams's initialized evaluator and
balanced parameters. General semantic proofs cover arbitrary inputs.
-/

public section

namespace CslibFrontierTests.OuterSearch

open Turing MultiTapeTM MultiTapePTM.BlockComputation

example : BalancedParameters.blockWidth 0 = 1 := by decide
example : BalancedParameters.horizon 0 = 0 := by decide
example : BalancedParameters.blockWidth 1 = 2 := by decide
example : BalancedParameters.horizon 1 = 1 := by decide
example : BalancedParameters.blockWidth 16 = 16 := by decide
example : BalancedParameters.horizon 16 = 1 := by decide
example : BalancedParameters.blockWidth 17 = 16 := by decide
example : BalancedParameters.horizon 17 = 2 := by decide
example : BalancedParameters.blockWidth 1024 = 128 := by decide
example : BalancedParameters.horizon 1024 = 8 := by decide

/-- A source that halts on its first step without accepting. -/
def stop : MultiTapeTM 0 Bool (Fin 1) := MultiTapeTM.ofTr 0 fun _ _ _ =>
  { inputTape := .zero, workTapes := Fin.elim0, output := none, state := none }

/-- Williams's initialized evaluator for `stop`. -/
noncomputable abbrev evaluator : ScheduleSearch.Evaluator :=
  InitializedEvaluator.scheduleEvaluator stop (Equiv.refl _)

/-- Williams's balanced parameters. -/
abbrev params : OuterSearch.Parameters := BalancedParameters.parameters

example : params.blockWidth 17 = 16 := by decide
example : params.horizon 17 = 2 := by decide

example : OuterSearch.initial evaluator 0 = .inl (0, 1, none) := rfl
example : OuterSearch.resume evaluator (3, 4, none)
    (.inl ((3, 4, 1), 0, some false)) = (3, 4, some false) := rfl
example : OuterSearch.resume evaluator (3, 4, none)
    (.inl ((3, 4, 1), 0, some true)) = (3, 4, some true) := rfl
example : OuterSearch.resume evaluator (3, 4, none)
    (.inl ((3, 4, 1), 0, none)) = (3, 5, none) := rfl
example : OuterSearch.caller.halted (3, 4, some false) = true := rfl
example : OuterSearch.caller.halted (3, 4, none) = false := rfl
example : OuterSearch.caller.finish (3, 4, some false) = [false] := rfl
example : OuterSearch.caller.finish (3, 4, some true) = [true] := rfl

example : (Driver.machine evaluator 0 params).run [] 1 = .inl (0, true) := rfl
example : (Driver.machine evaluator 0 params).run [] 2 =
    .inr (OuterSearch.initial evaluator 0) := rfl
example : (Driver.machine evaluator 0 params).run [true, false] 2 =
    .inl (2, false) := rfl
example : (Driver.machine evaluator 0 params).run [true, false] 4 =
    .inr (OuterSearch.initial evaluator 2) := rfl

/-- The complete driver correctness theorem has a concrete rejecting source instance. -/
example : ∃ T, (Driver.machine evaluator 0 params).halted
    ((Driver.machine evaluator 0 params).run [] T) = true ∧
    (Driver.machine evaluator 0 params).output [] T = [false] := by
  have hsource : (stop.runFrom (Cfg.init stop.q₀ []) 1).Halted := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (q := 0) rfl]
    simp [stop, Action.apply]
  have houtput : (stop.runFrom (Cfg.init stop.q₀ []) 1).output = [] := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (q := 0) rfl]
    simp [stop, Action.apply]
  obtain ⟨T, _, hhalt, hout, _⟩ := Driver.exists_first_decision params
    (InitializedEvaluator.scheduleEvaluator_correct stop (Equiv.refl _)) [] 1 hsource
  rw [houtput] at hout
  exact ⟨T, hhalt, hout⟩

end CslibFrontierTests.OuterSearch
