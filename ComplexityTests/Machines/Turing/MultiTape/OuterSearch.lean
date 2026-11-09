/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native increasing-guess simulation)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.DriverCorrect

/-!
# Balanced parameters and increasing-guess regressions

These tests exercise actual parameter values, both Boolean returns, live resumption, the empty
input starting guess and the fixed scanner phase. General semantic proofs cover arbitrary inputs.
-/

public section

namespace ComplexityTests.OuterSearch

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

example : OuterSearch.initial (k := 0) (Q := Fin 1) 0 = .inl (0, 1, none) := rfl
example : OuterSearch.resume (k := 0) (Q := Fin 1) (3, 4, none)
    (.inl ((3, 4, 1), 0, some false)) = (3, 4, some false) := rfl
example : OuterSearch.resume (k := 0) (Q := Fin 1) (3, 4, none)
    (.inl ((3, 4, 1), 0, some true)) = (3, 4, some true) := rfl
example : OuterSearch.resume (k := 0) (Q := Fin 1) (3, 4, none)
    (.inl ((3, 4, 1), 0, none)) = (3, 5, none) := rfl
example : OuterSearch.caller.halted (3, 4, some false) = true := rfl
example : OuterSearch.caller.halted (3, 4, none) = false := rfl
example : OuterSearch.caller.finish (3, 4, some false) = [false] := rfl
example : OuterSearch.caller.finish (3, 4, some true) = [true] := rfl

/-- A source that halts on its first step without accepting. -/
def stop : MultiTapeTM 0 Bool (Fin 1) := MultiTapeTM.ofTr 0 fun _ _ _ =>
  { inputTape := .zero, workTapes := Fin.elim0, output := none, state := none }

example : (Driver.machine stop (Equiv.refl _)).run [] 1 = .inl (0, true) := rfl
example : (Driver.machine stop (Equiv.refl _)).run [] 2 =
    .inr (OuterSearch.initial 0) := rfl
example : (Driver.machine stop (Equiv.refl _)).run [true, false] 2 =
    .inl (2, false) := rfl
example : (Driver.machine stop (Equiv.refl _)).run [true, false] 4 =
    .inr (OuterSearch.initial 2) := rfl

/-- The complete driver correctness theorem has a concrete rejecting source instance. -/
example : ∃ T, (Driver.machine stop (Equiv.refl _)).halted
    ((Driver.machine stop (Equiv.refl _)).run [] T) = true ∧
    (Driver.machine stop (Equiv.refl _)).output [] T = [false] := by
  have hsource : (stop.runFrom (Cfg.init stop.q₀ []) 1).Halted := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (q := 0) rfl]
    simp [stop, Action.apply]
  have houtput : (stop.runFrom (Cfg.init stop.q₀ []) 1).output = [] := by
    rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (q := 0) rfl]
    simp [stop, Action.apply]
  obtain ⟨T, _, hhalt, hout, _⟩ := Driver.exists_first_decision stop (Equiv.refl _) [] 1 hsource
  rw [houtput] at hout
  exact ⟨T, hhalt, hout⟩

end ComplexityTests.OuterSearch
