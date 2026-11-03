/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native root classification and schedule search)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchCorrect

/-!
# Root decisions and sequential search regressions

Both accepting and rejecting halted roots stop search; a live root advances the counter.
Header classification includes the existing decoder's unused-control-rank behavior. Counter
tests cover the exact first excluded schedule and the zero-horizon boundary.
-/

public section

namespace ComplexityTests.ScheduleSearch

open Turing MultiTapeTM MultiTapePTM.BlockComputation

/-- The singleton control-state encoding used by the numeric header examples. -/
abbrev code : Fin 1 ≃ Fin 1 := Equiv.refl _

example : RootDecision.classify 0 code (1, [true, false, false, false, true, false]) =
    some true := by decide
example : RootDecision.classify 0 code (1, [true, false, false, false, false, false]) =
    some false := by decide
example : RootDecision.classify 0 code (1, [true, false, false, false, true, true]) =
    some false := by decide
example : RootDecision.classify 0 code (1, [true, true, false, false, true, false]) =
    none := by decide
example : RootDecision.classify 0 code (1, [false, false, false, false, true, false]) =
    none := by decide
example : RootDecision.classify 0 code (1, [true, true, true, false, true, false]) =
    some true := by decide
example : RootDecision.classify 0 code (1, []) = none := by decide
example : RootDecision.classify 0 code (0, [true]) = none := by decide

example : ScheduleCounter.valid 0 (8, 2) = true := by decide
example : ScheduleCounter.valid 0 (9, 2) = false := by decide
example : ScheduleCounter.remaining 0 (9, 2) = 1 := by decide
example : ScheduleCounter.valid 0 (0, 0) = true := by decide
example : ScheduleCounter.valid 0 (1, 0) = false := by decide

/-- A completed initialized evaluator with a two-chunk physical target bank. -/
def returned (first second : ℕ) : InitializedEvaluator.State 0 (Fin 1) :=
  .inr (.inl ((1, 1, 0, 1, 3, 8, 64), (17, 1, 2), [first, second, 17, 17], [], none))

example : ScheduleSearch.resume code ((1, 1, 1), 1, none) (returned 18 17) =
    ((1, 1, 1), 1, some false) := by decide
example : ScheduleSearch.resume code ((1, 1, 1), 1, none) (returned 18 19) =
    ((1, 1, 1), 1, some true) := by decide
example : ScheduleSearch.resume code ((1, 1, 1), 1, none) (returned 20 17) =
    ((1, 1, 1), 2, none) := by decide
example : (ScheduleSearch.caller 0).halted ((1, 1, 1), 1, some false) = true := by decide
example : (ScheduleSearch.caller 0).halted ((1, 1, 1), 3, none) = true := by decide
example : (ScheduleSearch.caller 0).halted ((1, 1, 1), 2, none) = false := by decide

end ComplexityTests.ScheduleSearch
