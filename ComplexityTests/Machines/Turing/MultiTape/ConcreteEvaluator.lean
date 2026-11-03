/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of concrete implicit evaluation)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteEvaluatorCorrect

/-!
# Concrete evaluator regressions

A complete height-zero tree evaluation calls the concrete node supplier, returns its initial
source vector and decodes its actual physical bank. The fixed machine's default initialization
is halted; runtime metadata and bank are supplied explicitly.
-/

public section

namespace ComplexityTests.ConcreteEvaluator

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open Cslib.TreeEval.Ary.Packed

/-- A singleton control-state encoding. -/
abbrev code : Fin 1 ≃ Fin 1 := Equiv.refl _

/-- The computation used by the implicit tree has no work tapes and halts in one step. -/
def control : MultiTapeTM 0 Bool (Fin 1) := MultiTapeTM.ofTr 0 fun _ _ _ =>
  { inputTape := .zero, workTapes := fun _ => (none, .zero), output := none, state := none }

/-- A zero bank with paid assignment capacity and a coefficient-one root request. -/
def initial : ConcreteEvaluator.State 0 (Fin 1) :=
  .inl ((1, 1, 0, 0, 1, 2, 8192), (17, 1, 13), List.replicate 26 17, [], some (1, 0))

/-- Observe the physical bank only while the evaluator caller is active. -/
def observe : ConcreteEvaluator.State 0 (Fin 1) → Option (List ℕ) :=
  Sum.elim (fun (_, _, bank, _, _) => some bank) (fun _ => none)

example : (ConcreteEvaluator.machine control code).halted
    (ConcreteEvaluator.machine control code).init = true := by decide

example : (ConcreteEvaluator.machine control code).halted initial = false := by decide

example : observe ((ConcreteEvaluator.machine control code).runFrom [true] initial 2) =
    some ([18, 18] ++ List.replicate 24 17) := by decide

example : (ConcreteEvaluator.machine control code).halted
    ((ConcreteEvaluator.machine control code).runFrom [true] initial 2) = true := by decide

example : RawController.Output.decode ((13, 1, 17, 13, 0), [18, 18] ++ List.replicate 24 17) =
    [true, true] ++ List.replicate 11 false := by decide

end ComplexityTests.ConcreteEvaluator
