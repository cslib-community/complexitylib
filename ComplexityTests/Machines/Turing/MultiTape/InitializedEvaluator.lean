/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of streamed initialized evaluation)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluatorCorrect

/-!
# Streamed initialization and evaluation regressions

The assignment capacity stops growing when the child-register portion is complete. Selected
metadata then drives a complete initialized height-zero evaluation without a supplied bank.
-/

public section

namespace ComplexityTests.InitializedEvaluator

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open Cslib.TreeEval.Ary.Packed

/-- A small generic initializer with two child cells and four total bank cells. -/
def seed : Initializer.State := (((1, 1, 0, 0), (1, 2, 2, 17)), 0, [], 1)

example : (Initializer.machine 0).runFrom [] seed 1 =
    (((1, 1, 0, 0), (1, 2, 2, 17)), 1, [17], 2) := by decide

example : (Initializer.machine 0).runFrom [] seed 3 =
    (((1, 1, 0, 0), (1, 2, 2, 17)), 3, [17, 17, 17], 4) := by decide

example : (Initializer.machine 0).runFrom [] seed 4 =
    (((1, 1, 0, 0), (1, 2, 2, 17)), 4, [17, 17, 17, 17], 4) := by decide

example : (Initializer.machine 0).halted
    (((1, 1, 0, 0), (0, 0, 0, 0)), 0, [], 1) = true := by decide

example : Initializer.step 0 (((0, 0, 0, 0), (0, 1, 0, 0)), 0, [], 1) =
    (((0, 0, 0, 0), (0, 1, 0, 0)), 1, [0], 0) := by decide

/-- The singleton source-machine control encoding. -/
abbrev code : Fin 1 ≃ Fin 1 := Equiv.refl _

/-- A source machine with no work tapes. -/
def control : MultiTapeTM 0 Bool (Fin 1) := MultiTapeTM.ofTr 0 fun _ _ _ =>
  { inputTape := .zero, workTapes := fun _ => (none, .zero), output := none, state := none }

/-- Observe the physical bank only after entering the concrete evaluator caller. -/
def observe : InitializedEvaluator.State 0 (Fin 1) → Option (List ℕ) :=
  Sum.elim (fun _ => none)
    (Sum.elim (fun (_, _, bank, _, _) => some bank) (fun _ => none))

/-- The actual selected prime for six-bit values and fan-in one. -/
theorem selected_prime : fieldModulus 1 6 = 17 := by
  rw [fieldModulus_eq_boundedFirstPrime]
  rfl

/-- Actual metadata selection agrees with the small concrete execution below. -/
theorem prepared : Initializer.prepare 0 1 (1, 1, 0, 0) =
    (((1, 1, 0, 0), (3, 2, 8, 17)), 0, [], 1) := by
  simp only [Initializer.prepare, parameters]
  change (((1, 1, 0, 0), (3, 2, 8, fieldModulus 1 6)), 0, [], 1) = _
  rw [selected_prime]

example : observe ((InitializedEvaluator.machine control code).runFrom [true]
    (InitializedEvaluator.start 0 1 (1, 1, 0, 0)) 7) =
      some ([20] ++ List.replicate 3 17) := by
  rw [InitializedEvaluator.start, prepared]
  decide

example : (InitializedEvaluator.machine control code).halted
    ((InitializedEvaluator.machine control code).runFrom [true]
      (InitializedEvaluator.start 0 1 (1, 1, 0, 0)) 7) = true := by
  rw [InitializedEvaluator.start, prepared]
  decide

example : RawController.Output.decode ((6, 3, 17, 2, 0), [20] ++ List.replicate 3 17) =
    [true, true] ++ List.replicate 4 false := by decide

end ComplexityTests.InitializedEvaluator
