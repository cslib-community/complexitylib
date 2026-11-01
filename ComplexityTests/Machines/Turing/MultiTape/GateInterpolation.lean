/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native same-input gate interpolation)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateInterpolationBounds

/-!
# Native interpolation caller regressions

Actual parameters override the fixed halted template. The first two assignments exercise an
immediately rejected label and a live one-step replay with halted control. The caller retains
one modular accumulator rather than a table of assignments.
-/

public section

namespace ComplexityTests.GateInterpolation

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay
open Cslib.TreeEval.Ary.Packed

abbrev code : Fin 1 ≃ Fin 1 := Equiv.refl _

def haltedControl : MultiTapeTM 0 Bool (Fin 1) := MultiTapeTM.ofTr 0 fun _ _ _ =>
  { inputTape := .zero, workTapes := fun _ => (none, .zero), output := none, state := none }

def params : QueryGate.Params Interpolation.Context :=
  ((1, 1, 2, 0, 1, 0, 13), (17, 2, 13), List.replicate 13 0, 8192)

def observe : Interpolation.State 0 (Fin 1) → Option (ℕ × ℕ) :=
  Sum.elim (fun q => some q.2) (fun _ => none)

example : (Interpolation.machine haltedControl code).halted
    (Interpolation.machine haltedControl code).init = true := by decide
example : (Interpolation.machine haltedControl code).halted
    (Interpolation.initial params) = false := by decide
example : observe ((Interpolation.machine haltedControl code).runFrom [true]
    (Interpolation.initial params) 2) = some (1, 0) := by decide
example : observe ((Interpolation.machine haltedControl code).runFrom [true]
    (Interpolation.initial params) 5) = some (2, 0) := by decide
example : (Interpolation.start (k := 0) code (params, 1, 0)).1 = (1, 0) := rfl

end ComplexityTests.GateInterpolation
