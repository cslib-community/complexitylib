/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Defs
import Mathlib.Data.Fin.VecNotation

/-!
# Generic RAM with Boolean values and addresses

A nonnumeric instance exercises indirect memory and counted execution without a word width.
A failed primitive test must fault rather than taking its false branch.
-/

namespace ComplexityTests.GenericRAM

open Cslib.GenericRAM

private abbrev model : Model where
  Value := Bool
  Address := Bool
  Config := Unit
  Const := Bool
  operations := { Op := Unit, Arity := fun _ => 1 }
  tests := { Op := Unit, Arity := fun _ => 0 }
  constant _ v := some v
  evalOp _ _ args := some (!(args 0))
  evalTest _ _ _ := none
  admissible _ _ := true
  address _ v := some v
  validMove _ _ := true
  validPC _ _ := true

private def initial : State model 2 :=
  ⟨0, Data.init false (fun _ => true)⟩

private def program : Program model 2 :=
  [.op (.const 0 true), .op (.const 1 false), .op (.store 0 1),
    .op (.alu () 1 ![1]), .op (.load 1 0), .halt 1]

example :
    run () program 6 initial = some (false, 6) ∧
    Executes () program initial false 6 ∧
    step () [.branch (.test () ![]) 2, .halt 0, .halt 1] initial = .fault :=
  ⟨by decide,
   Executes.of_run (by decide : run () program 6 initial = some (false, 6)),
   rfl⟩

end ComplexityTests.GenericRAM
