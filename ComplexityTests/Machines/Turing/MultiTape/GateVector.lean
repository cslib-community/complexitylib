/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native complete gate vectors)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateVectorCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.NormalizePoint

/-!
# Complete gate-vector regressions

Zero-assignment calls return immediately, but each coordinate still requires a call and return.
The caller retains only the reduced output prefix, and padded raw-register points normalize to
the unsigned field coordinates used by interpolation.
-/

public section

namespace ComplexityTests.GateVector

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay
open Cslib.TreeEval.Ary.Packed

/-- The singleton control-state encoding. -/
abbrev code : Fin 1 ≃ Fin 1 := Equiv.refl _

/-- A deterministic machine that halts after one transition. -/
def haltedControl : MultiTapeTM 0 Bool (Fin 1) := MultiTapeTM.ofTr 0 fun _ _ _ =>
  { inputTape := .zero, workTapes := fun _ => (none, .zero), output := none, state := none }

/-- Three requested coordinates with an empty interpolation assignment range. -/
def params : GateVector.Params :=
  (((1, 1, 2, 0, 1, 0, 13), (17, 2, 13), List.replicate 13 0, 0), 3)

/-- Observe completed prefixes while distinguishing an active interpolation call. -/
def observe : GateVector.State 0 (Fin 1) → Option (ℕ × List ℕ) :=
  Sum.elim (fun (_, cursor, values) => some (cursor, values)) (fun _ => none)

example : (GateVector.machine haltedControl code).halted
    (GateVector.initial (params.1, 0)) = true := by decide

example : (GateVector.machine haltedControl code).halted
    (GateVector.initial params) = false := by decide

example : observe ((GateVector.machine haltedControl code).runFrom [true]
    (GateVector.initial params) 2) = some (1, [0]) := by decide

example : observe ((GateVector.machine haltedControl code).runFrom [true]
    (GateVector.initial params) 6) = some (3, [0, 0, 0]) := by decide

example : (GateVector.machine haltedControl code).halted
    ((GateVector.machine haltedControl code).runFrom [true]
      (GateVector.initial params) 6) = true := by decide

example : GateVector.resume (params, 1, [4])
    (.inl (params.1, 0, 35) : Interpolation.State 0 (Fin 1)) =
      (params, 2, [4, 1]) := rfl

example : NormalizePoint.normalize 17 [17, 18, 33] = [0, 1, 16] := by decide

example : NormalizePoint.normalize 17 [34, 0, 52, 100] = [0, 0, 1, 15] := by decide

end ComplexityTests.GateVector
