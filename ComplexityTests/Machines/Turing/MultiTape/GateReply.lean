/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of concrete implicit gate replies)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateReplyCorrect

/-!
# Implicit gate-reply routing regressions

Invalid and leaf addresses require zero gate updates. Internal source padding instead returns
the initial packed vector, while positive intervals delegate to the actual interpolation loop.
-/

public section

namespace ComplexityTests.GateReply

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay

/-- The singleton control-state encoding. -/
abbrev code : Fin 1 ≃ Fin 1 := Equiv.refl _

/-- A one-step reader with one work tape and the existing packed source layout. -/
def reader : MultiTapeTM 1 Bool (Fin 1) := MultiTapeTM.ofTr 0 fun _ input _ =>
  { inputTape := .pos, workTapes := fun _ => (some input, .neg), output := some true,
    state := none }

/-- Paid seven-coordinate parameters with deliberately padded raw point coordinates. -/
def params : GateVector.Params :=
  (((1, 1, 99, 99, 2, 99, 14), (17, 4, 28), [17, 18, 33], 2 ^ 14), 7)

/-- Observe completed immediate replies without collapsing active interpolation states. -/
def immediate : GateReply.State 1 (Fin 1) → Option (ℕ × List ℕ) :=
  Sum.elim some (fun _ => none)

example : immediate (GateReply.initial reader code ((0, 2, [4]), params)) =
    some (0, []) := by decide

example : immediate (GateReply.initial reader code ((0, 1, [0]), params)) =
    some (0, []) := by decide

example : ImplicitPath.walk 1 (0, 2, [1]) = 0 := by decide

example : immediate (GateReply.initial reader code ((0, 2, [1]), params)) =
    some (0, [3, 0, 0, 0, 0, 0, 0]) := by decide

example : immediate (GateReply.initial reader code ((0, 2, []), params)) =
    none := by decide

example : GateReply.prepare 1 ((0, 2, []), params) =
    (((1, 1, 0, 1, 2, 0, 14), (17, 4, 28), [0, 1, 16], 2 ^ 14), 7) := rfl

example : (GateReply.machine reader code).halted
    (GateReply.initial reader code ((0, 2, [1]), params)) = true := by decide

end ComplexityTests.GateReply
