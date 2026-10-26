/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle


import Diag1155.Measure
/-! Adaptive requests, ignored local bits, clock truncation, and polynomial-time replay. -/

@[expose] public section

namespace ComplexityTests.OracleReplay

open Cslib Turing MultiTapeMachine MultiTapeTM

inductive Phase where
  | start | ask | copy | askAgain | finish
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.start, .ask, .copy, .askAgain, .finish}, by intro phase; cases phase <;> simp⟩

private def action (output : Option Bool) (next : Option Phase) : Turing.Action 0 Bool Phase where
  inputTape := 0
  workTapes := Fin.elim0
  output := output
  state := next

-- The second request copies the first reply. The machine ignores its private coin.
private def machine : MultiTapePTM 0 Bool Phase Unit where
  initial := .start
  tr state _ _ answer _ := match state with
    | .start => .step (action none (some .ask)) (fun _ => some true) (fun _ => 0)
    | .ask => .query () .copy
    | .copy => .step (action none (some .askAgain)) (fun _ => answer ()) (fun _ => 0)
    | .askAgain => .query () .finish
    | .finish => .step (action (answer ()) none) (fun _ => none) (fun _ => 0)

-- Transcript bits at the first and third instructions are ignored. The first query is [true].
example : machine.pendingRequest (machine.replayPrefix [] [true] 1) = [true] := by decide

-- Changing the first oracle reply changes the later request.
example : machine.pendingRequest (machine.replayPrefix [] [false, false, true] 3) = [false] := by
  decide

example : machine.pendingRequest (machine.replayPrefix [] [true, true, false] 3) = [true] := by
  decide

-- Only the fourth bit supplies the final answer; local and halted bits have no effect.
example : machine.replayOutput [] [true, false, true, true, true, true] = [true] := by decide

example : machine.replayOutput [] [false, true, false, false, false, true] = [false] := by decide

example : machine.oracleReplies (fun w => !w.headD false) 7 [] =
    [false, false, false, true, false, false, false] := by decide

example (input : List Bool) (fuel : ℕ) :
    machine.replayConfig input (machine.oracleReplies (fun w => !w.headD false) fuel input) =
      (machine.answerStep (fun q => [!q.2.headD false]))^[fuel]
        (FiniteConfig.init machine.initial input) :=
  machine.replayConfig_oracleReplies _ _ _

example : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => machine.replayOutput p.1 p.2)
    (encPair encBits encBits) encBits := by fun_prop

example : ComputableTidilyInPolyTime
    (fun p : (List Bool × List Bool) × ℕ =>
      machine.pendingRequest (machine.replayPrefix p.1.1 p.1.2 p.2))
    (encPair (encPair encBits encBits) encUnary) encBits := by fun_prop

end ComplexityTests.OracleReplay
