/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.MPC.Broadcast
import Mathlib.Data.ZMod.Basic

/-!
# Concrete Client Tests for Synchronous All-to-All Broadcast Combinator

Direct client tests of `CslibFrontier.Crypto.Protocols.MPC.Broadcast` (without importing
`CslibFrontier.Crypto.Protocols.MPC.Beaver`) over `ZMod 7`:

1. Concrete evaluation of `broadcastPairs 3` and `outputAt_broadcastSteps` on a 3-party weighted
   aggregation protocol.
2. Concrete evaluation of `evalWith_broadcastSteps` in `MultiOracleWorld.empty`.
-/

namespace ComplexityTests.Crypto.Broadcast

open Cslib Cslib.Probability Cslib.Crypto.Protocols.MPC

/-- Concrete 3-party pair list has length `3 * 3 = 9`. -/
example : (broadcastPairs 3).length = 9 := by
  decide

/-- Concrete 3-party state vector over `ZMod 7`. -/
def sampleState : Fin 3 → ZMod 7 :=
  ![2, 5, 4]

/-- Concrete broadcast step combinator in `noOracleSpec` where each party `s` broadcasts
`2 * st s` and each party `i` outputs `st i + ∑ s, msgs s`. -/
def weightedSumSteps :
    Steps (fun _ : Fin 3 => ZMod 7) (fun _ : Fin 3 => ZMod 7)
      (broadcastSchedule 3 noOracleSpec (ZMod 7)) :=
  broadcastSteps 3 (fun _ x => 2 * x) (fun _ x msgs => x + ∑ s : Fin 3, msgs s)

/-- Evaluating `weightedSumSteps` in `noOracleWorld` deterministically delivers
`fun s => 2 * sampleState s`. -/
example :
    weightedSumSteps.evalWith noOracleWorld sampleState =
      PMF.pure (deliverBroadcast (fun s => 2 * sampleState s)) :=
  evalWith_broadcastSteps 3 (fun _ x => 2 * x) (fun _ x msgs => x + ∑ s : Fin 3, msgs s)
    noOracleWorld sampleState

/-- Party `0`'s output after `deliverBroadcast (fun s => 2 * sampleState s)` equals
`2 + (4 + 3 + 1) = 3` in `ZMod 7`. -/
example :
    weightedSumSteps.outputAt 0 (sampleState 0)
      (deliverBroadcast (spec := noOracleSpec) (fun s => 2 * sampleState s) 0) =
      (3 : ZMod 7) := by
  unfold weightedSumSteps
  rw [outputAt_broadcastSteps]
  decide

end ComplexityTests.Crypto.Broadcast
