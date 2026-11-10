/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.MPC.Broadcast
import Mathlib.Data.ZMod.Basic

/-!
# Concrete Client Tests for Synchronous All-to-All Broadcast Combinator

Direct client tests of `CslibFrontier.Crypto.Protocols.MPC.Broadcast` and of the all-to-all
layer `CslibFrontier.Crypto.Protocols.MPC.AllToAll` it is built on (without importing
`CslibFrontier.Crypto.Protocols.MPC.Beaver`) over `ZMod 7`:

1. Concrete evaluation of `allPairs 3` and `outputAt_broadcastSteps` on a 3-party weighted
   aggregation protocol.
2. Concrete evaluation of `evalWith_broadcastSteps` in `noOracleWorld`.
3. Concrete evaluation of `evalWith_allToAllStepsWith` and `outputAt_allToAllStepsWith` on a
   receiver-dependent protocol.
-/

namespace CslibFrontierTests.Crypto.Broadcast

open Cslib Cslib.Probability Cslib.Crypto.Protocols.MPC

/-- Concrete 3-party pair list has length `3 * 3 = 9`. -/
example : (allPairs 3).length = 9 := by
  decide

/-- Concrete 3-party state vector over `ZMod 7`. -/
def sampleState : Fin 3 → ZMod 7 :=
  ![2, 5, 4]

/-- Concrete broadcast step combinator in `noOracleSpec` where each party `s` broadcasts
`2 * st s` and each party `i` outputs `st i + ∑ s, msgs s`. -/
def weightedSumSteps :
    Steps (fun _ : Fin 3 => ZMod 7) (fun _ : Fin 3 => ZMod 7)
      (allToAllSchedule 3 (spec := noOracleSpec) (ZMod 7)) :=
  broadcastSteps 3 (fun _ x => 2 * x) (fun _ x msgs => x + ∑ s : Fin 3, msgs s)

/-- Evaluating `weightedSumSteps` in `noOracleWorld` deterministically delivers
`fun s => 2 * sampleState s`. -/
example :
    weightedSumSteps.evalWith noOracleWorld sampleState =
      PMF.pure (fun i =>
        receivedScheduleOfInbox i (fun s => 2 * sampleState s) (allPairs 3)) :=
  evalWith_broadcastSteps 3 (fun _ x => 2 * x) (fun _ x msgs => x + ∑ s : Fin 3, msgs s)
    noOracleWorld sampleState

/-- Party `0`'s output on the broadcast values `fun s => 2 * sampleState s` equals
`2 + (4 + 3 + 1) = 3` in `ZMod 7`. -/
example :
    weightedSumSteps.outputAt 0 (sampleState 0)
      (receivedScheduleOfInbox (spec := noOracleSpec) 0 (fun s => 2 * sampleState s)
        (allPairs 3)) =
      (3 : ZMod 7) := by
  unfold weightedSumSteps
  rw [outputAt_broadcastSteps]
  decide

/-- Concrete pairwise step combinator where sender `s` sends `(rcv.val + 1) * st s` to receiver
`rcv` and each party `i` sums its received inbox. -/
def pairwiseWeightedSteps :
    Steps (fun _ : Fin 3 => ZMod 7) (fun _ : Fin 3 => ZMod 7)
      (allToAllSchedule 3 (spec := noOracleSpec) (ZMod 7)) :=
  allToAllStepsWith 3 (fun _ x rcv => (rcv.val + 1 : ZMod 7) * x)
    (fun _ _ inbox => ∑ s : Fin 3, inbox s)

/-- Evaluating `pairwiseWeightedSteps` in `noOracleWorld` deterministically delivers each party's
receiver-dependent inbox. -/
example :
    pairwiseWeightedSteps.evalWith noOracleWorld sampleState =
      PMF.pure (fun i =>
        receivedScheduleOfInbox i (fun s => (i.val + 1 : ZMod 7) * sampleState s)
          (allPairs 3)) :=
  evalWith_allToAllStepsWith 3 (fun _ x rcv => (rcv.val + 1 : ZMod 7) * x)
    (fun _ _ inbox => ∑ s : Fin 3, inbox s) noOracleWorld sampleState

/-- Party `1`'s output (`rcv.val + 1 = 2`) sums `2 * 2 + 2 * 5 + 2 * 4 = 1 : ZMod 7`. -/
example :
    pairwiseWeightedSteps.outputAt 1 (sampleState 1)
      (receivedScheduleOfInbox (spec := noOracleSpec) 1
        (fun s => ((1 : Fin 3).val + 1 : ZMod 7) * sampleState s) (allPairs 3)) =
      (1 : ZMod 7) := by
  unfold pairwiseWeightedSteps
  rw [outputAt_allToAllStepsWith]
  decide

end CslibFrontierTests.Crypto.Broadcast
