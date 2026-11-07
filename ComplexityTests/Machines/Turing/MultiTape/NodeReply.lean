/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of paid implicit node replies)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.NodeReplyCorrect
public import ComplexityTests.Machines.Turing.MultiTape.QueryReplayGate

/-!
# Paid node-reply regressions

Leaves return the complete packed initial value; gates return only their tag. Invalid paths
and insufficient capacity are rejected. Large requested vector lengths cannot allocate their
numeric magnitude from short binary metadata.
-/

public section

namespace ComplexityTests.NodeReply

open Turing MultiTapePTM.BlockComputation
open NativeBlockCodec

def leafArgs : NodeReply.Args := ((0, 0, []), (2 ^ 14, 2, 7))

example : InitialVector.values QueryReplayGate.reader code (2 ^ 14, 2, 7) =
    [3, 0, 0, 0, 0, 0, 0] := by decide
example : InitialVector.values QueryReplayGate.reader code (1, 2, 1000000000) = [3] := by decide
example : InitialVector.values QueryReplayGate.reader code (0, 2, 1000000000) = [] := by decide
example : NodeReply.reply QueryReplayGate.reader code leafArgs =
    (1, [3, 0, 0, 0, 0, 0, 0]) := by decide
example : NodeReply.reply QueryReplayGate.reader code ((0, 1, []), (0, 2, 7)) =
    (2, []) := by decide
example : NodeReply.reply QueryReplayGate.reader code ((0, 1, [0]), (2 ^ 14, 2, 7)) =
    (1, [3, 0, 0, 0, 0, 0, 0]) := by decide
example : NodeReply.reply QueryReplayGate.reader code ((0, 1, [4]), (2 ^ 14, 2, 7)) =
    (0, []) := by decide
example : NodeReply.reply QueryReplayGate.reader code ((0, 1, [0, 0]), (2 ^ 14, 2, 7)) =
    (0, []) := by decide
example : NodeReply.reply QueryReplayGate.reader code ((0, 0, []), (1, 2, 1000000000)) =
    (0, []) := by decide

end ComplexityTests.NodeReply
