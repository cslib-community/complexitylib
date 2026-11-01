/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of implicit paths and source chunks)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitPathLookup
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialChunkCorrect
public import ComplexityTests.Machines.Turing.MultiTape.QueryReplayGate

/-!
# Native implicit path and source regressions

Paths exercise previous/provider edges, missing providers and invalid addresses. Source chunks
read a fixed initial-control prefix even for huge requested widths, without building blank tape
windows or a tree.
-/

public section

namespace ComplexityTests.ImplicitBlockPath

open Turing MultiTapePTM.BlockComputation
open NativeBlockCodec

-- The nonstationary two-head schedule has rows (2,0), (0,2), (1,1).
def schedule : ℕ := 380

example : ImplicitPath.child 1 (schedule, 3, 3, 0) = 2 := by decide
example : ImplicitPath.child 1 (schedule, 3, 3, 3) = 1 := by decide
example : ImplicitPath.child 1 (0, 3, 3, 1) = 0 := by decide
example : ImplicitPath.child 1 (schedule, 3, 4, 0) = 0 := by decide
example : ImplicitPath.child 1 (schedule, 3, 3, 4) = 0 := by decide
example : ImplicitPath.walk 1 (schedule, 3, [3, 0]) = 0 := by decide
example : ImplicitPath.walk 1 (schedule, 3, [0, 3]) = 1 := by decide
example : ImplicitPath.walk 0 (0, 4, [0, 0, 0, 0]) = 0 := by decide
example : ImplicitPath.walk 1 (schedule, 3, []) = 3 := rfl

example : ImplicitPath.lookupIndex 1 (schedule, 3, [3, 0]) = some 0 := by decide
example : ImplicitPath.lookupIndex 1 (schedule, 3, [0, 3]) = some 1 := by decide
example : ImplicitPath.lookupIndex 1 (schedule, 3, [4]) = none := by decide
example : ImplicitPath.lookupIndex 1 (schedule, 3, [0, 0, 0, 0]) = none := by decide
example : ImplicitPath.lookupIndex 0 (0, 0, []) = some 0 := rfl
example : ImplicitPath.lookupIndex 0 (0, 0, [0]) = none := by decide

example : (InitialChunk.headerWord QueryReplayGate.reader code).length = 3 := by decide
example : InitialChunk.chunk QueryReplayGate.reader code (2, 0) = 3 := by decide
example : InitialChunk.chunk QueryReplayGate.reader code (1, 1) = 1 := by decide
example : InitialChunk.chunk QueryReplayGate.reader code (2, 6) = 0 := by decide
example : InitialChunk.chunk QueryReplayGate.reader code (1000000000, 0) = 3 := by decide
example : InitialChunk.chunk QueryReplayGate.reader code (1000000000, 1) = 0 := by decide

end ComplexityTests.ImplicitBlockPath
