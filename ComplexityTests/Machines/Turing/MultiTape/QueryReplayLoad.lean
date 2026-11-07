/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native replay initialization)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayLoadCorrect
public import ComplexityTests.Machines.Turing.MultiTape.NativeBlockCodec

/-!
# Native loading from local labels

Signed origins exercise interior and blank input positions. Explicit cells are retained even on
malformed raw widths, while checked label loading rejects malformed and noncanonical labels.
-/

@[expose] public section

namespace ComplexityTests.QueryReplayLoad

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay QueryReplay.Load

def raw : RawResult 1 (Fin 1) :=
  (some 0, fun head => head.elim 5 (fun _ => 7), .empty, fun _ => [0, 1, 2, 0, 1, 2])

example : inputPos 3 2 0 0 5 = 2 := rfl
example : inputPos 3 2 0 1 5 = 0 := rfl
example : inputPos 3 2 100 0 5 = 0 := rfl
example : inputPos 3 2 0 100 5 = 0 := rfl
example : inputPos 3 2 1 0 5 = 4 := rfl
example : (load (3, 2, (0, 1), raw)).heads 0 = 3 := rfl
example : (load (3, 1000000000, (0, 1), raw)).cells 0 = [0, 1, 2, 0, 1, 2] := rfl

example : CanonicalWindows 2 raw := by simp [CanonicalWindows, raw]

example : load (3, 2, (0, 1), raw) =
    loadView 3 2 (fun _ => -1) (raw.toView 2) :=
  load_eq_loadView 3 2 0 1 raw (by simp [CanonicalWindows, raw]) (fun _ => -1) rfl

example : Label.load NativeBlockCodec.code (3, 1, (0, 0), NativeBlockCodec.good) =
    some (load (3, 1, (0, 0), NativeBlockCodec.raw)) := by
  have hp : Encoding.NativeChecked.parse (k := 1) NativeBlockCodec.code
      (1, NativeBlockCodec.good) = some NativeBlockCodec.raw := by decide
  simp only [Label.load, hp, Option.map_some]
example : Label.load (k := 1) NativeBlockCodec.code
    (3, 1, (0, 0), NativeBlockCodec.fail) = none := by decide
example : Label.load (k := 1) NativeBlockCodec.code
    (3, 1, (0, 0), NativeBlockCodec.noncanonicalBlank) = none := by decide
example : Label.load (k := 1) NativeBlockCodec.code
    (3, 1000000000, (0, 0), NativeBlockCodec.good) = none := by decide

/-- Actual checked input and supplied metadata pay for the entire initialized replay state. -/
example : ComputableInSpace (Label.load (k := 1) NativeBlockCodec.code)
    Label.encArgs (encOption encConfig) (fun a => (Label.encArgs a).length) :=
  Label.load_inSpace _

end ComplexityTests.QueryReplayLoad
