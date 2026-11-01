/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of packed assignment label acquisition)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAssignmentsCorrect
public import ComplexityTests.Machines.Turing.MultiTape.NativeBlockCodec

/-!
# Packed assignment label regressions

Child slices omit per-child padding, retain leading zero bits and use the same child order as
the block gate. Malformed binary widths cannot allocate their requested numeric magnitude.
The final examples pass extracted words through the existing canonical block parser.
-/

public section

namespace ComplexityTests.AssignmentLabels

open Cslib Cslib.TreeEval.Ary.Packed Turing.MultiTapeTM
open Turing.MultiTapePTM.BlockComputation
open QueryReplay
open Turing.MultiTapeNTM.ChoiceTable
open NativeBlockCodec

example : AssignmentLabels.label (65536, 165, 4, 3, 0) = [true, false, true] := by decide
example : AssignmentLabels.label (65536, 165, 4, 3, 1) = [false, true, false] := by decide
example : AssignmentLabels.label (65536, 0, 4, 3, 3) = [false, false, false] := by decide
example : AssignmentLabels.label (1, 0, 1000000000, 1000000000, 0) = [false] := by decide
example : AssignmentLabels.label (1, 0, 1000000000, 1000000000, 1) = [] := by decide
example : AssignmentLabels.label (65536, 165, 4, 0, 0) = [] := rfl

example : (Assignments.labels 1 (65536, 165, 4, 3)).1 = [true, false, true] := by decide
example : (Assignments.labels 1 (65536, 165, 4, 3)).2 0 0 = [false, true, false] := by decide
example : (Assignments.labels 1 (65536, 165, 4, 3)).2 0 2 = [false, false, false] := by decide

-- Four canonical labels, each with one padding bit, in the actual row-major assignment.
def counter : ℕ := ofBits ((List.replicate 4 (good ++ [false])).flatten)
def words := Assignments.labels 1 (2 ^ 56, counter, 14, 13)

example : words.1 = good := by decide
example : words.2 0 2 = good := by decide
example : Encoding.NativeChecked.parse code (1, words.1) = some raw := by decide
example : (Providers.Labels.combine code
    (1, (fun _ _ => none), words.1, words.2)).isSome = true := by decide

end ComplexityTests.AssignmentLabels
