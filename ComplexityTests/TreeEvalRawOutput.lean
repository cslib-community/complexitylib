/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of native packed-register output)

public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerOutput

/-!
# Native packed output regressions

Two-bit chunks decode a final partial chunk, and target selection reads a later register.
Malformed output capacity, unpaid cells and binary-large chunk widths are rejected before the
output loop. The native certificate includes the actual output's storage.
-/

@[expose] public section

namespace ComplexityTests.TreeEvalRawOutput

open Turing MultiTapeTM Cslib.TreeEval.Ary.Packed.RawController.Output

example : decode ((3, 2, 5, 2, 0), [8, 6]) = [true, true, true] := by decide
example : decode ((3, 2, 5, 2, 1), [5, 5, 8, 6]) = [true, true, true] := by decide
example : decode ((3, 2, 5, 2, 0), [5, 5]) = [false, false, false] := by decide
example : decode ((0, 1000000000, 5, 0, 0), []) = [] := by decide
example : decode ((3, 2, 5, 1, 0), [8]) = [] := by decide
example : decode ((3, 2, 5, 2, 0), [0, 0]) = [] := by decide
example : decode ((3, 0, 5, 2, 0), [8, 6]) = [] := by decide

/-- The tested decoder is realized with its actual framed output representation. -/
example : ComputableInSpace decode encArgs (encList encBool)
    (fun q => (encArgs q).length) := decode_inSpace

end ComplexityTests.TreeEvalRawOutput
