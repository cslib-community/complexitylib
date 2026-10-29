/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.CarrySave.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! Native construction of actual carry-save codes, including empty words, bit order,
overflow and a composition with two independently generated three-to-two reducers. -/

namespace ComplexityTests.CarrySaveNative

open Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableInPolyTime

example : csa3to2Code 0 = ([], []) := by decide
example : csa4to2Code 0 = ([], []) := by decide

-- Three one-bit ones produce a sum bit of one; the carry leaves the one-bit word.
example : (csa3to2Code 1).2.map (evalOutput [true, true, true] (csa3to2Code 1).1) =
    [true, false] := by decide

-- 3+2+1 modulo 4 is represented as the pair (0,2), with the sum word first.
example : (csa3to2Code 2).2.map
    (evalOutput [true, true, false, true, true, false] (csa3to2Code 2).1) =
      [false, false, false, true] := by decide

-- Four two-bit words 1,2,3,1 produce the pair (3,0), whose sum is 7 modulo 4.
example : (csa4to2Code 2).2.map
    (evalOutput [true, false, false, true, true, true, true, false] (csa4to2Code 2).1) =
      [true, true, false, false] := by decide

-- The constant lowest carry saves four gates compared with a padded majority block.
example : (csa3to2Code 3).1.length = 56 ∧ (csa3to2Code 3).2.length = 6 := by decide

private def twice3to2 (w : ℕ) : Circuit signature (w + (w + w)) ((w + w) + (w + w)) :=
  (csa3to2 w).append (csa3to2 w)

/-- A client generates both reducers and feeds their shared-input outputs to a four-to-two
reducer. The full resulting code, not just a size bound, is uniformly native polynomial-time. -/
theorem composed_generator : ComputableInPolyTime
    (fun w => ((csa4to2 w).comp (twice3to2 w)).code) encUnary encCode := by
  have hw := unary_to_binary
  have hn : ComputableInPolyTime (fun w : ℕ => w + (w + w)) encUnary encNat := by fun_prop
  have h := computableInPolyTime_compCode hn computableInPolyTime_csa4to2
    (computableInPolyTime_appendCode hn computableInPolyTime_csa3to2
      computableInPolyTime_csa3to2)
  simpa only [appendCode_code, compCode_code, twice3to2] using h

end ComplexityTests.CarrySaveNative
