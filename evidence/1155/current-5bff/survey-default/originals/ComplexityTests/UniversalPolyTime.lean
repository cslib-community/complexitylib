/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# Universal input-coding clients

Description decoding and bit coding are available without importing hierarchy or Ladner modules.
The automatic rules also compose description decoding and input-symbol conversion.
-/

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

namespace ComplexityTests.UniversalPolyTime

example : ComputableTidilyInPolyTime
    (fun x : List Bool => (decodeDesc x, x.map eBit)) encBits
    (encPair eDesc (encList encUnary)) := by
  fun_prop

example : ComputableTidilyInDegree (fun x : List Bool => x.map eBit)
    encBits (encList encUnary) 1 1 :=
  computableTidilyInDegree_map_eBit

example : ComputableTidilyInPolyTime (fun b : Bool => eBit b) encBool encUnary := by
  fun_prop

-- Empty input and both bit values retain the exact framed unary symbol coding.
example : symbolsT.run false (encTrueDoubled []) = [] := rfl

example : symbolsT.run false (encTrueDoubled [true, false, true]) =
    [true, true, false, false, true, true, false] := rfl

end ComplexityTests.UniversalPolyTime
