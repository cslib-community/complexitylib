/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString

/-!
# Direct conversion of framed Boolean lists to raw words

The canonical `ComputableInPolyTime.listToBits` certificate keeps its original public contract
and registration. Its proof reuses the linear streaming conversion certificate, without a fold
over a growing word. The higher bit-string facade reexports this same declaration.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Convert framed Boolean lists to raw words without changing their contents. -/
@[fun_prop]
theorem listToBits :
    ComputableInPolyTime (fun l => l) (encList encBool) encBits :=
  ComputableInDegree.listToBits.computableInPolyTime


end Turing.MultiTapeTM.ComputableInPolyTime
