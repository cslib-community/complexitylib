/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words

/-! # Consequences of the counter-program word operations

The logspace-to-polynomial-time bridge applied to the new list lookup.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Tests.LogSpaceCounterWords

/-- Lookup in a list of bit strings is computable in polynomial time, by the (tidy)
logspace-to-polynomial-time bridge. -/
example : ComputableTidilyInPolyTime (fun p : List (List Bool) × ℕ => p.1[p.2]?)
    (encPair (encList encBits) encUnary) (encOption encBits) :=
  (ComputableInLogSpace.getElem? encBits).computableTidilyInPolyTime

end Turing.MultiTapeTM.Tests.LogSpaceCounterWords
