/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words

/-! # Consequences of the counter-program word operations

Logspace composition and the polynomial-time bridge applied to the new operations.
-/

@[expose] public section

namespace Turing.MultiTapeTM.Tests.LogSpaceCounterWords

/-- Enumerating `0, …, n - 1` and reading the result back as unary list cells: by composition,
the encoding of the list `0, …, n - 1` is computed in logarithmic space from `n` in unary. -/
example : ComputableInLogSpace (fun n => List.range n) encUnary (encList encUnary) :=
  ComputableInLogSpace.range.comp ComputableInLogSpace.id

/-- Lookup in a list of bit strings is computable in polynomial time, by the logspace bridge. -/
example : ComputableTidilyInPolyTime (fun p : List (List Bool) × ℕ => p.1[p.2]?)
    (encPair (encList encBits) encUnary) (encOption encBits) :=
  (ComputableInLogSpace.getElem? encBits).computableTidilyInPolyTime

end Turing.MultiTapeTM.Tests.LogSpaceCounterWords
