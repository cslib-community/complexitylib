/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Initial

/-!
The initializer derives its unary logarithm from the binary width, including the empty width
and the transition across a power of two. The raw claimed bit determines the actual game header.
-/

namespace CslibFrontierTests.CarryLookaheadInitial

open Cslib.Circuits.Boolean.CarryLookahead.Query

example : Initial.position ⟨0, 0, false⟩ = ⟨0, 0, ⟨11, 0, 0⟩, false⟩ := by decide

example : Initial.position ⟨1, 0, true⟩ = ⟨1, 1, ⟨11, 0, 0⟩, true⟩ := by decide

example : Initial.position ⟨63, 62, true⟩ = ⟨63, 6, ⟨11, 0, 62⟩, true⟩ := by decide

example : Initial.position ⟨64, 63, false⟩ = ⟨64, 7, ⟨11, 0, 63⟩, false⟩ := by decide

example (width bit : ℕ) (claim : Bool) :
    Turing.wordGameHeader (Routing.player (Initial.position ⟨width, bit, claim⟩)) =
      [claim, false] := Initial.header_position _

end CslibFrontierTests.CarryLookaheadInitial
