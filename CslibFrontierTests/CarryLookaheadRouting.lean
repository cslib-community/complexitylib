/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Routing

/-! Native metadata transitions preserve semantic ownership, claims, and resource bounds. -/

namespace CslibFrontierTests.CarryLookaheadRouting

open Cslib Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarryLookahead.Query
open Routing Turing.MultiTapeTM

example : ComputableInPolyTime Routing.step (encPair encBool encPosition)
    (encPair (encOption encBool) encPosition) := step_polyTime

/-- A true AND claim gives both branches the correct semantic obligation. -/
example (w rounds i : ℕ) (u : BitString (w + w + 1)) :
    value w rounds u (.sum i) = true ↔
      ∀ b, value w rounds u (next (ofClaim w rounds ⟨.sum i, true⟩) b).address.address =
        (next (ofClaim w rounds ⟨.sum i, true⟩) b).claim := by
  simpa using value_iff_next w rounds u ⟨.sum i, true⟩ (p := true) rfl

/-- A NOT gate ignores the branch bit and flips the asserted value. -/
example (w rounds i : ℕ) (claim b : Bool) :
    next (ofClaim w rounds ⟨.sumNot i, claim⟩) b =
      ofClaim w rounds ⟨.sumAnd i, !claim⟩ := by
  simpa [LocalValueGame.next, decoder] using
    next_ofClaim w rounds (fun _ => false) ⟨.sumNot i, claim⟩ b

example (w rounds : ℕ) (i : Fin w) (claim : Bool) :
    (encPosition (ofClaim w rounds ⟨.sum i.val, claim⟩)).length ≤
      4 * w.size + 6 * rounds + 26 :=
  length_ofClaim_le _ i.isLt

end CslibFrontierTests.CarryLookaheadRouting
