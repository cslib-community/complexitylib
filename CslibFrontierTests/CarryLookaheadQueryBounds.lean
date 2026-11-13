/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Bounds

/-! Reachable query metadata stays short even along unused constant-gate edges. -/

namespace CslibFrontierTests.CarryLookaheadQueryBounds

open Cslib Cslib.Circuits.Boolean.CarryLookahead.Query

example (w rounds : ℕ) (i : Fin w) (u : BitString (w + w + 1)) (path : List Bool) :
    (encAddress (path.foldl (decoder w rounds u).child (.sum i.val))).length ≤
      2 * rounds + w.size + 11 :=
  ((show WellFormed w rounds (.sum i.val) from i.isLt).foldl u path).length_encAddress

/-- A propagate sentinel is constant true, but following its unused child is still bounded. -/
example (w rounds : ℕ) (u : BitString (w + w + 1)) (b : Bool) :
    WellFormed w rounds ((decoder w rounds u).child (.propagate 0 (w + 1)) b) :=
  (show WellFormed w rounds (.propagate 0 (w + 1)) from ⟨Nat.zero_le _, le_rfl⟩).child u b

end CslibFrontierTests.CarryLookaheadQueryBounds
