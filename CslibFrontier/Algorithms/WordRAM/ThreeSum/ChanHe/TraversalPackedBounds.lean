/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalFrames
public import CslibFrontier.Algorithms.ThreeSum.ChanHe.FromNumbers

/-!
# Direct value bounds for a reached Chan–He traversal node

A node's packed values are bounded directly by its three current input sets. This does not
require completion of a standalone catalogue-producing execution, so it remains applicable when
native solver calls are interleaved with traversal.

## Main results

* `Entry.Valid.abs_oneArray_le`: the existing finite packing bound for any admitted pending entry.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

/-- Every packed value has the finite construction's bound at the current admitted entry. -/
theorem Entry.Valid.abs_oneArray_le {e : Entry} {n U : ℕ} (h : e.Valid n U)
    (Q : Finset ℕ) (Λ i : ℕ) :
    |(e.task.node Q Λ).oneArray U i| ≤ 60 * (U : ℤ) + 40 :=
  Cslib.Algorithms.ThreeSum.ChanHe.Node.abs_oneArray_le h.2.bdd₁ h.2.bdd₂ h.2.bdd₃ i

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
