/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate

/-!
# Valid indices for native cyclic argument successors

The native next-index program stays inside the actual occurrence list, and its selected
constraint/scope pair occurs in that list. Existing positional occurrence and rotation
successor identities supply both facts, including wraparound and repeated variables.
These original program bounds do not require a supplied rotation or numerical genus.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} {F : CSP Rel V}

/-- The actual next argument has an occurrence-list index bounded by that list's length. -/
theorem argumentNextIndex_lt_occurrences (o : F.Occurrence) :
    argumentNextIndex F o.1 o.2 < F.occurrences.length := by
  classical
  rw [argumentNextIndex_occurrence]
  simpa only [incidenceGraph_edges, List.length_map] using
    incidenceEdgeIndex_lt (argumentSuccessor o)

/-- The cyclic next-position pair really occurs, including the last-to-first wrap. -/
theorem argumentNextPosition_mem (o : F.Occurrence) :
    (o.1.val, if o.2.val + 1 < scopeLength F o.1 then o.2.val + 1 else 0) ∈
      argumentPositions F := by
  classical
  apply List.idxOf_lt_length_iff.mp
  change argumentNextIndex F o.1 o.2 < (argumentPositions F).length
  simpa only [argumentPositions, List.length_map] using argumentNextIndex_lt_occurrences o

end Cslib.Complexity.CSP
