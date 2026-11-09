/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.PerfectMatching
public import Complexity.Computability.PolyTime.CSP.ToCNF
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.PolyTime.CSP.Vars

/-!
# Polynomial-time edge lists and perfect-matching instances

The edge list of a graph (`Cslib.Complexity.Graph.edgeList`) and its perfect-matching instance
(`Cslib.Complexity.Graph.perfectMatchingInstance`) are computable in polynomial time from the
encoded graph `Cslib.Complexity.encGraph`. The instance's variables are written in binary.

## Main results

* `Cslib.Complexity.Graph.computableInPolyTime_edgeList`: the edge list.
* `Cslib.Complexity.Graph.computableInPolyTime_perfectMatchingInstance`: the perfect-matching
  instance.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Listing the edges of `G.induced` is polynomial-time. -/
theorem computableInPolyTime_edgeList :
    ComputableInPolyTime edgeList encGraph (encList (encPair encNat encNat)) := by
  unfold edgeList encGraph
  fun_prop

/-- Building the perfect-matching instance of a graph is polynomial-time. -/
theorem computableInPolyTime_perfectMatchingInstance :
    ComputableInPolyTime perfectMatchingInstance encGraph (encCSP encUnit encNat) := by
  have hE := computableInPolyTime_edgeList
  refine (Complexity.CSP.computableInPolyTime_unary_to_binary encUnit).comp
    (?_ : ComputableInPolyTime (fun G : Graph => G.perfectMatchingInstance) _ _)
  unfold perfectMatchingInstance incident
  fun_prop

end Cslib.Complexity.Graph
