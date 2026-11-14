/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.LongPath.Hardness

/-!
# Tests: k-Path is `NP`-complete

The verifier for k-Path on the edge `1 — 2`, by `decide`. The certificate `[false, false, true,
false]` names the ordering `[1, 2]`: block `0` has no set bit and names position `0`, block `1` has
one set bit and names position `1`. The verifier accepts it for `k = 1` and `k = 2`, rejects it for
`k = 3`, which exceeds the number of vertices, and rejects it when the edge is missing. The
all-`false` certificate names `[1, 1]`, which is not an ordering, and is rejected. `NP`-hardness
and `NP`-completeness are instantiated.
-/

namespace CslibFrontierTests.LongPathHardness

section Opened

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- The edge `1 — 2`. -/
def edge : Graph := ⟨[1, 2], [(1, 2)]⟩

/-- The vertices `1` and `2` without edges. -/
def noEdge : Graph := ⟨[1, 2], []⟩

/-- The certificate naming the ordering `[1, 2]` of the vertices of `edge` and `noEdge`. -/
def cert : List Bool := [false, false, true, false]

/-- The ordering `[1, 2]` gives a path on two vertices of the edge `1 — 2`. -/
example : LongPath.verifier (⟨edge, 2⟩, cert) = true := by decide

/-- The ordering `[1, 2]` gives a path on one vertex. -/
example : LongPath.verifier (⟨edge, 1⟩, cert) = true := by decide

/-- No path has three vertices in a graph with two. -/
example : LongPath.verifier (⟨edge, 3⟩, cert) = false := by decide

/-- Without the edge, `[1, 2]` is not a path. -/
example : LongPath.verifier (⟨noEdge, 2⟩, cert) = false := by decide

/-- The all-`false` certificate names `[1, 1]`, which is not an ordering of the vertices. -/
example : LongPath.verifier (⟨edge, 1⟩, [false, false, false, false]) = false := by decide

/-- `LongPathInstance` extensionality identifies instances with equal fields. -/
example {x y : LongPathInstance} (hG : x.graph = y.graph) (hk : x.target = y.target) :
    x = y :=
  LongPathInstance.ext hG hk

example : (default : LongPathInstance) = ⟨default, default⟩ := rfl

/-- `encLongPath` exposes polynomial-time projections and constructor to `fun_prop`. -/
example : ComputableInPolyTime LongPathInstance.graph encLongPath encGraph := by fun_prop

example : ComputableInPolyTime LongPathInstance.target encLongPath encNat := by fun_prop

example :
    ComputableInPolyTime
      (fun x : LongPathInstance => (⟨x.graph, x.target⟩ : LongPathInstance))
      encLongPath encLongPath := by
  fun_prop

/-- k-Path is `NP`-hard. -/
example : NPHard encLongPath LongPath := LongPath_npHard

/-- k-Path is `NP`-complete. -/
example : NPComplete encLongPath LongPath := LongPath_npComplete

end Opened

section Unopened

open Turing.MultiTapeTM

example :
    ComputableInPolyTime
      (fun x : Cslib.Complexity.LongPathInstance =>
        Cslib.Complexity.LongPathInstance.mk x.graph x.target)
      Cslib.Complexity.encLongPath Cslib.Complexity.encLongPath := by
  fun_prop

end Unopened

end CslibFrontierTests.LongPathHardness
