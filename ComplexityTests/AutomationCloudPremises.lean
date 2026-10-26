/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.PCP.Encoded.Cloud
import Complexity.Tactic.PolyTime

/-! Missing-premise companions to the original generic Cloud source positives.
The library already checks `unfold halfEdges List.product; polytime` and
`unfold endpoint; polytime`; those positives are not duplicated here.
These controls unfold the operations too, preventing a named endpoint certificate shortcut.
-/

open Cslib Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

set_option maxHeartbeats 200000 in
-- Pin the original default budget and preserve the original `polytime` search configuration.
example {C Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}
    {graph : Input → Graph C}
    (_hgraph : ComputableInPolyTime graph input (Graph.encoding enc)) : True := by
  fail_if_success
    clear _hgraph
    have : ComputableInPolyTime (fun x => (graph x).halfEdges)
        input (encList (encPair encUnary encBool)) := by
      unfold Graph.halfEdges List.product
      polytime
  trivial

set_option maxHeartbeats 200000 in
-- Pin the original default budget and preserve the original `polytime` search configuration.
example {C Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}
    {graph : Input → Graph C} {halfEdge : Input → ℕ × Bool}
    (_hgraph : ComputableInPolyTime graph input (Graph.encoding enc))
    (_hhalfEdge : ComputableInPolyTime halfEdge input (encPair encUnary encBool))
    (_fallback : C) : True := by
  fail_if_success
    clear _hgraph
    have : ComputableInPolyTime (fun x => (graph x).endpoint _fallback (halfEdge x))
        input encUnary := by
      unfold Graph.endpoint
      polytime
  trivial

set_option maxHeartbeats 200000 in
-- Pin the original default budget and preserve the original `polytime` search configuration.
example {C Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}
    {graph : Input → Graph C} {halfEdge : Input → ℕ × Bool}
    (_hgraph : ComputableInPolyTime graph input (Graph.encoding enc))
    (_hhalfEdge : ComputableInPolyTime halfEdge input (encPair encUnary encBool))
    (_fallback : C) : True := by
  fail_if_success
    clear _hhalfEdge
    have : ComputableInPolyTime (fun x => (graph x).endpoint _fallback (halfEdge x))
        input encUnary := by
      unfold Graph.endpoint
      polytime
  trivial
