/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.PCP.Encoded.AddTrivial
import Mathlib.Logic.Equiv.Fin.Basic
import Complexity.Tactic.PolyTime


import Diag1155.Measure
/-! Replay the original automatic AddTrivial proof, not its explicit production replacement.
Unfold first so the registered certificate for `addTrivial` cannot close the named goal.
The captured companions require both supplied callbacks. -/

diag1155_install
open Turing.MultiTapeTM Cslib.PCP.Encoded

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example {C : Type} (enc : C ↪ List Bool) (truth : C) :
    ComputableInPolyTime (fun p : Graph C × List (ℕ × ℕ) =>
      p.1.addTrivial truth p.2)
      (encPair (Graph.encoding enc) (encList (encPair encUnary encUnary)))
      (Graph.encoding enc) := by
  unfold Graph.addTrivial
  polytime

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example {C Input : Type} (enc : C ↪ List Bool) (input : Input ↪ List Bool) (truth : C)
    {graph : Input → Graph C} {extra : Input → List (ℕ × ℕ)}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding enc))
    (hextra : ComputableInPolyTime extra input (encList (encPair encUnary encUnary))) :
    ComputableInPolyTime (fun a => (graph a).addTrivial truth (extra a))
      input (Graph.encoding enc) := by
  unfold Graph.addTrivial
  polytime

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example {C Input : Type} (enc : C ↪ List Bool) (input : Input ↪ List Bool) (_truth : C)
    {graph : Input → Graph C} {extra : Input → List (ℕ × ℕ)}
    (_hgraph : ComputableInPolyTime graph input (Graph.encoding enc))
    (_hextra : ComputableInPolyTime extra input (encList (encPair encUnary encUnary))) : True := by
  fail_if_success
    clear _hgraph
    have : ComputableInPolyTime (fun a => (graph a).addTrivial _truth (extra a))
        input (Graph.encoding enc) := by
      unfold Graph.addTrivial
      polytime
  fail_if_success
    clear _hextra
    have : ComputableInPolyTime (fun a => (graph a).addTrivial _truth (extra a))
        input (Graph.encoding enc) := by
      unfold Graph.addTrivial
      polytime
  trivial
