/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

import Complexity.Algorithms.Reachability.InductiveCounting.Bounds

/-!
# Tests of the binary-choice inductive-counting controller

These tests execute the actual guarded transition on singleton, edgeless and cyclic graphs.
They include reflexive reachability, dishonest omissions, count mismatches, invalid identifiers,
and a guessed nonedge.
-/

namespace ComplexityTests.InductiveCounting

open Cslib.InductiveCounting

-- Kernel-checked evaluation unfolds up to 120 controller instructions, each with ten-register
-- updates and progress checks. The larger elaborator stack is confined to these finite tests.
set_option maxRecDepth 4096

private def noEdge : ℕ → ℕ → Bool := fun _ _ => false
private def noBad : ℕ → Bool := fun _ => false
private def badAt (target : ℕ) : ℕ → Bool := fun u => u == target

/-- Replay a state-dependent test strategy. This helper is not part of the controller. -/
private def drive (N width source : ℕ) (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool)
    (strategy : State → Bool) : ℕ → State → State
  | 0, s => s
  | n + 1, s => drive N width source edge bad strategy n
      (step N width source edge bad s (strategy s))

private def onlySource (source : ℕ) (s : State) : Bool :=
  s.phase == .candidate && s.candidate == source ||
    s.phase == .guess && source == 1

private def cycleEdge (u v : ℕ) : Bool := (u == 0 && v == 1) || (u == 1 && v == 0)

private def cycleChoice (s : State) : Bool :=
  (s.phase == .candidate && (s.round != 0 || s.candidate == 0)) ||
    (s.phase == .guess && s.candidate == 1)

-- Singleton, edgeless, non-power-of-two, and cyclic graph runs of `drive`, together with `step`,
-- `Bounded`, `initial`, and `accepts_iff`.
example :
    (drive 1 0 0 noEdge noBad (onlySource 0) 8 (initial 1 0)).phase = .accept ∧
    (drive 1 0 0 noEdge (badAt 0) (onlySource 0) 8 (initial 1 0)).phase = .reject ∧
    (drive 2 1 0 noEdge (badAt 1) (onlySource 0) 80 (initial 2 0)).phase = .accept ∧
    (drive 2 1 1 noEdge (badAt 0) (onlySource 1) 80 (initial 2 1)).phase = .accept ∧
    (drive 2 1 0 noEdge (badAt 0) (onlySource 0) 80 (initial 2 0)).phase = .reject ∧
    (drive 3 2 0 noEdge (badAt 2) (onlySource 0) 120 (initial 3 0)).phase = .accept ∧
    (drive 2 1 0 cycleEdge noBad cycleChoice 100 (initial 2 0)).phase = .accept ∧
    (drive 2 1 0 cycleEdge (badAt 1) cycleChoice 100 (initial 2 0)).phase = .reject ∧
    (drive 2 1 0 cycleEdge (badAt 1) (onlySource 0) 100 (initial 2 0)).phase = .reject ∧
    (drive 2 1 0 noEdge noBad (fun _ => false) 20 (initial 2 0)).phase = .reject ∧
    step 2 1 0 noEdge noBad
      { phase := .done, count := 1, selected := 0, finalScan := true } false = reject ∧
    Bounded 2 1 { phase := .done, count := 2, selected := 2 } ∧
    step 3 2 0 noEdge noBad { phase := .guess, guess := 3, bits := 0 } false = reject ∧
    step 3 2 0 noEdge noBad
      (step 3 2 0 noEdge noBad { phase := .guess, guess := 0, bits := 2 } true) false =
        { phase := .guess, guess := 2, bits := 0 } ∧
    step 2 1 0 noEdge noBad
      { phase := .edge, current := 0, guess := 1, remaining := 1 } false = reject ∧
    initial 0 0 = reject ∧
    initial 2 2 = reject := by
  decide

-- The primitive correctness theorem is uniform in the graph, not just these computations.
example (edge : ℕ → ℕ → Bool) (bad : ℕ → Bool) :
    Accepts 1 0 0 edge bad ↔ Safe 1 0 edge bad := accepts_iff (by decide) (by decide)

/--
info: 'Cslib.InductiveCounting.halted_replay_budget' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.InductiveCounting.halted_replay_budget

end ComplexityTests.InductiveCounting
