/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify

/-!
# Step-exact state simulations of alternating machines

A state map preserving the player and both native transitions preserves bounded acceptance
and all-branch halting with exactly the same budget. Injectivity is unnecessary: a finite
controller can identify equivalent copies of continuation states. The configuration map
preserves tapes, head positions and output, and maps halting precisely to halting.
-/

public section

namespace Turing.MultiTapeATM

variable {k : ℕ} {S T : Type}

/-- A state-only simulation preserving every machine step and its alternating player. -/
structure StateSimulation (source : MultiTapeATM k Bool S) (target : MultiTapeATM k Bool T) where
  /-- Map finite control; distinct source states may have the same image. -/
  stateMap : S → T
  /-- Universal and existential states keep their player. -/
  universal_eq : ∀ q, target.universal (stateMap q) = source.universal q
  /-- Both possible transitions commute with the configuration map, on every tape contents. -/
  next_eq : ∀ {input : List Bool} (c : Cfg k Bool S input) (b : Bool),
    target.next b (c.mapState (Option.map stateMap)) =
      (source.next b c).mapState (Option.map stateMap)

namespace StateSimulation

variable {source : MultiTapeATM k Bool S} {target : MultiTapeATM k Bool T}
  (h : StateSimulation source target)

/-- A state simulation preserves acceptance within exactly the same number of steps. -/
theorem acceptsWithin_iff {input : List Bool} (n : ℕ) (c : Cfg k Bool S input) :
    target.AcceptsWithin n (c.mapState (Option.map h.stateMap)) ↔ source.AcceptsWithin n c := by
  induction n generalizing c with
  | zero => simp [AcceptsWithin, Cfg.mapState]
  | succ n ih =>
    cases hs : c.state with
    | none => simp [AcceptsWithin, Cfg.mapState, hs]
    | some q =>
      simp only [AcceptsWithin, Cfg.mapState_state, hs, Option.map_some, h.universal_eq]
      simp only [h.next_eq, ih]

/-- Every branch has the same halting bound; this includes incorrect existential guesses. -/
theorem haltsWithin_iff {input : List Bool} (n : ℕ) (c : Cfg k Bool S input) :
    target.HaltsWithin n (c.mapState (Option.map h.stateMap)) ↔ source.HaltsWithin n c := by
  induction n generalizing c with
  | zero => simp [haltsWithin_zero, Cfg.mapState]
  | succ n ih => simp only [haltsWithin_succ, h.next_eq, ih]

end StateSimulation
end Turing.MultiTapeATM
