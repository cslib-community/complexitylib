/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify

/-!
# Exact alternating semantics of deterministic leaf machines

Duplicating a deterministic transition table for both alternating moves incurs no time overhead.
The player labels are arbitrary, since both successors coincide. These lemmas apply at arbitrary
physical configurations, so a work-tape query runner can supply a native alternating leaf without
resetting its storage or treating deterministic execution as an oracle.
-/

public section

namespace Turing.MultiTapeATM

/-- Duplicating deterministic transitions preserves the exact all-branch halting clock. -/
theorem haltsWithin_ofTMs_const_iff {k : ℕ} {Symbol S : Type}
    (tm : MultiTapeTM k Symbol S) (player : S → Bool) {input : List Symbol}
    (n : ℕ) (cfg : Cfg k Symbol S input) :
    (ofTMs (fun _ => tm) player).HaltsWithin n cfg ↔ (tm.runFrom cfg n).state = none := by
  induction n generalizing cfg with
  | zero => exact haltsWithin_zero
  | succ n ih =>
    rw [haltsWithin_succ]
    simp only [next_ofTMs, ih, forall_const]
    rfl

/-- Duplicating a deterministic machine accepts exactly its halted singleton-true outputs. -/
theorem acceptsWithin_ofTMs_const_iff {k : ℕ} {S : Type}
    (tm : MultiTapeTM k Bool S) (player : S → Bool) {input : List Bool}
    (n : ℕ) (cfg : Cfg k Bool S input) :
    (ofTMs (fun _ => tm) player).AcceptsWithin n cfg ↔
      (tm.runFrom cfg n).state = none ∧ (tm.runFrom cfg n).output = [true] := by
  induction n generalizing cfg with
  | zero => rfl
  | succ n ih =>
    rw [acceptsWithin_succ_of_next_eq (fun b => next_ofTMs (fun _ => tm) player b cfg), ih]
    rfl

end Turing.MultiTapeATM
