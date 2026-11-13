/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingClockBound
import CslibFrontierTests.CountingLeafRawCost
import Mathlib.Tactic.FinCases

/-!
The same native machine tests both claims and bits with arbitrary contexts, starting from raw
parameters. Five positive leaves overflow precision two; their low bit remains true. Empty
counts reject the same true claim, all at the simplified context-linear clock.
-/

namespace CslibFrontierTests.CarryLookaheadCountingClockBound

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib.Circuits.Boolean.CarryLookahead.Query
open Turing.MultiTapeATM.CarryLookaheadCountingFromParametersCost

example : ∃ (scratch k r q : ℕ) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool S) (A D : ℕ),
    ∀ (input context : List Bool) (filled : Bool) (bit : Fin 2) (claim : Bool),
      let n := if filled then 5 else 0
      let a : CountingInput.Input := ⟨n, ⟨2, bit.val, claim⟩⟩
      let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
        (some atm.toPTM.initial)
      let time := A * (context.length + (n.size + (2 : ℕ).size + 1) ^ D)
      atm.HaltsWithin time start ∧
        (atm.AcceptsWithin time start ↔ (filled && (bit == 0)) = claim) := by
  obtain ⟨scratch, k, r, q, S, hS, atm, A, D, h⟩ :=
    exists_evaluator_testBit (fun _ => true) CountingLeafRawCost.true_inO
  refine ⟨scratch, k, r, q, S, hS, atm, A, D, ?_⟩
  intro input context filled bit claim
  have hrun := h input context (if filled then 5 else 0) 2 bit claim 0
    (fun _ _ => Nat.le_refl 0)
  dsimp only at hrun ⊢
  rw [Nat.add_zero] at hrun
  refine ⟨hrun.1, hrun.2.trans ?_⟩
  have hbit : (∑ j ∈ Finset.range (if filled then 5 else 0), (true : Bool).toNat).testBit
      bit.val = (filled && (bit == 0)) := by
    cases filled <;> fin_cases bit <;> decide
  rw [hbit]

end CslibFrontierTests.CarryLookaheadCountingClockBound
