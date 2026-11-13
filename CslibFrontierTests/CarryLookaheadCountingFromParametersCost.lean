/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingFromParametersCost
import CslibFrontierTests.CarryLookaheadCounting
import CslibFrontierTests.CountingLeafRawCost

/-!
A primitive constant-time predicate yields one actual machine that initializes and answers both
bits of empty and positive counts. The context is arbitrarily long, while the complete native
clock is exactly affine in its length. Both claimed values use the actual initial control state.
-/

namespace CslibFrontierTests.CarryLookaheadCountingFromParametersCost

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib Cslib.Circuits.Boolean.CarryLookahead.Query
open Turing.MultiTapeATM.CarryLookaheadCountingFromParametersCost

example : ∃ (scratch k r q : ℕ) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool S)
    (cInit dInit c d cRoot dRoot : ℕ),
    ∀ (input context : List Bool) (filled : Bool) (bit : Fin 2) (claim : Bool),
      let a : CountingInput.Input := ⟨if filled then 2 else 0, ⟨2, bit.val, claim⟩⟩
      let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
        (some atm.toPTM.initial)
      let t := clock cInit dInit c d cRoot dRoot [] a 0 + (cRoot + 4) * context.length
      atm.HaltsWithin t start ∧
        (atm.AcceptsWithin t start ↔ (filled && (bit == 1)) = claim) := by
  obtain ⟨scratch, k, r, q, S, hS, atm, cInit, dInit, c, d, cRoot, dRoot, h⟩ :=
    exists_evaluator (fun _ => true) CountingLeafRawCost.true_inO
  refine ⟨scratch, k, r, q, S, hS, atm, cInit, dInit, c, d, cRoot, dRoot, ?_⟩
  intro input context filled bit claim
  have hrun := h input context (if filled then 2 else 0) 2 bit claim 0
    (fun _ _ => Nat.le_refl 0)
  dsimp only at hrun ⊢
  rw [clock_eq_empty, Nat.mul_zero, Nat.add_zero] at hrun
  refine ⟨hrun.1, hrun.2.trans ?_⟩
  rw [CarryLookaheadCounting.count_bits]

end CslibFrontierTests.CarryLookaheadCountingFromParametersCost
