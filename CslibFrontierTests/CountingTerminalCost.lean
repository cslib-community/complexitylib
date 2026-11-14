/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminalCost
import CslibFrontierTests.CarrySaveCountingRoot
import CslibFrontierTests.CountingLeafRawCost

/-!
One actual terminal machine handles both operand selectors and padded constants, with arbitrary
context and both claims. The primitive predicate has constant time and workspace, so the terminal
clock's context cost is supplied by the native counting computation rather than a predicate bound.
-/

namespace CslibFrontierTests.CountingTerminalCost

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib.Circuits.Boolean.CarryLookahead.Query
open Cslib.Circuits.Boolean.CarrySaveQuery

example : ∃ (k r : ℕ) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM (CountingTerminalLayout.size k r) Bool S) (cP dP cR dR : ℕ),
    ∀ (input context : List Bool) (live carry claim : Bool),
      let p := Routing.ofClaim 2 1 ⟨.input (if live then if carry then 3 else 1 else 4), claim⟩
      let cfg := (CountingTerminalLayout.storage k r input context 2 2 p []).withState
        (some atm.toPTM.initial)
      let time := CountingTerminal.clockOfRoot cP dP 2 p
        (CarrySaveCountingRootCost.clock cR dR context 2 2 0)
      atm.HaltsWithin time cfg ∧
        (atm.AcceptsWithin time cfg ↔ (if live then !carry else false) = claim) := by
  obtain ⟨k, r, S, hS, atm, cP, dP, cR, dR, h⟩ :=
    Turing.MultiTapeATM.CountingTerminalCost.exists_evaluator (fun _ => true)
      CslibFrontierTests.CountingLeafRawCost.true_inO
  refine ⟨k, r, S, hS, atm, cP, dP, cR, dR, ?_⟩
  intro input context live carry claim
  let p := Routing.ofClaim 2 1 ⟨.input (if live then if carry then 3 else 1 else 4), claim⟩
  have hr := h input context 2 2 p rfl 0 (fun _ _ => by decide)
  refine ⟨hr.1, hr.2.trans ?_⟩
  have hbits (b : Bool) : component (Counting.rootPair 2 2 (fun _ => true)) b (1 : Fin 2) = !b :=
    CslibFrontierTests.CarrySaveCountingRoot.root_bit b
  cases live <;> cases carry <;>
    simp [Terminal.response, Terminal.queries, Terminal.carry, Terminal.index, Terminal.answer,
      Routing.operation, p, Routing.ofClaim, Address.toData, opData, hbits]

end CslibFrontierTests.CountingTerminalCost
