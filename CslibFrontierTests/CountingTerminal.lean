/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminal
import CslibFrontierTests.CarrySaveCountingRoot

namespace CslibFrontierTests.CountingTerminal

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib.Circuits.Boolean.CarryLookahead.Query
open Cslib.Circuits.Boolean.CarrySaveQuery
open Turing.MultiTapeATM.CountingTerminal

private def position (carry claim : Bool) : Routing.Position :=
  Routing.ofClaim 2 1 ⟨.input (if carry then 3 else 1), claim⟩

-- The complete native terminal prepares its flags, copies its index, and evaluates a positive
-- carry-save layer. Both operand selectors and both claimed answers use one finite machine.
example : ∃ (k r : ℕ) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM (CountingTerminalLayout.size k r) Bool S) (cP dP cR dR : ℕ),
    ∀ (input : List Bool) (carry claim : Bool),
      let p := position carry claim
      let cfg := (CountingTerminalLayout.storage k r input [] 2 2 p []).withState
        (some atm.toPTM.initial)
      atm.HaltsWithin (clock cP dP cR dR [] 2 2 p) cfg ∧
        (atm.AcceptsWithin (clock cP dP cR dR [] 2 2 p) cfg ↔ (!carry) = claim) := by
  obtain ⟨k, r, S, hS, atm, cP, dP, cR, dR, h⟩ := exists_evaluator (fun _ => true)
    (ComputableInPolyTime.const true)
  refine ⟨k, r, S, hS, atm, cP, dP, cR, dR, ?_⟩
  intro input carry claim
  have hrun := h input [] 2 2 (position carry claim) rfl
  refine ⟨hrun.1, hrun.2.trans ?_⟩
  have hbits (b : Bool) : component (Counting.rootPair 2 2 (fun _ => true)) b (1 : Fin 2) = !b :=
    CslibFrontierTests.CarrySaveCountingRoot.root_bit b
  cases carry <;> simp [Terminal.response, Terminal.queries, Terminal.carry, Terminal.index,
    position, Routing.ofClaim, Address.toData, hbits]

-- Width and count zero still run native terminal preparation. Padded input is zero, so a false
-- claim accepts and a true claim rejects without assuming any root-component query exists.
example : ∃ (k r : ℕ) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM (CountingTerminalLayout.size k r) Bool S) (cP dP cR dR : ℕ),
    ∀ (input : List Bool) (claim : Bool),
      let p := Routing.ofClaim 0 0 ⟨.input 0, claim⟩
      let cfg := (CountingTerminalLayout.storage k r input [] 0 0 p []).withState
        (some atm.toPTM.initial)
      atm.HaltsWithin (clock cP dP cR dR [] 0 0 p) cfg ∧
        (atm.AcceptsWithin (clock cP dP cR dR [] 0 0 p) cfg ↔ false = claim) := by
  obtain ⟨k, r, S, hS, atm, cP, dP, cR, dR, h⟩ := exists_evaluator (fun _ => true)
    (ComputableInPolyTime.const true)
  refine ⟨k, r, S, hS, atm, cP, dP, cR, dR, ?_⟩
  intro input claim
  have hrun := h input [] 0 0 (Routing.ofClaim 0 0 ⟨.input 0, claim⟩) rfl
  refine ⟨hrun.1, hrun.2.trans ?_⟩
  cases claim <;> simp [Terminal.response, Terminal.queries, Terminal.answer, Routing.operation,
    Routing.ofClaim, Address.toData, opData]

end CslibFrontierTests.CountingTerminal
