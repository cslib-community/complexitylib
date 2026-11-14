/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CountingTerminal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCountingRootCost

/-!
# Counting terminals with a separate primitive predicate cost

The existing native preparation, request dispatch and index copy invoke the root evaluator
compiled from a plain resource certificate. Their short-metadata overhead adds to the root's
context-linear clock. A supplied scalar bounds only the primitive predicate on the reachable
path domain; neither a complete counting answer nor a counting-machine contract is assumed.
-/

public section

namespace Turing.MultiTapeATM.CountingTerminalCost

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query
open Cslib.Circuits.Boolean.CarrySaveQuery

/-- One finite native terminal retains the primitive predicate's separate runtime bound.
All machine and preparation constants precede the runtime data and the path-domain bound. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool) {T W : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T W) :
    ∃ (k r : ℕ) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM (CountingTerminalLayout.size k r) Bool S) (cP dP cR dR : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (p : Routing.Position) (hw : p.width = w)
        (predicateTime : ℕ),
        (∀ path : List Bool, path.length ≤ CarrySaveCountingRoot.sizeBudget n w →
          T (context, Cslib.BitString.binaryValue path) ≤ predicateTime) →
        let root := Counting.rootPair n w (fun j => predicate (context, j))
        let cfg := (CountingTerminalLayout.storage k r input context n w p []).withState
          (some atm.toPTM.initial)
        let time := CountingTerminal.clockOfRoot cP dP w p
          (CarrySaveCountingRootCost.clock cR dR context n w predicateTime)
        atm.HaltsWithin time cfg ∧
          (atm.AcceptsWithin time cfg ↔
            Terminal.response (component root false) (component root true) p hw = true) := by
  obtain ⟨k, SR, hSR, roots, cR, dR, hroots⟩ :=
    CarrySaveCountingRootCost.exists_evaluator predicate hp
  let := hSR
  obtain ⟨r, S, hS, atm, cP, dP, h⟩ := CountingTerminal.exists_evaluator_of_root predicate roots
  refine ⟨k, r, S, hS, atm, cP, dP, cR, dR, ?_⟩
  intro input context n w p hw predicateTime htime
  exact h input context n w (CarrySaveCountingRootCost.clock cR dR context n w predicateTime)
    (fun bit carry claim => hroots input context n w bit carry claim predicateTime htime) p hw

end Turing.MultiTapeATM.CountingTerminalCost
