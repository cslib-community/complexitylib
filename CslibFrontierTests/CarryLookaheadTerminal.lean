/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Terminal

/-! Terminal requests use actual operands and treat the incoming carry as padded zero. -/

namespace CslibFrontierTests.CarryLookaheadTerminal

open Cslib Cslib.Circuits.Boolean.CarryLookahead.Query Routing Terminal Turing.MultiTapeTM

example : ComputableInPolyTime word encPosition encBits := word_polyTime

example (w rounds : ℕ) (i : Fin w) (claim : Bool) :
    word (ofClaim w rounds ⟨.input (w + i.val), claim⟩) =
      [true, true, claim] ++ encNat i.val := word_input_right w rounds i claim

/-- Width zero immediately checks the padded incoming carry and requests no operand. -/
example : word (ofClaim 0 0 ⟨.input 0, false⟩) = [false, true, true] := by
  simpa using word_input_padding 0 0 false

/-- The classifier's dummy zero does not replace an actual true input bit. -/
example : response ![true] ![false] (ofClaim 1 0 ⟨.input 0, true⟩) rfl = true ∧
    response ![true] ![false] (ofClaim 1 0 ⟨.input 0, false⟩) rfl = false := by
  decide

/-- An out-of-range input takes the immediate zero branch. -/
example : queries (ofClaim 1 0 ⟨.input 3, false⟩) = false ∧
    response ![true] ![true] (ofClaim 1 0 ⟨.input 3, false⟩) rfl = true := by
  decide

/-- A terminal response evaluates the actual operand, independently of the dummy classifier. -/
example (w rounds : ℕ) (left right : BitString w) (i : Fin w) (claim : Bool) :
    response left right (ofClaim w rounds ⟨.input i.val, claim⟩) rfl = true ↔
      value w rounds (Fin.append (Fin.append left right) ![false]) (.input i.val) = claim :=
  response_eq_true_iff w rounds left right ⟨.input i.val, claim⟩ rfl

end CslibFrontierTests.CarryLookaheadTerminal
