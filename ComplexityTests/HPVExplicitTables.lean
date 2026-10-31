/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.TablePolyTime

/-! The tables of the explicit block-counting networks on numbers: decoded letters, table entries
of a concrete machine read off the explicit network, and the polynomial-time certificate. -/

namespace ComplexityTests.HPVExplicitTables

open Turing MultiTapeMachine MultiTapePTM MultiTapeNTM.ChoiceTable Cslib.Circuits.Frontier

/-- Emit the first coin and halt. No work tapes; the input head stays. -/
private def emitCoin : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

/-! ### Decoding letters -/

-- With two states, one work tape and blocks of two cells there are `3 * (2 ^ 2 * 3) = 36`
-- control records. Letter `34` is the record of state `true`, both offsets `1` and output track
-- `accept` (compare `HPVExplicitBlockNetwork`), and letter `44` is the block holding `true` twice.
example : decodeControlData (k := 1) finTwoEquiv.symm 2 34 =
    controlData (some true, (fun _ => 1 : Option (Fin 1) → ZMod 2), OutputTrack.accept) := by
  rw [show (34 : ℕ) = letterEquiv (k := 1) (b := 2) finTwoEquiv.symm
    (.inl (some true, fun _ => 1, .accept)) by decide]
  simp only [letterEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.val_castAdd, decodeControlData_controlEquiv]

example : contentsCellNum 1 2 2 44 0 = some true ∧ contentsCellNum 1 2 2 44 1 = some true ∧
    acceptNum 1 2 2 34 = 1 ∧ acceptNum 1 2 2 44 = 0 := by decide

/-! ### Table entries of `emitCoin` -/

-- One interval of two steps; letters of `10` bits. The interval (vertex `0`) has the source
-- halves of its control edge as ports. At index `1` its leaving letter is number `1`: halted,
-- offsets `0`, output track `accept`, reached by the two coin strings starting with `true`.
example : ((emitCoin.explicitBlockNetwork [] 2 (scheduleOfNat 0 1 1)
    (Equiv.ofUnique Unit (Fin 1))).vertices[0]!.2)[1]! = 2 := by
  rw [explicitBlockNetwork_eq_explicitNetworkNum]
  decide +kernel

-- The sink of the control edge (vertex `1`) accepts letter `1` and rejects letter `0`, whose
-- output track is empty.
example : ((emitCoin.explicitBlockNetwork [] 2 (scheduleOfNat 0 1 1)
      (Equiv.ofUnique Unit (Fin 1))).vertices[1]!.2)[1]! = 1 ∧
    ((emitCoin.explicitBlockNetwork [] 2 (scheduleOfNat 0 1 1)
      (Equiv.ofUnique Unit (Fin 1))).vertices[1]!.2)[0]! = 0 := by
  rw [explicitBlockNetwork_eq_explicitNetworkNum]
  decide +kernel

-- A subdivision vertex (vertex `2`) is the equality of the bits on its two ports.
example : (emitCoin.explicitBlockNetwork [] 2 (scheduleOfNat 0 1 1)
    (Equiv.ofUnique Unit (Fin 1))).vertices[2]!.2 = [1, 0, 0, 1] := by
  rw [explicitBlockNetwork_eq_explicitNetworkNum]
  decide +kernel

/-! ### Polynomial time -/

-- The network of `emitCoin` with blocks of two steps and one interval is polynomial-time in the
-- schedule number, with `2 ^ 2 ≤ 4`.
example : MultiTapeTM.ComputableInPolyTime (fun σ : ℕ =>
    ((explicitNetworkNum (Equiv.ofUnique Unit (Fin 1)) 2 emitCoin [] 1 σ).numEdges,
      (explicitNetworkNum (Equiv.ofUnique Unit (Fin 1)) 2 emitCoin [] 1 σ).vertices))
    MultiTapeTM.encNat (MultiTapeTM.encPair MultiTapeTM.encUnary
      (MultiTapeTM.encList (MultiTapeTM.encPair (MultiTapeTM.encList MultiTapeTM.encNat)
        (MultiTapeTM.encList MultiTapeTM.encNat)))) :=
  computableInPolyTime_explicitNetworkNum (Equiv.ofUnique Unit (Fin 1)) emitCoin (.const _)
    (.const _) (fun _ => two_pos) (.const _) MultiTapeTM.ComputableInPolyTime.id' (.const 4)
    (fun _ => le_refl 4)

end ComplexityTests.HPVExplicitTables
