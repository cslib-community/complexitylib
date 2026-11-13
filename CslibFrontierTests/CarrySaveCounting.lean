/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCounting

namespace CslibFrontierTests.CarrySaveCounting

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Turing.MultiTapeATM.CarrySaveCounting
open Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarrySaveQuery

private theorem frontier_one : CarrySaveStream.Frontier [true] 0 1 := by
  intro j
  rw [zero_add, tapeOfList_ofNat]
  cases j <;> simp

-- Two true counting leaves are compressed by the actual cyclic machine. Padded counters
-- survive the native leaf interface; the sum and carry bits differ, testing both claims.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
    ∀ (input : List Bool) (carry claim : Bool),
    let cfg := (CarrySaveLeaf.initial k input [] [false, true, false] [false, true, false]
      [true, false] [true, false] [] [true] 0 false).withState
        (some (atm carry claim).toPTM.toNTM.q₀)
    let time := CarrySaveStream.budget
      (CarrySaveLeaf.clock c d [] [false, true, false] [false, true, false] 5)
      1 [true, false] [true, false]
    (atm carry claim).HaltsWithin time cfg ∧
      ((atm carry claim).AcceptsWithin time cfg ↔ (!carry) = claim) := by
  obtain ⟨k, S, hS, atm, c, d, h⟩ := exists_evaluator (fun _ => true)
    (ComputableInPolyTime.const true)
  refine ⟨k, S, hS, atm, c, d, fun input carry claim => ?_⟩
  have hv : value (leaves (fun _ => true) [] [false, true, false] [false, true, false])
      ⟨[], 1, carry, 1⟩ = !carry := by
    rw [value_layer _ _ 0 carry ⟨1, by decide⟩]
    cases carry <;> simp [CarrySaveLocal.eval_formula, descend, CarrySaveLocal.source,
      value, tree, leaves, Counting.component_leafPair, ofBits, Cslib.BitString.binaryValue,
      childSide, childCarry, maj3]
  simpa only [show Cslib.BitString.lsbValue [true, false] = 1 from rfl, hv] using
    h input [] [false, true, false] [false, true, false] [true, false] [true, false] [] [true]
      1 0 false carry claim 5 frontier_one (by decide) rfl (by decide)

-- A nonempty persistent path reaches only padded leaves outside the count. The same native
-- composition rejects a true claim and accepts a false claim for either component.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
    ∀ (input : List Bool) (carry claim : Bool),
    let cfg := (CarrySaveLeaf.initial k input [] [false, true] [false, true]
      [true] [false] [true] [true] 0 true).withState
        (some (atm carry claim).toPTM.toNTM.q₀)
    let time := CarrySaveStream.budget
      (CarrySaveLeaf.clock c d [] [false, true] [false, true] 4) 1 [true] [false]
    (atm carry claim).HaltsWithin time cfg ∧
      ((atm carry claim).AcceptsWithin time cfg ↔ false = claim) := by
  obtain ⟨k, S, hS, atm, c, d, h⟩ := exists_evaluator (fun _ => true)
    (ComputableInPolyTime.const true)
  refine ⟨k, S, hS, atm, c, d, fun input carry claim => ?_⟩
  have hv : value (leaves (fun _ => true) [] [false, true] [false, true])
      ⟨[true], 1, carry, 0⟩ = false := by
    rw [value_layer _ _ 0 carry ⟨0, by decide⟩]
    cases carry <;> simp [CarrySaveLocal.eval_formula, descend, CarrySaveLocal.source,
      value, tree, leaves, Counting.component_leafPair, ofBits, Cslib.BitString.binaryValue,
      childSide, childCarry, maj3]
  simpa only [show Cslib.BitString.lsbValue [false] = 0 from rfl, hv] using
    h input [] [false, true] [false, true] [true] [false] [true] [true]
      1 0 true carry claim 4 frontier_one (by decide) rfl (by decide)

end CslibFrontierTests.CarrySaveCounting
