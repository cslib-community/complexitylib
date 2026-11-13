/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCountingRoot

namespace CslibFrontierTests.CarrySaveCountingRoot

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Cslib.Circuits.Boolean.CarrySaveQuery
open Turing.MultiTapeATM.CarrySaveCountingRoot

-- One finite family handles both a singleton nonzero sum and the empty count.
-- Each query checks both possible claims at the same bit-independent clock.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
    ∀ (input : List Bool) (carry claim : Bool),
      ((atm carry claim).AcceptsWithin (clock c d [] 1 2)
        ((initial k input [] 1 2 0).withState
          (some (atm carry claim).toPTM.toNTM.q₀)) ↔ (!carry) = claim) ∧
      ((atm carry claim).AcceptsWithin (clock c d [] 0 2)
        ((initial k input [] 0 2 0).withState
          (some (atm carry claim).toPTM.toNTM.q₀)) ↔ false = claim) := by
  obtain ⟨k, S, hS, atm, c, d, h⟩ := exists_evaluator (fun _ => true)
    (ComputableInPolyTime.const true)
  refine ⟨k, S, hS, atm, c, d, fun input carry claim => ?_⟩
  have hone : component (Counting.rootPair 1 2 (fun _ => true)) carry ⟨0, by decide⟩ =
      !carry := by
    cases carry <;> simp [Counting.rootPair, tree, Counting.component_leafPair,
      Cslib.BitString.binaryValue]
  have hzero : component (Counting.rootPair 0 2 (fun _ => true)) carry ⟨0, by decide⟩ =
      false := by
    cases carry <;> simp [Counting.rootPair, tree, Counting.component_leafPair,
      Cslib.BitString.binaryValue]
  exact ⟨(h input [] 1 2 ⟨0, by decide⟩ carry claim).2.trans (by rw [hone]),
    (h input [] 0 2 ⟨0, by decide⟩ carry claim).2.trans (by rw [hzero])⟩

/-- A shared positive-depth fixture: bit one distinguishes the two root components. -/
theorem root_bit (carry : Bool) :
    component (Counting.rootPair 2 2 (fun _ => true)) carry ⟨1, by decide⟩ = !carry := by
  have hv : value
      (fun path => Counting.leafPair 2 2 (fun _ => true) (Cslib.BitString.binaryValue path))
      ⟨[], 1, carry, 1⟩ = !carry := by
    rw [value_layer _ _ 0 carry ⟨1, by decide⟩]
    cases carry <;> simp [Cslib.Circuits.Boolean.CarrySaveLocal.eval_formula, descend,
      Cslib.Circuits.Boolean.CarrySaveLocal.source, value, tree, Counting.component_leafPair,
      Cslib.BitString.binaryValue, childSide, childCarry, Cslib.Circuits.Boolean.maj3]
  simpa [value, Counting.rootPair, show Nat.clog 2 2 = 1 from by decide] using hv

-- Two counted leaves exercise a positive canonical frontier. At bit one the sum is true
-- and the carry is false; both claims and all branches use the same root clock.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
    ∀ (input : List Bool) (carry claim : Bool),
      let cfg := (initial k input [] 2 2 1).withState
        (some (atm carry claim).toPTM.toNTM.q₀)
      (atm carry claim).HaltsWithin (clock c d [] 2 2) cfg ∧
        ((atm carry claim).AcceptsWithin (clock c d [] 2 2) cfg ↔ (!carry) = claim) := by
  obtain ⟨k, S, hS, atm, c, d, h⟩ := exists_evaluator (fun _ => true)
    (ComputableInPolyTime.const true)
  refine ⟨k, S, hS, atm, c, d, fun input carry claim => ?_⟩
  simpa only [root_bit] using h input [] 2 2 ⟨1, by decide⟩ carry claim


end CslibFrontierTests.CarrySaveCountingRoot
