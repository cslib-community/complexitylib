/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCountingRootCost
import CslibFrontierTests.CarrySaveCountingRoot

/-! Actual root queries retain a primitive time bound linear in an arbitrarily long context.
The positive-depth case distinguishes the two components; empty-domain padding rejects true
claims with the same finite machine family. -/

namespace CslibFrontierTests.CarrySaveCountingCost

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Cslib.Circuits.Boolean.CarrySaveQuery

private theorem query_length_le (context path : List Bool) (budget : ℕ)
    (hpath : path.length ≤ budget) :
    (encPair encBits encNat (context, Cslib.BitString.binaryValue path)).length ≤
      2 * context.length + budget + 2 := by
  have hsize := Nat.size_le.2 (Cslib.BitString.binaryValue_lt_two_pow path)
  rw [length_encPair]
  simpa only [encBits_apply, encNat_apply, Nat.size_eq_bits_len] using
    (show 2 * context.length + 1 + (Cslib.BitString.binaryValue path).size ≤
      2 * context.length + budget + 2 by omega)

example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
    ∀ (input context : List Bool) (carry claim : Bool),
      let positive := (CarrySaveCountingRoot.initial k input context 2 2 1).withState
        (some (atm carry claim).toPTM.toNTM.q₀)
      let empty := (CarrySaveCountingRoot.initial k input context 0 2 0).withState
        (some (atm carry claim).toPTM.toNTM.q₀)
      let positiveTime := CarrySaveCountingRootCost.clock c d context 2 2
        (2 * context.length + 6)
      let emptyTime := CarrySaveCountingRootCost.clock c d context 0 2
        (2 * context.length + 4)
      (atm carry claim).HaltsWithin positiveTime positive ∧
        ((atm carry claim).AcceptsWithin positiveTime positive ↔ (!carry) = claim) ∧
        (atm carry claim).HaltsWithin emptyTime empty ∧
        ((atm carry claim).AcceptsWithin emptyTime empty ↔ false = claim) := by
  obtain ⟨k, S, hS, atm, c, d, h⟩ := CarrySaveCountingRootCost.exists_evaluator
    (fun _ => true) (ComputableInO.const true)
  refine ⟨k, S, hS, atm, c, d, ?_⟩
  intro input context carry claim
  have hp := h input context 2 2 ⟨1, by decide⟩ carry claim (2 * context.length + 6)
    (fun path hpath => by
      have hb : path.length ≤ 4 := hpath
      simpa only [Nat.add_assoc] using query_length_le context path 4 hb)
  have he := h input context 0 2 ⟨0, by decide⟩ carry claim (2 * context.length + 4)
    (fun path hpath => by
      have hb : path.length ≤ 2 := hpath
      simpa only [Nat.add_assoc] using query_length_le context path 2 hb)
  have hzero : component (Counting.rootPair 0 2 (fun _ => true)) carry ⟨0, by decide⟩ =
      false := by
    cases carry <;> simp [Counting.rootPair, tree, Counting.component_leafPair,
      Cslib.BitString.binaryValue]
  exact ⟨hp.1, hp.2.trans (by rw [CarrySaveCountingRoot.root_bit]),
    he.1, he.2.trans (by rw [hzero])⟩

end CslibFrontierTests.CarrySaveCountingCost
