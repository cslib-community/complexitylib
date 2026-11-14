/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingFromLeaves
import CslibFrontierTests.CarryLookaheadCounting
import CslibFrontierTests.CountingLeafRawCost

/-!
The direct alternating-leaf route runs the existing concrete native leaf family, initializes all
count fields from raw parameters, and answers both bits and claims for empty and positive counts.
The same machine accepts any additional runtime padding of the leaf clock, charged additively.
-/

namespace CslibFrontierTests.CarryLookaheadCountingFromLeaves

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib Cslib.Circuits.Boolean.CarryLookahead.Query
open Turing.MultiTapeATM.CarryLookaheadCountingFromLeaves

example : ∃ (scratch k r q : ℕ) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r q) Bool S)
    (A D cLeaf dLeaf : ℕ),
    ∀ (input context : List Bool) (filled : Bool) (bit : Fin 2) (claim : Bool) (extra : ℕ),
      let n := if filled then 2 else 0
      let a : CountingInput.Input := ⟨n, ⟨2, bit.val, claim⟩⟩
      let start := (CarryLookaheadCountingPrepare.initial scratch k r q input context a).withState
        (some atm.toPTM.initial)
      let leafTime := CarrySaveLeafCost.clock cLeaf dLeaf context (encNat n) (encNat 2)
        (CarrySaveCountingRoot.sizeBudget n 2) 0
      let t := A * (n.size + (2 : ℕ).size + 1) ^ D + (leafTime + extra)
      atm.HaltsWithin t start ∧
        (atm.AcceptsWithin t start ↔ (filled && (bit == 1)) = claim) := by
  obtain ⟨k, SL, hSL, leaf, cLeaf, dLeaf, hleaf⟩ :=
    CarrySaveCountingCost.exists_leaves (fun _ => true) CountingLeafRawCost.true_inO
  let : Finite SL := hSL
  obtain ⟨scratch, r, q, S, hS, atm, A, D, h⟩ := exists_evaluator (fun _ => true) leaf
  refine ⟨scratch, k, r, q, S, hS, atm, A, D, cLeaf, dLeaf, ?_⟩
  intro input context filled bit claim extra
  let n := if filled then 2 else 0
  let B := CarrySaveCountingRoot.sizeBudget n 2
  let leafTime := CarrySaveLeafCost.clock cLeaf dLeaf context (encNat n) (encNat 2) B 0
  obtain ⟨ht, ha⟩ := hleaf input context (encNat n) (encNat 2) B 0
    (fun _ _ => Nat.le_refl 0)
  have ht' : CarrySaveStream.LeafBound leaf (leafTime + extra) B input
      (CarrySaveLeaf.scratch k context (encNat n) (encNat 2)) := by
    intro height bits path unary frontier status carry value hf hs
    exact (ht height bits path unary frontier status carry value hf hs).mono (Nat.le_add_right _ _)
  have ha' : CarrySaveStream.LeafCorrect
      (CarrySaveCounting.leaves (fun _ => true) context (encNat n) (encNat 2)) leaf
      (leafTime + extra) B input (CarrySaveLeaf.scratch k context (encNat n) (encNat 2)) := by
    intro height bits path unary frontier status carry value hf hs hb
    have hh := ht height bits path unary frontier status carry value hf hs
    have hv := ha height bits path unary frontier status carry value hf hs hb
    exact ⟨fun h => hv.mp (h.of_halted_stepCoins hh),
      fun h => (hv.mpr h).mono (Nat.le_add_right _ _)⟩
  have hr := h input context n 2 bit claim (leafTime + extra) ht' ha'
  have hbits := CarryLookaheadCounting.count_bits filled bit
  rw [Circuits.Boolean.CarrySaveQuery.Counting.count_apply] at hbits
  exact ⟨hr.1, hr.2.trans (by rw [hbits])⟩

end CslibFrontierTests.CarryLookaheadCountingFromLeaves
