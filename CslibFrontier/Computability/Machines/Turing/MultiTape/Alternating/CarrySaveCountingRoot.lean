/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCounting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip

/-!
# Native queries to the two words of a predicate count

The canonical root layout uses binary height and bit index, an empty path, and a unary depth
frontier. One clock serves every bit below the precision and both component/claim choices.
These are actual initial work-tape contents; constructing them is a separate charged phase.
The finishing adder can use this interface without reconstructing traversal invariants.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveCountingRoot

open MultiTapeTM Cslib.CountingLeaf Cslib.Circuits.Boolean.CarrySaveQuery

/-- One size budget for all root-component queries at the given count and precision. -/
@[expose] def sizeBudget (n w : ℕ) : ℕ := (Nat.clog 2 n).size + w.size + Nat.clog 2 n

/-- The root clock includes the complete traversal and its native leaf evaluation. -/
@[expose] def clock (c d : ℕ) (context : List Bool) (n w : ℕ) : ℕ :=
  40 * Nat.clog 2 n + 2 * (Nat.clog 2 n).size + 2 * w.size +
    CarrySaveLeaf.clock c d context (encNat n) (encNat w) (sizeBudget n w) + 1

/-- Binary counters and a unary depth frontier at their origins, with empty path and status. -/
@[expose] def initial (k : ℕ) (input context : List Bool) (n w bit : ℕ) :
    Cfg (k + 12) Bool Unit input :=
  CarrySaveLeaf.initial k input context (encNat n) (encNat w)
    (encNat (Nat.clog 2 n)) (encNat bit) [] (encUnary (Nat.clog 2 n)) 0 false

/-- One finite native family answers every component bit of the mathematical root pair.
The common clock is independent of the queried bit and of both Boolean selectors. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (carry claim : Bool),
      let cfg := (initial k input context n w bit.val).withState
        (some (atm carry claim).toPTM.toNTM.q₀)
      (atm carry claim).HaltsWithin (clock c d context n w) cfg ∧
        ((atm carry claim).AcceptsWithin (clock c d context n w) cfg ↔
          component (Counting.rootPair n w (fun j => predicate (context, j))) carry bit =
            claim) := by
  obtain ⟨k, S, hS, atm, c, d, h⟩ := CarrySaveCounting.exists_evaluator predicate hp
  refine ⟨k, S, hS, atm, c, d, ?_⟩
  intro input context n w bit carry claim
  have hb : bit.val.size ≤ w.size := Nat.size_le_size bit.isLt.le
  have hfront : CarrySaveStream.Frontier (encUnary (Nat.clog 2 n)) 0 (Nat.clog 2 n) := by
    intro j
    simp [encUnary_apply, tapeOfList, List.getElem?_replicate]
  have hval (m : ℕ) : Cslib.BitString.lsbValue (encNat m) = m := by
    exact Cslib.BitString.lsbValue_bits m
  have hlen (m : ℕ) : (encNat m).length = m.size := Nat.size_eq_bits_len m
  have hs : (encNat (Nat.clog 2 n)).length + (encNat bit.val).length +
      ([] : List Bool).length + Nat.clog 2 n ≤ sizeBudget n w := by
    simpa [sizeBudget, encNat_apply, ← Nat.size_eq_bits_len] using
      Nat.add_le_add_right (Nat.add_le_add_left hb (Nat.clog 2 n).size) (Nat.clog 2 n)
  obtain ⟨ht, ha⟩ := h input context (encNat n) (encNat w)
    (encNat (Nat.clog 2 n)) (encNat bit.val) [] (encUnary (Nat.clog 2 n))
    (Nat.clog 2 n) 0 false carry claim (sizeBudget n w) hfront hs (hval _)
    (by simp)
  have htime : CarrySaveStream.budget
      (CarrySaveLeaf.clock c d context (encNat n) (encNat w) (sizeBudget n w))
      (Nat.clog 2 n) (encNat (Nat.clog 2 n)) (encNat bit.val) ≤ clock c d context n w := by
    have hl := CarrySaveStream.budget_le
      (CarrySaveLeaf.clock c d context (encNat n) (encNat w) (sizeBudget n w))
      (Nat.clog 2 n) (encNat (Nat.clog 2 n)) (encNat bit.val)
    rw [hlen, hlen] at hl
    unfold clock
    omega
  dsimp only at ht ha ⊢
  refine ⟨ht.mono htime, ?_⟩
  unfold value CarrySaveCounting.leaves at ha
  generalize hw : ofBits (encNat w) = w' at ha
  rw [ofBits_encNat] at hw
  subst w'
  simp only [hval, ofBits_encNat, bit.isLt, dite_true] at ha
  have ha' : (atm carry claim).AcceptsWithin
      (CarrySaveStream.budget (CarrySaveLeaf.clock c d context (encNat n) (encNat w)
        (sizeBudget n w)) (Nat.clog 2 n) (encNat (Nat.clog 2 n)) (encNat bit.val))
      ((initial k input context n w bit.val).withState (some (atm carry claim).toPTM.toNTM.q₀)) ↔
      component (Counting.rootPair n w (fun j => predicate (context, j))) carry bit = claim := by
    simpa [initial, value, hval, Counting.rootPair, bit.isLt] using ha
  exact ⟨fun h => ha'.mp (h.of_halted_stepCoins ht), fun h => (ha'.mpr h).mono htime⟩

end Turing.MultiTapeATM.CarrySaveCountingRoot
