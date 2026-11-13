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

/-- One bit-independent root clock for any supplied native leaf time. -/
@[expose] def clockOfLeaf (leafTime n w : ℕ) : ℕ :=
  40 * Nat.clog 2 n + 2 * (Nat.clog 2 n).size + 2 * w.size + leafTime + 1

/-- The root clock includes the complete traversal and its native leaf evaluation. -/
@[expose] def clock (c d : ℕ) (context : List Bool) (n w : ℕ) : ℕ :=
  clockOfLeaf (CarrySaveLeaf.clock c d context (encNat n) (encNat w) (sizeBudget n w)) n w

/-- Binary counters and a unary depth frontier at their origins, with empty path and status. -/
@[expose] def initial (k : ℕ) (input context : List Bool) (n w bit : ℕ) :
    Cfg (k + 12) Bool Unit input :=
  CarrySaveLeaf.initial k input context (encNat n) (encNat w)
    (encNat (Nat.clog 2 n)) (encNat bit) [] (encUnary (Nat.clog 2 n)) 0 false

/-- The canonical unary frontier represents precisely the remaining root depth. -/
theorem initial_frontier (n : ℕ) :
    CarrySaveStream.Frontier (encUnary (Nat.clog 2 n)) 0 (Nat.clog 2 n) := by
  intro j
  simp [encUnary_apply, tapeOfList, List.getElem?_replicate]

/-- Canonical height and any bounded bit index fit the shared root size budget. -/
theorem initial_size_le (n w : ℕ) (bit : Fin w) :
    (encNat (Nat.clog 2 n)).length + (encNat bit.val).length +
      ([] : List Bool).length + Nat.clog 2 n ≤ sizeBudget n w := by
  have hb := Nat.size_le_size bit.isLt.le
  simpa [sizeBudget, encNat_apply, ← Nat.size_eq_bits_len] using
    Nat.add_le_add_right (Nat.add_le_add_left hb (Nat.clog 2 n).size) (Nat.clog 2 n)

/-- The root clock bounds every bounded bit query, independent of the leaf implementation. -/
theorem budget_le_clockOfLeaf (leafTime n w : ℕ) (bit : Fin w) :
    CarrySaveStream.budget leafTime (Nat.clog 2 n) (encNat (Nat.clog 2 n)) (encNat bit.val) ≤
      clockOfLeaf leafTime n w := by
  have hl := CarrySaveStream.budget_le leafTime (Nat.clog 2 n)
    (encNat (Nat.clog 2 n)) (encNat bit.val)
  have hb := Nat.size_le_size bit.isLt.le
  have hlen (m : ℕ) : (encNat m).length = m.size := Nat.size_eq_bits_len m
  rw [hlen, hlen] at hl
  unfold clockOfLeaf
  omega

/-- The canonical streamed query denotes the requested component bit of the mathematical root. -/
theorem value_root (predicate : List Bool × ℕ → Bool) (context : List Bool)
    (n w : ℕ) (carry : Bool) (bit : Fin w) :
    value (CarrySaveCounting.leaves predicate context (encNat n) (encNat w))
      ⟨[], Nat.clog 2 n, carry, bit.val⟩ =
        component (Counting.rootPair n w (fun j => predicate (context, j))) carry bit := by
  unfold value CarrySaveCounting.leaves
  generalize hw : ofBits (encNat w) = w'
  rw [ofBits_encNat] at hw
  subst w'
  simp [bit.isLt, Counting.rootPair]

/-- A canonical stream specification yields the component-bit specification at the common root
clock. Halting makes acceptance stable under padding; the root query has its ordinary semantics. -/
theorem spec_of_stream {k : ℕ} {S : Type} {atm : MultiTapeATM (k + 12) Bool S}
    (predicate : List Bool × ℕ → Bool) (input context : List Bool) (n w : ℕ) (bit : Fin w)
    (carry claim : Bool) (leafTime : ℕ)
    (h : let cfg := (initial k input context n w bit.val).withState (some atm.toPTM.toNTM.q₀)
      let time := CarrySaveStream.budget leafTime (Nat.clog 2 n)
        (encNat (Nat.clog 2 n)) (encNat bit.val)
      atm.HaltsWithin time cfg ∧
        (atm.AcceptsWithin time cfg ↔
          value (CarrySaveCounting.leaves predicate context (encNat n) (encNat w))
            ⟨[], Nat.clog 2 n, carry, Cslib.BitString.lsbValue (encNat bit.val)⟩ = claim)) :
    let cfg := (initial k input context n w bit.val).withState (some atm.toPTM.toNTM.q₀)
    atm.HaltsWithin (clockOfLeaf leafTime n w) cfg ∧
      (atm.AcceptsWithin (clockOfLeaf leafTime n w) cfg ↔
        component (Counting.rootPair n w (fun j => predicate (context, j))) carry bit = claim) := by
  obtain ⟨ht, ha⟩ := h
  have htime := budget_le_clockOfLeaf leafTime n w bit
  refine ⟨ht.mono htime, ?_⟩
  have hval : Cslib.BitString.lsbValue (encNat bit.val) = bit.val :=
    Cslib.BitString.lsbValue_bits _
  rw [hval, value_root] at ha
  exact ⟨fun h => ha.mp (h.of_halted_stepCoins ht), fun h => (ha.mpr h).mono htime⟩

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
  apply spec_of_stream predicate input context n w bit carry claim
    (CarrySaveLeaf.clock c d context (encNat n) (encNat w) (sizeBudget n w))
  exact h input context (encNat n) (encNat w)
    (encNat (Nat.clog 2 n)) (encNat bit.val) [] (encUnary (Nat.clog 2 n))
    (Nat.clog 2 n) 0 false carry claim (sizeBudget n w) (initial_frontier n)
    (initial_size_le n w bit) (Cslib.BitString.lsbValue_bits _) (by simp)

end Turing.MultiTapeATM.CarrySaveCountingRoot
