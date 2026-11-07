/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: subset of crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# Binary natural encoding and carry increment

This module defines the little-endian binary encoding `Turing.MultiTapeTM.encNat` of natural
numbers (`Nat.bits`) and the carry-propagation step `Turing.MultiTapeTM.NatSucc.incr` for
binary successor, independent of machine resource certificates.

## Main definitions

* `Turing.MultiTapeTM.encNat`: natural numbers encoded by their binary digits, least significant
  first.
* `Turing.MultiTapeTM.NatSucc.incr`: adds an incoming carry bit to a little-endian binary word.

## Main statements

* `Turing.MultiTapeTM.encNat_apply`: unfolding `encNat n` to `n.bits`.
* `Turing.MultiTapeTM.NatSucc.bits_succ`: `(n + 1).bits = incr true n.bits`.
-/

public section

namespace Turing.MultiTapeTM

/-- Natural numbers encoded by their binary digits, least significant first. -/
@[expose] public def encNat : ℕ ↪ List Bool :=
  ⟨Nat.bits, fun m n h => Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_eq_inth, h]⟩

/-- `encNat n` is the little-endian binary digit list `n.bits`. -/
@[simp]
public lemma encNat_apply (n : ℕ) : encNat n = n.bits := rfl

namespace NatSucc

/-- Adds the carry `c` to the binary digits `l`, least significant first. -/
@[expose] public def incr : Bool → List Bool → List Bool
  | false, l => l
  | true, [] => [true]
  | true, false :: l => true :: l
  | true, true :: l => false :: incr true l

/-- The binary digits of `n + 1` are obtained by incrementing `n.bits` with carry `true`. -/
public lemma bits_succ (n : ℕ) : (n + 1).bits = incr true n.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit1_bits, Nat.bit0_bits m (by omega), incr]
    · rw [Nat.bit1_bits, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.bit0_bits _ (by omega),
        ih m (by omega), incr]

end NatSucc

end Turing.MultiTapeTM
