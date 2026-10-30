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
# Binary natural encoding and digit algorithms

The encoding and the carry word folds are independent of resource certificates. Their
definitions and arithmetic correctness proofs are retained here.
-/

public section

namespace Turing.MultiTapeTM

/-- Natural numbers encoded by their binary digits, least significant first. -/
@[expose] public def encNat : ℕ ↪ List Bool :=
  ⟨Nat.bits, fun m n h => Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_eq_inth, h]⟩

@[simp]
public lemma encNat_apply (n : ℕ) : encNat n = n.bits := rfl

namespace NatSucc

/-- Adds the carry `c` to the binary digits `l`, least significant first. -/
@[expose] public def incr : Bool → List Bool → List Bool
  | false, l => l
  | true, [] => [true]
  | true, false :: l => true :: l
  | true, true :: l => false :: incr true l

public lemma bits_succ (n : ℕ) : (n + 1).bits = incr true n.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit1_bits, Nat.bit0_bits m (by omega), incr]
    · rw [Nat.bit1_bits, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Nat.bit0_bits _ (by omega),
        ih m (by omega), incr]

/-- One round: add the carry to the digit `b`, append the resulting digit and keep the carry. -/
@[expose] public def succStep (p : Bool × List Bool) (b : Bool) : Bool × List Bool :=
  (p.1 && b, p.2 ++ [p.1 ^^ b])

/-- Appends the final carry digit. -/
@[expose] public def succFinish (p : Bool × List Bool) : List Bool :=
  if p.1 then p.2 ++ [true] else p.2

public lemma succFinish_foldl (l : List Bool) (c : Bool) (out : List Bool) :
    succFinish (l.foldl succStep (c, out)) = out ++ incr c l := by
  induction l generalizing c out with
  | nil => cases c <;> simp [succFinish, incr]
  | cons b l ih => cases c <;> cases b <;> simp [succStep, ih, incr]

lemma bits_succ_eq_foldl (n : ℕ) :
    (n + 1).bits = succFinish (n.bits.foldl succStep (true, [])) := by
  rw [succFinish_foldl, bits_succ, List.nil_append]

public lemma length_foldl_succStep (l : List Bool) (p : Bool × List Bool) :
    (l.foldl succStep p).2.length = p.2.length + l.length := by
  induction l generalizing p <;> simp [*, succStep]; omega

/-- The encoding of the accumulator: the carry and the digits so far. -/
public abbrev encAcc : Bool × List Bool ↪ List Bool := encPair encBool encBits

public lemma length_encAcc (p : Bool × List Bool) : (encAcc p).length = p.2.length + 3 := by
  simp

end NatSucc

end Turing.MultiTapeTM
