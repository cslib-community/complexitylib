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

The encoding and the carry, borrow and normalization word folds are independent of resource
certificates. Their original definitions and arithmetic correctness proofs are retained here.
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

namespace NatPred

/-- Subtracts a borrow from the binary digits `l`, least significant first, keeping a leading
zero. -/
@[expose] public def decr : List Bool → List Bool
  | [] => []
  | true :: l => false :: l
  | false :: l => true :: decr l

/-- Drops a leading zero, the last digit. -/
@[expose] public def norm (l : List Bool) : List Bool :=
  if l.getLast? = some false then l.dropLast else l

lemma norm_cons {l : List Bool} (hl : l ≠ []) (b : Bool) : norm (b :: l) = b :: norm l := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hl)
  simp only [norm, List.getLast?_cons, hx, Option.getD_some, List.dropLast_cons_of_ne_nil hl]
  split_ifs <;> rfl

lemma bits_ne_nil {m : ℕ} (hm : m ≠ 0) : m.bits ≠ [] := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [Nat.bit0_bits k (by omega)]; simp
  · rw [Nat.bit1_bits]; simp

lemma decr_ne_nil {l : List Bool} (hl : l ≠ []) : decr l ≠ [] := by
  rcases l with _ | ⟨_ | _, l⟩ <;> simp_all [decr]

lemma norm_bits (n : ℕ) : norm n.bits = n.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m (by omega), norm_cons (bits_ne_nil (by omega)), ih m (by omega)]
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit1_bits, norm_cons (bits_ne_nil (by omega)), ih m (by omega)]

public lemma bits_pred (n : ℕ) : (n - 1).bits = norm (decr n.bits) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m (by omega), decr, show 2 * m - 1 = 2 * (m - 1) + 1 by omega,
          Nat.bit1_bits, ih m (by omega), norm_cons (decr_ne_nil (bits_ne_nil (by omega)))]
    · rw [Nat.bit1_bits, decr, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m (by omega), norm_cons (bits_ne_nil (by omega)), norm_bits]

/-- One round of the decrement: subtract the borrow from the digit `b`, append the result and keep
the borrow. -/
@[expose] public def decrStep (p : Bool × List Bool) (b : Bool) : Bool × List Bool :=
  (p.1 && !b, p.2 ++ [p.1 ^^ b])

lemma length_decr (l : List Bool) : (decr l).length = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [decr, ih]

lemma foldl_decrStep (l : List Bool) (c : Bool) (out : List Bool) :
    (l.foldl decrStep (c, out)).2 = out ++ if c then decr l else l := by
  induction l generalizing c out with
  | nil => cases c <;> simp [decr]
  | cons b l ih => cases c <;> cases b <;> simp [decrStep, ih, decr]

/-- One round of dropping a leading zero: append the pending digit and keep the new one. -/
@[expose] public def normStep (p : Option Bool × List Bool) (b : Bool) :
    Option Bool × List Bool :=
  (some b, p.2 ++ p.1.toList)

/-- Appends the pending digit unless it is a zero. -/
@[expose] public def normFinish (p : Option Bool × List Bool) : List Bool :=
  if p.1 = some true then p.2 ++ [true] else p.2

lemma length_foldl_normStep (l : List Bool) (p : Option Bool) (acc : List Bool) :
    (l.foldl normStep (p, acc)).2.length ≤ acc.length + p.toList.length + l.length := by
  induction l generalizing p acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, normStep]
    have := ih (some b) (acc ++ p.toList)
    simp only [Option.toList_some, List.length_append, List.length_cons, List.length_nil]
      at this ⊢
    omega

lemma normFinish_foldl (l : List Bool) (p : Option Bool) (acc : List Bool) :
    normFinish (l.foldl normStep (p, acc)) = acc ++ norm (p.toList ++ l) := by
  induction l generalizing p acc with
  | nil => rcases p with _ | _ | _ <;> simp [normFinish, norm]
  | cons b l ih =>
    rw [List.foldl_cons, normStep, ih]
    rcases p with _ | p
    · simp
    · simp [norm_cons]

end NatPred

end Turing.MultiTapeTM
