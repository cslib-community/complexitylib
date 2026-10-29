/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Foundations.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# The existing binary subtraction word algorithm

The public borrow, digit-pair and subtraction definitions and laws are moved unchanged from the
higher arithmetic facade. No machine or computability predicate is needed for these identities.
The consuming-cursor realization has the same borrow rounds without repeated indexed lookup.

## Main definitions

* `BinarySub.borrow`, `BinarySub.subStep`: the existing schoolbook borrow round.
* `BinarySub.digitPairs`: the original indexed pairs of input digits.
* `BinarySub.cursorStep`: consume the remaining words and execute that same round.

## Main results

* `BinarySub.sub_eq`: the existing truncated-subtraction correctness law.
* `BinarySub.foldl_cursorStep`: equality of the consuming and indexed realizations.
* `BinarySub.cursorStep_lengths`: remaining words never grow; one output digit is added per round.
-/

@[expose] public section
namespace Turing.MultiTapeTM.BinarySub

/-- The borrow out of a digit position: the minuend digit `x` minus the subtrahend digit `y` and
the incoming borrow `c` is negative. -/
def borrow (c x y : Bool) : Bool := !x && (y || c) || y && c

/-- One round of schoolbook subtraction, least significant digit first: append the difference
digit and pass on the borrow. -/
def subStep (s : Bool × List Bool) (d : Bool × Bool) : Bool × List Bool :=
  (borrow s.1 d.1 d.2, s.2 ++ [s.1 ^^ d.1 ^^ d.2])

/-- The digit pairs of two binary naturals at their first `size a + size b` positions. -/
def digitPairs (p : ℕ × ℕ) : List (Bool × Bool) :=
  (List.range (p.1.bits.length + p.2.bits.length)).map fun i =>
    (p.1.bits.getD i false, p.2.bits.getD i false)

lemma bits_getD (n i : ℕ) : n.bits.getD i false = n.testBit i := by
  rw [Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
  rfl

lemma foldl_subStep (ps : List (Bool × Bool)) (c : Bool) (out : List Bool) :
    ∃ ds, (ps.foldl subStep (c, out)).2 = out ++ ds ∧ ds.length = ps.length ∧
      ds.foldr Nat.bit 0 + (ps.map Prod.snd).foldr Nat.bit 0 + c.toNat =
        (ps.map Prod.fst).foldr Nat.bit 0 +
          (ps.foldl subStep (c, out)).1.toNat * 2 ^ ps.length := by
  induction ps generalizing c out with
  | nil => exact ⟨[], by simp⟩
  | cons d ps ih =>
    obtain ⟨x, y⟩ := d
    obtain ⟨ds, hds, hlen, hval⟩ := ih (borrow c x y) (out ++ [c ^^ x ^^ y])
    refine ⟨(c ^^ x ^^ y) :: ds, ?_, ?_, ?_⟩
    · simpa [subStep] using hds
    · simpa using hlen
    · simp only [List.foldl_cons, subStep] at hval ⊢
      simp only [List.map_cons, List.foldr_cons, Nat.bit_val, List.length_cons, Nat.pow_succ]
      cases c <;> cases x <;> cases y <;>
        simp only [borrow, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
          Bool.or_true, Bool.or_false, Bool.true_xor, Bool.false_xor, Bool.toNat_true,
          Bool.toNat_false] at hval ⊢ <;> lia

/-- Truncated subtraction through the borrow of schoolbook subtraction: when the final borrow is
set the difference is negative, and otherwise the digits read off the difference. -/
lemma sub_eq (p : ℕ × ℕ) : p.1 - p.2 =
    if ((digitPairs p).foldl subStep (false, [])).1 then 0
    else ((digitPairs p).foldl subStep (false, [])).2.foldr Nat.bit 0 := by
  obtain ⟨ds, hds, hlen, hval⟩ := foldl_subStep (digitPairs p) false []
  have hfst : ((digitPairs p).map Prod.fst).foldr Nat.bit 0 = p.1 := by
    simp only [digitPairs, List.map_map, Function.comp_def, bits_getD]
    exact Nat.foldr_bit_testBit (by simp [Nat.size_eq_bits_len])
  have hsnd : ((digitPairs p).map Prod.snd).foldr Nat.bit 0 = p.2 := by
    simp only [digitPairs, List.map_map, Function.comp_def, bits_getD]
    exact Nat.foldr_bit_testBit (by simp [Nat.size_eq_bits_len])
  have hlt := Nat.foldr_bit_lt ds
  rw [hfst, hsnd, ← hlen] at hval
  rw [hds, List.nil_append]
  cases h : ((digitPairs p).foldl subStep (false, [])).1 <;>
    simp only [h, Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true, ↓reduceIte] at hval ⊢ <;>
    lia

/-- Realize one existing borrow round by consuming the two remaining input words. The clock
symbol is ignored; its word supplies the number of digit positions to visit. -/
def cursorStep (s : (List Bool × List Bool) × (Bool × List Bool)) (_ : Bool) :
    (List Bool × List Bool) × (Bool × List Bool) :=
  ((s.1.1.tail, s.1.2.tail), subStep s.2 (s.1.1.headD false, s.1.2.headD false))

/-- The consuming-word realization executes exactly the original indexed borrow fold. -/
lemma foldl_cursorStep (clock left right : List Bool) (acc : Bool × List Bool) :
    clock.foldl cursorStep ((left, right), acc) =
      ((left.drop clock.length, right.drop clock.length),
        ((List.range clock.length).map fun i =>
          (left.getD i false, right.getD i false)).foldl subStep acc) := by
  induction clock generalizing left right acc with
  | nil => simp
  | cons bit clock ih =>
    have hget (l : List Bool) (i : ℕ) : l.tail.getD i false = l.getD (i + 1) false := by
      cases l <;> simp
    have hzero (l : List Bool) : l.getD 0 false = l.headD false := by cases l <;> rfl
    simp only [List.foldl_cons, cursorStep, ih, List.length_cons, List.range_succ_eq_map,
      List.map_cons, hzero, List.map_map, Function.comp_def, List.foldl_cons]
    simp only [hget, List.drop_tail, Nat.succ_eq_add_one]

/-- No cursor grows, and the existing subtraction accumulator appends one digit per round. -/
lemma cursorStep_lengths (clock left right : List Bool) (acc : Bool × List Bool) :
    (clock.foldl cursorStep ((left, right), acc)).1.1.length ≤ left.length ∧
    (clock.foldl cursorStep ((left, right), acc)).1.2.length ≤ right.length ∧
    (clock.foldl cursorStep ((left, right), acc)).2.2.length = acc.2.length + clock.length := by
  rcases acc with ⟨c, out⟩
  rw [foldl_cursorStep]
  obtain ⟨ds, hds, hlen, _⟩ := foldl_subStep
    ((List.range clock.length).map fun i => (left.getD i false, right.getD i false)) c out
  simp only [List.length_map, List.length_range] at hlen
  simp only [hds, List.length_drop, List.length_append, hlen]
  exact ⟨Nat.sub_le _ _, Nat.sub_le _ _, trivial⟩

end Turing.MultiTapeTM.BinarySub
