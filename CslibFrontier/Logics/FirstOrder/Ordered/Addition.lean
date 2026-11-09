/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Basic
import CslibFrontier.Foundations.Data.BitString.Propagation
import Mathlib.Data.Nat.Basic

/-!
# Canonical addition from order and BIT

A generate/propagate formula defines binary carry in the least-significant-bit-first convention.
Comparing all sum bits defines ordinary addition on every canonical universe `Fin n`, `n ≥ 2`.
The result is nonmodular: an out-of-range sum has no satisfying result in the universe.

This is the PLUS portion of the arithmetic-definability foundation. The Bit Sum Lemma is proved
in `Ordered.BitSum`; native TIMES and full-tuple BIT are constructed in
`Ordered.Multiplication` and `Ordered.TupleBit`. Numeric-preserving full-tuple composition is
supplied in `Ordered.FullTuple.Composition`.

## Main definitions

* `Cslib.Logic.FO.Ordered.carryFormula`: a carry generated below the given bit position.
* `Cslib.Logic.FO.Ordered.addition`: a single native formula for exact canonical addition.

## Main results

* `Cslib.Logic.FO.Ordered.realize_addition`: the formula means natural-number addition.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Proposition 1.9 and the PLUS part of
  Theorem 1.17(1). Canonical BIT indexes from the least significant end, reversing the string
  orientation used in Proposition 1.9.
* Reuses Lean's `BitVec.carry_succ` and `BitVec.getLsbD_add`, and the library's source/link
  propagation characterization.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

private theorem carry_eq_propagate {w : ℕ} (x y : BitVec w) (i : ℕ) :
    BitVec.carry i x y false = BitString.propagate
      (fun j => x.getLsbD j && y.getLsbD j) (fun j => x.getLsbD j || y.getLsbD j) i := by
  induction i with
  | zero => simp [BitString.propagate]
  | succ i ih =>
    rw [BitVec.carry_succ, BitString.propagate, ← ih]
    cases x.getLsbD i <;> cases y.getLsbD i <;> cases BitVec.carry i x y false <;> rfl

private theorem carry_eq_true_iff {w : ℕ} (x y : BitVec w) (i : ℕ) :
    BitVec.carry i x y false = true ↔ ∃ j, j < i ∧ x.getLsbD j = true ∧
      y.getLsbD j = true ∧ ∀ k, j < k → k < i → x.getLsbD k = true ∨ y.getLsbD k = true := by
  rw [carry_eq_propagate, BitString.propagate_eq_true_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, and_assoc]

/-- A lower bit generates a carry and every intervening bit propagates it. The two quantifiers
range over positions in the canonical universe, with bit zero least significant. -/
noncomputable def carryFormula (L : Language) {α : Type*}
    (x y i : (language L).Term α) : (language L).Formula α :=
  Formula.iExs Unit (
    (le L (i.relabel Sum.inl) (.var (.inr ()))).not ⊓
    bit L (x.relabel Sum.inl) (.var (.inr ())) ⊓
    bit L (y.relabel Sum.inl) (.var (.inr ())) ⊓
    Formula.iAlls Unit (
      ((le L (.var (.inr ())) (.var (.inl (.inr ())))).not ⊓
        (le L (i.relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ()))).not).imp
      (bit L (x.relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ())) ⊔
        bit L (y.relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ())))))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

private theorem realize_carryFormula (x y i : (language L).Term α) (v : α → Fin n) :
    (carryFormula L x y i).Realize v ↔
      ∃ j : Fin n, j < i.realize v ∧ (x.realize v).val.testBit j.val = true ∧
        (y.realize v).val.testBit j.val = true ∧ ∀ k : Fin n, j < k → k < i.realize v →
          (x.realize v).val.testBit k.val = true ∨ (y.realize v).val.testBit k.val = true := by
  simp only [carryFormula, Formula.realize_iExs, Formula.realize_inf, Formula.realize_not,
    realize_le, realize_bit, Term.realize_var, Term.realize_relabel, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_sup,
    not_le, and_imp, and_assoc]
  constructor
  · rintro ⟨j, hj, hx, hy, h⟩
    exact ⟨j (), hj, hx, hy, fun k => h (fun _ => k)⟩
  · rintro ⟨j, hj, hx, hy, h⟩
    exact ⟨fun _ => j, hj, hx, hy, fun k => h (k ())⟩

private def word {n : ℕ} (a : Fin n) : BitVec n :=
  BitVec.ofNatLT a.val (lt_trans a.isLt Nat.lt_two_pow_self)

private theorem realize_carryFormula_word (x y i : (language L).Term α) (v : α → Fin n) :
    (carryFormula L x y i).Realize v ↔
      BitVec.carry (i.realize v).val (word (x.realize v)) (word (y.realize v)) false = true := by
  rw [realize_carryFormula, carry_eq_true_iff]
  simp only [word, BitVec.getLsbD_ofNatLT]
  constructor
  · rintro ⟨j, hj, hx, hy, h⟩
    exact ⟨j.val, hj, hx, hy, fun k hk hki =>
      h ⟨k, lt_trans hki (i.realize v).isLt⟩ hk hki⟩
  · rintro ⟨j, hj, hx, hy, h⟩
    exact ⟨⟨j, lt_trans hj (i.realize v).isLt⟩, hj, hx, hy, fun k hk hki =>
      h k.val hk hki⟩

/-- Exact addition, expressed by comparing the result bits with input bits and generated carries.
The formula is independent of the universe size and uses only native order, BIT and quantifiers. -/
noncomputable def addition (L : Language) : (language L).Formula (Fin 3) :=
  let x := bit L (.var (.inl 0)) (.var (.inr ()))
  let y := bit L (.var (.inl 1)) (.var (.inr ()))
  let z := bit L (.var (.inl 2)) (.var (.inr ()))
  let c := carryFormula L (.var (.inl 0)) (.var (.inl 1)) (.var (.inr ()))
  -- Two nested equivalences express the parity of three input bits.
  Formula.iAlls Unit (z.iff (x.iff (y.iff c)))

private theorem iff_iff_eq_xor (a b c d : Bool) :
    (c = true ↔ (a = true ↔ (b = true ↔ d = true))) ↔ c = (a ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem word_getLsbD {n : ℕ} (a : Fin n) (i : ℕ) :
    (word a).getLsbD i = a.val.testBit i := BitVec.getLsbD_ofNatLT _ _ _

private theorem realize_addition_word (v : Fin 3 → Fin n) :
    (addition L).Realize v ↔ word (v 2) = word (v 0) + word (v 1) := by
  rw [addition, Formula.realize_iAlls, BitVec.eq_of_getLsbD_eq_iff]
  simp only [Formula.realize_iff, realize_bit, realize_carryFormula_word,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr, iff_iff_eq_xor]
  constructor
  · intro h i hi
    rw [BitVec.getLsbD_add hi, word_getLsbD, word_getLsbD, word_getLsbD]
    exact h (fun _ => ⟨i, hi⟩)
  · intro h i
    have hh := h (i ()).val (i ()).isLt
    rw [BitVec.getLsbD_add (i ()).isLt, word_getLsbD, word_getLsbD, word_getLsbD] at hh
    exact hh

/-- The formula defines ordinary natural-number addition, including out-of-range rejection. -/
theorem realize_addition (v : Fin 3 → Fin n) :
    (addition L).Realize v ↔ (v 0).val + (v 1).val = (v 2).val := by
  rw [realize_addition_word]
  have hbound : (word (v 0)).toNat + (word (v 1)).toNat < 2 ^ n := by
    have := Nat.mul_le_pow (by decide : 2 ≠ 1) n
    have := (v 0).isLt
    have := (v 1).isLt
    simp only [word, BitVec.toNat_ofNatLT]
    lia
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    rw [BitVec.toNat_add_of_lt hbound] at hh
    exact hh.symm
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add_of_lt hbound]
    exact h.symm

/-- No element of the universe can represent an out-of-range sum. -/
theorem not_realize_addition_of_le (v : Fin 3 → Fin n)
    (h : n ≤ (v 0).val + (v 1).val) : ¬(addition L).Realize v := by
  rw [realize_addition]
  have := (v 2).isLt
  lia

end Cslib.Logic.FO.Ordered
