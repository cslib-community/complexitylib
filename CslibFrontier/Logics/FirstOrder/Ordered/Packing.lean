/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.BitArithmetic
public import CslibFrontier.Foundations.Data.Nat.Bitwise.Packing
import CslibFrontier.Tactic.FirstOrder
import Mathlib.Tactic.Linarith

/-!
# Native access to fixed tuples of packed words

The number of words is a syntactic constant. Addressing uses literal multiples and native PLUS;
it does not presuppose a multiplication relation. Decoding a field checks all bits, including
zeros above its width and zeros at unused addresses.

## Main definitions

* `Cslib.Logic.FO.Ordered.packedBit`: read a bit across a fixed tuple of words.
* `Cslib.Logic.FO.Ordered.packedField`: decode a bounded-width field.

## Main results

* `Cslib.Logic.FO.Ordered.realize_packedBit`: exact word-address semantics.
* `Cslib.Logic.FO.Ordered.realize_packedField`: exact natural-number field semantics.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 1.17(1)
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

variable (L : Language)

/-- Read a bit in a fixed tuple. Each scale is a syntactic literal, independent of the universe. -/
noncomputable def packedBit {α : Type*} {B : ℕ} (h : (language L).Term α)
    (w : Fin B → (language L).Term α) (a : (language L).Term α) : (language L).Formula α :=
  Formula.iSup fun r : Fin B => Formula.iExs (Fin 2)
    (scaleEq L r.val (h.relabel Sum.inl) (.var (.inr 0)) ⊓
     addEq L (.var (.inr 0)) (.var (.inr 1)) (a.relabel Sum.inl) ⊓
     (le L (h.relabel Sum.inl) (.var (.inr 1))).not ⊓
     bit L ((w r).relabel Sum.inl) (.var (.inr 1)))

/-- Decode exactly `s` bits starting at `a`, with all higher bits explicitly zero. -/
noncomputable def packedField {α : Type*} {B : ℕ} (h : (language L).Term α)
    (w : Fin B → (language L).Term α) (a s z : (language L).Term α) :
    (language L).Formula α := Formula.iAlls Unit
  ((bit L (z.relabel Sum.inl) (.var (.inr ()))).iff
    ((le L (s.relabel Sum.inl) (.var (.inr ()))).not ⊓ Formula.iExs Unit
      (addEq L (a.relabel (Sum.inl ∘ Sum.inl)) (.var (.inl (.inr ()))) (.var (.inr ())) ⊓
       packedBit L (h.relabel (Sum.inl ∘ Sum.inl))
         (fun r => (w r).relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ())))))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- `packedBit L h w a` holds exactly when position `a` falls in one of the `B` words `w`, of
width `h`, at a set bit. -/
@[simp, fo_realize]
theorem realize_packedBit {B : ℕ} (h : (language L).Term α)
    (w : Fin B → (language L).Term α) (a : (language L).Term α) (v : α → Fin n) :
    (packedBit L h w a).Realize v ↔ ∃ r : Fin B, ∃ b : Fin n,
      r.val * (h.realize v).val + b.val = (a.realize v).val ∧
        b.val < (h.realize v).val ∧ ((w r).realize v).val.testBit b.val = true := by
  fo_simp [packedBit, Function.comp_def, not_le, and_assoc]
  constructor
  · rintro ⟨r, u, h0, h1, h2, h3⟩
    exact ⟨r, u 1, by lia, h2, h3⟩
  · rintro ⟨r, b, ha, hb, hw⟩
    have ho : r.val * (h.realize v).val < n := by have := (a.realize v).isLt; lia
    exact ⟨r, ![⟨_, ho⟩, b], rfl, ha, hb, hw⟩

/-- When `B` words of width `h` fit in the universe, `packedField L h w a s z` holds exactly when
`z` is the field of `s` bits at position `a` (`BitString.readPackedField`). -/
@[fo_realize]
theorem realize_packedField {B : ℕ} (h : (language L).Term α)
    (w : Fin B → (language L).Term α) (a s z : (language L).Term α) (v : α → Fin n)
    (hspace : B * (h.realize v).val < n) :
    (packedField L h w a s z).Realize v ↔ (z.realize v).val =
      BitString.readPackedField (h.realize v).val (fun r => ((w r).realize v).val)
        (a.realize v).val (s.realize v).val := by
  fo_simp [packedField, Function.comp_def, not_le]
  constructor
  · intro hf
    apply Nat.eq_of_testBit_eq
    intro b
    apply Bool.eq_iff_iff.mpr
    rw [BitString.readPackedField_testBit]
    constructor
    · intro hz
      have hb : b < n := lt_trans
        (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.ge_two_pow_of_testBit hz)) (z.realize v).isLt
      obtain ⟨hbs, u, hu, r, t, ht, hth, hw⟩ := (hf (fun _ => ⟨b, hb⟩)).mp hz
      exact ⟨hbs, r, ⟨t.val, hth⟩, ht.trans hu.symm, hw⟩
    · rintro ⟨hbs, r, t, ht, hw⟩
      have hb : b < n := lt_trans hbs (s.realize v).isLt
      have ha : (a.realize v).val + b < n := by
        have hr := r.isLt
        have htt := t.isLt
        nlinarith
      apply (hf (fun _ => ⟨b, hb⟩)).mpr
      exact ⟨hbs, (fun _ => ⟨_, ha⟩), rfl, r,
        ⟨t.val, lt_trans t.isLt (h.realize v).isLt⟩, ht, t.isLt, hw⟩
  · intro hz b
    rw [hz, BitString.readPackedField_testBit]
    constructor
    · rintro ⟨hbs, r, t, ht, hw⟩
      have ha : (a.realize v).val + (b ()).val < n := by
        have hr := r.isLt
        have htt := t.isLt
        nlinarith
      exact ⟨hbs, (fun _ => ⟨_, ha⟩), rfl, r,
        ⟨t.val, lt_trans t.isLt (h.realize v).isLt⟩, ht, t.isLt, hw⟩
    · rintro ⟨hbs, u, hu, r, t, ht, hth, hw⟩
      exact ⟨hbs, r, ⟨t.val, hth⟩, ht.trans hu.symm, hw⟩

end Cslib.Logic.FO.Ordered
