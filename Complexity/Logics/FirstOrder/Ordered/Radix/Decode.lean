/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Radix.Arithmetic

/-!
# Native radix decoding

A source element is decoded by exact scalar quotient equations, with its final quotient
required to be zero. Every intermediate scalar is at most the original element, so decoding
works even when the universe size is not a power of two.

## Main definitions

* `Cslib.Logic.FO.Ordered.Radix.quotientEq`, `Cslib.Logic.FO.Ordered.Radix.decode`: one scalar
  quotient equation and decoding a source element into a fixed-length word.

## Main results

* `Cslib.Logic.FO.Ordered.Radix.realize_decode`: exact bounded-digit semantics.
* `Cslib.Logic.FO.Ordered.Radix.exists_word`: every value below the word capacity has witnesses.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Exercise 1.33(3): the full-tuple
  application.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered.Radix

open FirstOrder Language Structure

/-- The exact quotient equation `x = r + B*q`; a remainder bound is supplied separately. -/
noncomputable def quotientEq (L : Language) {α : Type*}
    (B x q r : (language L).Term α) : (language L).Formula α :=
  Formula.iExs Unit
    (mulEq L (B.relabel Sum.inl) (q.relabel Sum.inl) (.var (.inr ())) ⊓
     addEq L (r.relabel Sum.inl) (.var (.inr ())) (x.relabel Sum.inl))

/-- Decode a scalar by exact quotient equations, including a zero final quotient. -/
noncomputable def decode (L : Language) {α : Type*} {d : ℕ}
    (B x : (language L).Term α) (w : Fin d → (language L).Term α) :
    (language L).Formula α := digits L B w ⊓ Formula.iExs (Fin (d + 1))
  ((Term.var (.inr 0)).equal (x.relabel Sum.inl) ⊓
   (Term.var (.inr (Fin.last d))).equal (zero L) ⊓
   Formula.iInf fun i : Fin d =>
     quotientEq L (B.relabel Sum.inl) (.var (.inr i.castSucc)) (.var (.inr i.succ))
       ((w i).relabel Sum.inl))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- `quotientEq L B x q r` holds iff `x = r + B * q`. -/
@[fo_realize]
theorem realize_quotientEq (B x q r : (language L).Term α) (v : α → Fin n) :
    (quotientEq L B x q r).Realize v ↔
      (x.realize v).val = (r.realize v).val + (B.realize v).val * (q.realize v).val := by
  simp only [quotientEq, Formula.realize_iExs, Formula.realize_inf, realize_mulEq, realize_addEq,
    Term.realize_relabel, Term.realize_var, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨u, hu, he⟩
    lia
  · intro he
    have ht : (B.realize v).val * (q.realize v).val < n := by
      have := (x.realize v).isLt
      lia
    exact ⟨fun _ => ⟨_, ht⟩, rfl, he.symm⟩

/-- When `1 ≤ B`, `decode L B x w` holds exactly when `w` is a radix-`B` word with the value of
`x`. -/
@[fo_realize]
theorem realize_decode {d : ℕ} (B x : (language L).Term α)
    (w : Fin d → (language L).Term α) (v : α → Fin n) (hB : 1 ≤ (B.realize v).val) :
    (decode L B x w).Realize v ↔
      (∀ i, ((w i).realize v).val < (B.realize v).val) ∧
      Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((w i).realize v).val) =
        (x.realize v).val := by
  simp only [decode, Formula.realize_inf, realize_digits, Formula.realize_iExs,
    Formula.realize_equal, Formula.realize_iInf, realize_quotientEq, Term.realize_var,
    Term.realize_relabel, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    Fin.ext_iff, realize_zero_val, and_assoc]
  constructor
  · rintro ⟨hw, q, hq0, hqe, hs⟩
    exact ⟨hw, (Nat.ofDigits_eq_of_quotients _ (fun i => (q i).val) hqe hs).trans hq0⟩
  · rintro ⟨hw, he⟩
    obtain ⟨q, hq0, hqe, hqb, hs⟩ := Nat.exists_radix_quotients hB
      (fun i => ((w i).realize v).val)
    rw [he] at hq0 hqb
    exact ⟨hw, (fun i => ⟨q i, lt_of_le_of_lt (hqb i) (x.realize v).isLt⟩), hq0, hqe, hs⟩

omit [Fact (2 ≤ n)] in
/-- Digit witnesses fit in the source universe even when the represented word does not. -/
theorem exists_word {d : ℕ} (B : Fin n) {z : ℕ} (hz : z < B.val ^ d) :
    ∃ w : Fin d → Fin n, (∀ i, (w i).val < B.val) ∧
      Nat.ofDigits B.val (List.ofFn fun i => (w i).val) = z := by
  obtain ⟨w, hw, he⟩ := Nat.exists_ofDigits_ofFn hz
  exact ⟨(fun i => ⟨w i, lt_trans (hw i) B.isLt⟩), hw, he⟩

end Cslib.Logic.FO.Ordered.Radix
