/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.BitSum
public import Complexity.Foundations.Data.Nat.Bitwise.Multiplication

/-!
# Native multiplication columns

The contributing rows of column `j` are encoded by the bits `x[t] ∧ y[j-t]`. This word is
always at most `x`, so it fits in every canonical universe containing `x`, not only universes
whose size is a power of two. Native Bit Sum counts the rows, and PLUS checks the exact carry
equation without modular overflow.

## Main definitions

* `Cslib.Logic.FO.Ordered.Multiplication.columnWord`: the bitwise column formula.
* `Cslib.Logic.FO.Ordered.Multiplication.columnCount`: the exact column count.
* `Cslib.Logic.FO.Ordered.Multiplication.carryStep`: one nonmodular carry equation.

## Main results

* `Cslib.Logic.FO.Ordered.Multiplication.realize_columnCount`: exact column-count semantics.
* `Cslib.Logic.FO.Ordered.Multiplication.realize_carryStep`: exact bounded carry semantics.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 1.17(1) and Lemma 1.18.
  The Bit Sum Lemma is due to Barrington, Immerman and Straubing
  [BarringtonImmermanStraubing1990]. The carry equation is a variant of the source's short sums.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered.Multiplication

open FirstOrder Language Structure

variable (L : Language)

/-- A word marking the input bits contributing to one multiplication column. -/
noncomputable def columnWord {α : Type*} (x y j w : (language L).Term α) :
    (language L).Formula α := Formula.iAlls Unit
  ((bit L (w.relabel Sum.inl) (.var (.inr ()))).iff
    (bit L (x.relabel Sum.inl) (.var (.inr ())) ⊓ Formula.iExs Unit
      (addEq L (.var (.inl (.inr ()))) (.var (.inr ())) (j.relabel (Sum.inl ∘ Sum.inl)) ⊓
       bit L (y.relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ())))))

/-- Native Bit Sum counts the contributing rows of a column. -/
noncomputable def columnCount {α : Type*} (x y j a : (language L).Term α) :
    (language L).Formula α := Formula.iExs Unit
  (columnWord L (x.relabel Sum.inl) (y.relabel Sum.inl) (j.relabel Sum.inl) (.var (.inr ())) ⊓
    (bitSum L).subst ![.var (.inr ()), a.relabel Sum.inl])

/-- One exact carry equation. All addition and doubling witnesses must fit in the universe. -/
noncomputable def carryStep {α : Type*} (x y z i c c' : (language L).Term α) :
    (language L).Formula α := Formula.iExs (Fin 3)
  (columnCount L (x.relabel Sum.inl) (y.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0)) ⊓
   addEq L (c.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) ⊓
   scaleEq L 2 (c'.relabel Sum.inl) (.var (.inr 2)) ⊓
   ((bit L (z.relabel Sum.inl) (i.relabel Sum.inl) ⊓
       addEq L (one L) (.var (.inr 2)) (.var (.inr 1))) ⊔
    ((bit L (z.relabel Sum.inl) (i.relabel Sum.inl)).not ⊓
       (Term.var (.inr 1)).equal (.var (.inr 2)))))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- `columnWord L x y j w` holds iff `w` is the bit mask `BitString.mulColumnWord` of rows
contributing to column `j` of the product of `x` and `y`. -/
@[simp, fo_realize]
theorem realize_columnWord (x y j w : (language L).Term α) (v : α → Fin n) :
    (columnWord L x y j w).Realize v ↔ (w.realize v).val =
      BitString.mulColumnWord (x.realize v).val (y.realize v).val (j.realize v).val := by
  simp only [columnWord, Formula.realize_iAlls, Formula.realize_iff, Formula.realize_inf,
    Formula.realize_iExs, realize_bit, realize_addEq, Term.realize_var, Term.realize_relabel,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro hf
    apply Nat.eq_of_testBit_eq
    intro b
    apply Bool.eq_iff_iff.mpr
    rw [BitString.mulColumnWord_testBit]
    constructor
    · intro hb
      have hbn : b < n := lt_trans
        (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.ge_two_pow_of_testBit hb)) (w.realize v).isLt
      obtain ⟨hx, u, hu, hy⟩ := (hf (fun _ => ⟨b, hbn⟩)).mp hb
      exact ⟨hx, by lia, by simpa only [show (j.realize v).val - b = (u ()).val by lia] using hy⟩
    · rintro ⟨hx, hb, hy⟩
      have hbn : b < n := lt_of_le_of_lt hb (j.realize v).isLt
      have hd : (j.realize v).val - b < n :=
        lt_of_le_of_lt (Nat.sub_le _ _) (j.realize v).isLt
      exact (hf (fun _ => ⟨b, hbn⟩)).mpr ⟨hx, (fun _ => ⟨_, hd⟩), by dsimp; lia, hy⟩
  · intro hw b
    rw [hw, BitString.mulColumnWord_testBit]
    constructor
    · rintro ⟨hx, hb, hy⟩
      have hd : (j.realize v).val - (b ()).val < n :=
        lt_of_le_of_lt (Nat.sub_le _ _) (j.realize v).isLt
      exact ⟨hx, (fun _ => ⟨_, hd⟩), by dsimp; lia, hy⟩
    · rintro ⟨hx, u, hu, hy⟩
      exact ⟨hx, by lia,
        by simpa only [show (j.realize v).val - (b ()).val = (u ()).val by lia] using hy⟩

private theorem realize_subst_bitSum {β : Type*} (x y : (language L).Term β) (v : β → Fin n) :
    Formula.Realize ((bitSum L).subst ![x, y]) v ↔
      (y.realize v).val = (x.realize v).val.bitIndices.length := by
  change ((bitSum L).subst ![x, y]).Realize v _ ↔ _
  rw [BoundedFormula.realize_subst]
  exact realize_bitSum _

/-- `columnCount L x y j a` holds exactly when `a` is the number of rows contributing to column
`j` of the product of `x` and `y` (`BitString.mulColumn`). -/
@[simp, fo_realize]
theorem realize_columnCount (x y j a : (language L).Term α) (v : α → Fin n) :
    (columnCount L x y j a).Realize v ↔ (a.realize v).val =
      BitString.mulColumn (x.realize v).val (y.realize v).val (j.realize v).val := by
  simp only [columnCount, Formula.realize_iExs, Formula.realize_inf, realize_columnWord,
    realize_subst_bitSum, Term.realize_var, Term.realize_relabel,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨u, hu, ha⟩
    simpa only [hu, BitString.mulColumn] using ha
  · intro ha
    have hw := lt_of_le_of_lt (BitString.mulColumnWord_le (x.realize v).val
      (y.realize v).val (j.realize v).val) (x.realize v).isLt
    exact ⟨(fun _ => ⟨_, hw⟩), rfl, ha⟩

/-- `carryStep L x y z i c c'` holds exactly when the carry `c` into column `i` plus its column
count is bit `i` of `z` plus twice the outgoing carry `c'`, and that sum fits in the universe. -/
@[fo_realize]
theorem realize_carryStep (x y z i c c' : (language L).Term α) (v : α → Fin n) :
    (carryStep L x y z i c c').Realize v ↔
      (c.realize v).val +
          BitString.mulColumn (x.realize v).val (y.realize v).val (i.realize v).val =
        ((z.realize v).val.testBit (i.realize v).val).toNat + 2 * (c'.realize v).val ∧
      (c.realize v).val +
        BitString.mulColumn (x.realize v).val (y.realize v).val (i.realize v).val < n := by
  simp only [carryStep, Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup,
    Formula.realize_not, realize_columnCount, realize_addEq, realize_scaleEq, realize_bit,
    Formula.realize_equal, Term.realize_var, Term.realize_relabel, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, realize_one_val, and_assoc, Fin.ext_iff]
  constructor
  · rintro ⟨u, ha, hc, hd, hs⟩
    have hn := (u 1).isLt
    rcases hs with ⟨hb, he⟩ | ⟨hb, he⟩
    · rw [hb]
      simp only [Bool.toNat_true]
      lia
    · have hb' := Bool.eq_false_iff.mpr hb
      rw [hb']
      simp only [Bool.toNat_false]
      lia
  · rintro ⟨he, hn⟩
    have ha : BitString.mulColumn (x.realize v).val (y.realize v).val
        (i.realize v).val < n := by lia
    have hd : 2 * (c'.realize v).val < n := by lia
    refine ⟨![⟨_, ha⟩, ⟨_, hn⟩, ⟨_, hd⟩], rfl, rfl, rfl, ?_⟩
    cases hb : (z.realize v).val.testBit (i.realize v).val with
    | false => exact Or.inr ⟨by decide, by simpa [hb] using he⟩
    | true => exact Or.inl ⟨rfl, by simpa [hb] using he.symm⟩

end Cslib.Logic.FO.Ordered.Multiplication
