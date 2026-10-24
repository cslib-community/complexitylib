/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Addition
import Complexity.Tactic.FirstOrder

/-!
# Native numeral and shift formulas

Exact binary shifts are definable from BIT and the native addition formula. A separate
no-lost-bit condition rejects overflow; matching only the visible output bits would instead
define a truncated shift. Numeral formulas work even when their numeral is outside the universe:
they then have no satisfying value.

## Main definitions

* `Cslib.Logic.FO.Ordered.addEq`: native addition applied to arbitrary terms.
* `Cslib.Logic.FO.Ordered.natEq`: equality to a fixed natural numeral.
* `Cslib.Logic.FO.Ordered.scaleEq`: multiplication by a fixed syntactic literal.
* `Cslib.Logic.FO.Ordered.powerOfTwo`: a numeral containing exactly the specified bit.
* `Cslib.Logic.FO.Ordered.highestBit`: the largest set-bit position of a nonzero numeral.
* `Cslib.Logic.FO.Ordered.shiftLeft`: exact multiplication by a power of two.

## Main results

* `Cslib.Logic.FO.Ordered.realize_natEq`: exact numeral semantics.
* `Cslib.Logic.FO.Ordered.realize_powerOfTwo`: exact power-of-two semantics.
* `Cslib.Logic.FO.Ordered.realize_shiftLeft`: exact, nonmodular shift semantics.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 1.2.1.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

variable (L : Language)

/-- Apply the native PLUS formula to three terms. -/
noncomputable def addEq {α : Type*} (x y z : (language L).Term α) :
    (language L).Formula α := (addition L).subst ![x, y, z]

/-- Equality to a fixed natural numeral, without requiring that numeral to exist. -/
noncomputable def natEq : ℕ → {α : Type*} → (language L).Term α → (language L).Formula α
  | 0, _, x => x.equal (zero L)
  | k + 1, _, x => Formula.iExs Unit
      (natEq k (.var (.inr ())) ⊓ addEq L (.var (.inr ())) (one L) (x.relabel Sum.inl))

/-- Multiplication by a fixed literal, expanded as a fixed chain of additions. -/
noncomputable def scaleEq : ℕ → {α : Type*} →
    (language L).Term α → (language L).Term α → (language L).Formula α
  | 0, _, _, z => z.equal (zero L)
  | k + 1, _, x, z => Formula.iExs Unit
      (scaleEq k (x.relabel Sum.inl) (.var (.inr ())) ⊓
        addEq L (.var (.inr ())) (x.relabel Sum.inl) (z.relabel Sum.inl))

/-- Exactly one set bit, at the specified exponent. -/
noncomputable def powerOfTwo {α : Type*} (p e : (language L).Term α) :
    (language L).Formula α := Formula.iAlls Unit
  ((bit L (p.relabel Sum.inl) (.var (.inr ()))).iff
    ((e.relabel Sum.inl).equal (.var (.inr ()))))

/-- The highest set bit of a nonzero numeral. -/
noncomputable def highestBit {α : Type*} (x h : (language L).Term α) :
    (language L).Formula α := bit L x h ⊓ Formula.iAlls Unit
  ((bit L (x.relabel Sum.inl) (.var (.inr ()))).imp
    (le L (.var (.inr ())) (h.relabel Sum.inl)))

/-- Exact left shift, with every source set bit required to remain representable. -/
noncomputable def shiftLeft {α : Type*} (x e z : (language L).Term α) :
    (language L).Formula α :=
  Formula.iAlls Unit
    ((bit L (z.relabel Sum.inl) (.var (.inr ()))).iff
      (Formula.iExs Unit
        (addEq L (.var (.inr ())) (e.relabel (Sum.inl ∘ Sum.inl))
          (.var (.inl (.inr ()))) ⊓
         bit L (x.relabel (Sum.inl ∘ Sum.inl)) (.var (.inr ()))))) ⊓
  Formula.iAlls Unit
    ((bit L (x.relabel Sum.inl) (.var (.inr ()))).imp
      (Formula.iExs Unit
        (addEq L (.var (.inl (.inr ()))) (e.relabel (Sum.inl ∘ Sum.inl))
          (.var (.inr ())))))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- `addEq L x y z` holds under `v` if and only if
`(x.realize v).val + (y.realize v).val = (z.realize v).val`. -/
@[simp, fo_realize]
theorem realize_addEq (x y z : (language L).Term α) (v : α → Fin n) :
    (addEq L x y z).Realize v ↔ (x.realize v).val + (y.realize v).val = (z.realize v).val := by
  change ((addition L).subst ![x, y, z]).Realize v _ ↔ _
  rw [BoundedFormula.realize_subst]
  exact realize_addition _

/-- `natEq L k x` holds exactly when `x` denotes `k`. -/
@[simp, fo_realize]
theorem realize_natEq (k : ℕ) (x : (language L).Term α) (v : α → Fin n) :
    (natEq L k x).Realize v ↔ (x.realize v).val = k := by
  induction k generalizing α with
  | zero =>
    simp only [natEq, Formula.realize_equal, ← Fin.val_inj, realize_zero_val]
  | succ k ih =>
    fo_simp [natEq, ih, realize_one_val, Function.comp_def]
    exact ⟨fun ⟨a, ha, he⟩ => by lia,
      fun hx => ⟨fun _ => ⟨k, by have := (x.realize v).isLt; lia⟩, rfl, hx.symm⟩⟩

/-- `scaleEq L k x z` holds under `v` iff `k * (x.realize v).val = (z.realize v).val`. -/
@[simp, fo_realize]
theorem realize_scaleEq (k : ℕ) (x z : (language L).Term α) (v : α → Fin n) :
    (scaleEq L k x z).Realize v ↔ k * (x.realize v).val = (z.realize v).val := by
  induction k generalizing α with
  | zero => simp [scaleEq, ← Fin.val_inj, eq_comm]
  | succ k ih =>
    fo_simp [scaleEq, ih, Function.comp_def]
    refine ⟨fun ⟨a, ha, he⟩ => by rw [Nat.succ_mul]; lia, fun hz => ?_⟩
    exact ⟨fun _ => ⟨k * (x.realize v).val,
      by have := (z.realize v).isLt; rw [Nat.succ_mul] at hz; lia⟩,
      rfl, by simpa only [Nat.succ_mul] using hz⟩

omit [Fact (2 ≤ n)] in
private theorem bitIndex_lt {x : Fin n} {i : ℕ} (hi : x.val.testBit i = true) : i < n :=
  lt_trans (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.ge_two_pow_of_testBit hi)) x.isLt

/-- `highestBit L x h` holds under `v` iff `2 ^ (h.realize v).val ≤ (x.realize v).val` and
`(x.realize v).val < 2 ^ ((h.realize v).val + 1)`. -/
@[simp, fo_realize]
theorem realize_highestBit (x h : (language L).Term α) (v : α → Fin n) :
    (highestBit L x h).Realize v ↔
      2 ^ (h.realize v).val ≤ (x.realize v).val ∧
        (x.realize v).val < 2 ^ ((h.realize v).val + 1) := by
  fo_simp [highestBit, Function.comp_def]
  constructor
  · rintro ⟨hx, ht⟩
    refine ⟨Nat.ge_two_pow_of_testBit hx, Nat.lt_pow_two_of_testBit _ ?_⟩
    intro i hi
    apply Bool.eq_false_iff.mpr
    intro hb
    have hh := ht (fun _ => ⟨i, bitIndex_lt hb⟩) hb
    change i ≤ (h.realize v).val at hh
    lia
  · rintro ⟨hx, ht⟩
    refine ⟨Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hx ht, fun i hi => ?_⟩
    have hp := Nat.ge_two_pow_of_testBit hi
    have hh := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (lt_of_le_of_lt hp ht)
    change (i ()).val ≤ (h.realize v).val
    lia

/-- `powerOfTwo L p e` holds exactly when `p = 2 ^ e`. -/
@[simp, fo_realize]
theorem realize_powerOfTwo (p e : (language L).Term α) (v : α → Fin n) :
    (powerOfTwo L p e).Realize v ↔ (p.realize v).val = 2 ^ (e.realize v).val := by
  fo_simp [powerOfTwo, Function.comp_def]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    by_cases hi : i < n
    · simpa only [← Fin.val_inj, eq_comm] using h (fun _ => ⟨i, hi⟩)
    · exact ⟨fun hp => (hi (bitIndex_lt hp)).elim,
        fun he => (hi (he ▸ (e.realize v).isLt)).elim⟩
  · intro hp i
    rw [hp, Nat.testBit_two_pow]
    simp [← Fin.val_inj, eq_comm]

omit [Fact (2 ≤ n)] in
private theorem shift_iff (x e z : Fin n) :
    ((∀ i : Fin n, z.val.testBit i.val = true ↔
        ∃ j : Fin n, j.val + e.val = i.val ∧ x.val.testBit j.val = true) ∧
      ∀ j : Fin n, x.val.testBit j.val = true →
        ∃ i : Fin n, j.val + e.val = i.val) ↔ x.val * 2 ^ e.val = z.val := by
  constructor
  · rintro ⟨hbits, hkeep⟩
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mul_two_pow]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨he, hx⟩
      have hj : i - e.val < n := bitIndex_lt hx
      obtain ⟨i', hi'⟩ := hkeep ⟨i - e.val, hj⟩ hx
      have hi : i < n := by have := i'.isLt; dsimp at hi'; lia
      exact (hbits ⟨i, hi⟩).mpr ⟨⟨i - e.val, hj⟩, by dsimp; lia, hx⟩
    · intro hz
      obtain ⟨j, hj, hx⟩ := (hbits ⟨i, bitIndex_lt hz⟩).mp hz
      refine ⟨by dsimp at hj; lia, ?_⟩
      have hi : i - e.val = j.val := by dsimp at hj; lia
      rwa [hi]
  · intro he
    constructor
    · intro i
      rw [← he, Nat.testBit_mul_two_pow]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hi, hx⟩
        exact ⟨⟨i.val - e.val, bitIndex_lt hx⟩, by dsimp; lia, hx⟩
      · rintro ⟨j, hj, hx⟩
        refine ⟨by lia, ?_⟩
        have hi : i.val - e.val = j.val := by lia
        rwa [hi]
    · intro j hx
      have hz : z.val.testBit (j.val + e.val) = true := by
        rw [← he, Nat.testBit_mul_two_pow]
        simp [hx]
      exact ⟨⟨j.val + e.val, bitIndex_lt hz⟩, rfl⟩

/-- `shiftLeft L x e z` holds exactly when `x * 2 ^ e = z`; the product is not reduced modulo
the universe size. -/
@[simp, fo_realize]
theorem realize_shiftLeft (x e z : (language L).Term α) (v : α → Fin n) :
    (shiftLeft L x e z).Realize v ↔
      (x.realize v).val * 2 ^ (e.realize v).val = (z.realize v).val := by
  rw [← shift_iff]
  fo_simp [shiftLeft]
  exact ⟨fun ⟨hbits, hkeep⟩ =>
    ⟨fun i => ⟨fun hz => let ⟨j, hj⟩ := (hbits (fun _ => i)).mp hz; ⟨j (), hj⟩,
      fun ⟨j, hj⟩ => (hbits (fun _ => i)).mpr ⟨fun _ => j, hj⟩⟩,
    fun j hj => let ⟨i, hi⟩ := hkeep (fun _ => j) hj; ⟨i (), hi⟩⟩,
    fun ⟨hbits, hkeep⟩ =>
    ⟨fun i => ⟨fun hz => let ⟨j, hj⟩ := (hbits (i ())).mp hz; ⟨fun _ => j, hj⟩,
      fun ⟨j, hj⟩ => (hbits (i ())).mpr ⟨j (), hj⟩⟩,
    fun j hj => let ⟨i, hi⟩ := hkeep (j ()) hj; ⟨fun _ => i, hi⟩⟩⟩

end Cslib.Logic.FO.Ordered
