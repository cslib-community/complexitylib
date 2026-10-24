/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Synthesis
public import Complexity.Computability.Circuit.Iteration
public import Complexity.Foundations.Data.BitString.Basic
public import Init.Data.BitVec.Bitblast
public import Mathlib.Data.List.OfFn

/-!
# Word arithmetic over the De Morgan basis

Words are Lean's `BitVec`s, stored least significant bit first. A word-valued function of the
inputs is available when each of its coordinate functions is (`Boolean.wordWires`). This module
bounds the gates needed to make words available from available words: addition, subtraction,
unsigned comparison, comparison with a constant, complementation, constants, multiplexing, and
selection of one of several words by a binary index. Equality of available bit strings is
`Formula.equalBits` inserted by `Synthesis.circuit`. Their semantics are the
`BitVec` operations, through the bit-blasting identities of the core library; no decision
procedure or native evaluation is used.

Addition is a ripple-carry adder: every carry is computed once and shared by the sum bits, for
`12 * w + 1` gates on `w`-bit words including the initial carry constant. All bounds charge every
gate, including constants and negations.

## Main definitions

* `Cslib.Circuits.Boolean.word`: the word with given bits.
* `Cslib.Circuits.Boolean.wordWires`: the coordinate functions of a word-valued function.
* `Cslib.Circuits.Boolean.selectBits`: select one of several bit strings by a binary index.

## Main results

* `Cslib.Circuits.Synthesis.mux`: a multiplexer in four gates.
* `Cslib.Circuits.Synthesis.word_add`, `word_addCarry`, `word_sub`: ripple-carry arithmetic.
* `Cslib.Circuits.Synthesis.word_ult`, `word_eq_const`: comparisons.
* `Cslib.Circuits.Synthesis.word_not`, `word_const`, `word_mux`: bitwise operations.
* `Cslib.Circuits.Synthesis.selectBits`: selection charging one comparison per record and bit.

## References

* Adapted from lean/Proofs/{Synthesis,Arithmetic,Words}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions],
  where each sum bit recomputes its carry chain.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Boolean

variable {n k w R : ℕ}

/-- The word with the given bits, least significant first. -/
def word (bits : BitString w) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn bits)).cast (by simp)

theorem getLsbD_word (bits : BitString w) (i : Fin w) :
    (word bits).getLsbD i.val = bits i := by
  rw [word, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  simp

@[simp] theorem getElem_word (bits : BitString w) (i : ℕ) (hi : i < w) :
    (word bits)[i] = bits ⟨i, hi⟩ := getLsbD_word bits ⟨i, hi⟩

theorem word_getLsbD (a : BitVec w) : word (fun i : Fin w => a.getLsbD i.val) = a :=
  BitVec.eq_of_getLsbD_eq fun i hi => getLsbD_word _ ⟨i, hi⟩

/-- The word representation and the bit-string numbering use the same unsigned value. -/
theorem toNat_word_eq_equivFin {w : ℕ} (x : BitString w) :
    (word x).toNat = (BitString.equivFin w x : ℕ) := by
  induction w with
  | zero =>
    have h := (BitString.equivFin 0 x).isLt
    simp only [pow_zero, Nat.lt_one_iff] at h
    have hx := (word x).isLt
    simp only [pow_zero, Nat.lt_one_iff] at hx
    exact hx.trans h.symm
  | succ w ih =>
    have heq : x = Fin.cons (x 0) (fun i => x i.succ) := by
      funext i
      induction i using Fin.cases <;> rfl
    rw [heq, BitString.val_equivFin_cons]
    have hw : word (Fin.cons (x 0) (fun i => x i.succ)) =
        (word (fun i => x i.succ)).concat (x 0) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [getLsbD_word _ ⟨i, hi⟩, BitVec.getLsbD_concat]
      cases i with
      | zero => simp
      | succ i =>
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
          Nat.add_sub_cancel]
        exact (getLsbD_word (fun i => x i.succ) ⟨i, by omega⟩).symm
    rw [hw, BitVec.toNat_concat, ih]
    omega

/-- The coordinate functions of a word-valued function. -/
def wordWires (a : BitString n → BitVec w) : Set (BooleanFunction n) :=
  Set.range fun i : Fin w => fun x => (a x).getLsbD i.val

/-- Zero extension and truncation only rewire available bits and the false constant. -/
theorem wordWires_setWidth_subset {v : ℕ} {s : Set (BooleanFunction n)}
    {value : BitString n → BitVec w} (hv : wordWires value ⊆ s) (hz : (fun _ => false) ∈ s) :
    wordWires (fun x => (value x).setWidth v) ⊆ s := by
  rintro _ ⟨bit, rfl⟩
  simp only [BitVec.getLsbD_setWidth, bit.isLt, decide_true, Bool.true_and]
  by_cases hi : bit.val < w
  · exact hv ⟨⟨bit.val, hi⟩, rfl⟩
  · simpa only [BitVec.getLsbD_of_ge _ _ (by omega : w ≤ bit.val)] using hz

/-- The bit string at the position given by the value of a binary index, or all-false if the
value is not a position. Positions beyond `2 ^ k` are never selected. -/
def selectBits (index : BitVec k) (values : Fin R → BitString w) : BitString w :=
  fun bit => decide (∃ j : Fin R, index.toNat = j.val ∧ values j bit = true)

/-- An index whose value is a position selects exactly that bit string. -/
theorem selectBits_of_toNat_lt (index : BitVec k) (values : Fin R → BitString w)
    (hi : index.toNat < R) : selectBits index values = values ⟨index.toNat, hi⟩ := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  simp only [selectBits, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hv⟩
    rwa [show (⟨index.toNat, hi⟩ : Fin R) = j from Fin.ext hj]
  · exact fun hv => ⟨_, rfl, hv⟩

/-- An index whose value is not a position selects all-false. -/
theorem selectBits_of_le_toNat (index : BitVec k) (values : Fin R → BitString w)
    (hi : R ≤ index.toNat) : selectBits index values = fun _ => false := by
  funext bit
  simp only [selectBits, decide_eq_false_iff_not, not_exists, not_and]
  intro j hj
  omega

/-- An in-range position written as an index selects exactly its bit string. -/
theorem selectBits_ofNat (hR : R ≤ 2 ^ k) (values : Fin R → BitString w) (j : Fin R) :
    selectBits (BitVec.ofNat k j.val) values = values j := by
  have hj : (BitVec.ofNat k j.val).toNat = j.val := by
    simp [Nat.mod_eq_of_lt (j.isLt.trans_le hR)]
  rw [selectBits_of_toNat_lt _ _ (by have := j.isLt; omega)]
  exact congrArg values (Fin.ext hj)

end Boolean

namespace Synthesis

open Boolean

variable {n k w R : ℕ} {s : Set (BooleanFunction n)}

/-- One available control bit selects between two available functions in four gates. -/
theorem mux {f a b : BooleanFunction n} (hf : f ∈ s) (ha : a ∈ s) (hb : b ∈ s) :
    Synthesis interpretation s {fun x => if f x then a x else b x} 4 := by
  have h := ((of_mem hf).and (of_mem ha)).or ((of_mem hf).not.and (of_mem hb))
  convert h using 2
  funext x
  cases f x <;> simp

section Arithmetic

variable (a b : BitString n → BitVec w)

/-- One carry chain uses four gates per bit and its initial constant. -/
private theorem word_carry (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) (c : Bool) {t : ℕ} (ht : t ≤ w) :
    Synthesis interpretation s {fun x => BitVec.carry t (a x) (b x) c} (4 * t + 1) := by
  induction t with
  | zero => simpa using Synthesis.const c
  | succ t ih =>
    have hat := of_mem (I := interpretation) (ha ⟨t, by omega⟩)
    have hbt := of_mem (I := interpretation) (hb ⟨t, by omega⟩)
    have h := (hat.and hbt).or ((hat.or hbt).and (ih (by omega)))
    convert h using 2
    · funext x
      rw [BitVec.carry_succ]
      cases (a x).getLsbD t <;> cases (b x).getLsbD t <;>
        cases BitVec.carry t (a x) (b x) c <;> rfl
    · omega

/-- All carries of a sum, each computed once from the previous one. -/
private theorem word_carries (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) (c : Bool) :
    Synthesis interpretation s
      (stages (fun t => {fun x => BitVec.carry t (a x) (b x) c}) w) (4 * w + 1) := by
  let q := fun t => ({fun x => BitVec.carry t (a x) (b x) c} : Set (BooleanFunction n))
  have h0 : Synthesis interpretation s (q 0) 1 := by simpa [q] using Synthesis.const c
  have hs := steps (I := interpretation) (s := s ∪ q 0) q 4 w Set.subset_union_right
    fun t ht => ?_
  · simpa [Nat.add_comm, Nat.mul_comm] using h0.trans hs
  · have hat := of_mem (I := interpretation) (s := s ∪ q 0 ∪ stages q t)
      (Or.inl (Or.inl (ha ⟨t, ht⟩)))
    have hbt := of_mem (I := interpretation) (s := s ∪ q 0 ∪ stages q t)
      (Or.inl (Or.inl (hb ⟨t, ht⟩)))
    have hct := of_mem (I := interpretation) (s := s ∪ q 0 ∪ stages q t)
      (Or.inr (subset_stages q le_rfl rfl))
    have h := (hat.and hbt).or ((hat.or hbt).and hct)
    convert h using 2
    funext x
    rw [BitVec.carry_succ]
    cases (a x).getLsbD t <;> cases (b x).getLsbD t <;>
      cases BitVec.carry t (a x) (b x) c <;> rfl

/-- Ripple-carry addition with an initial carry: four gates per carry, eight per sum bit and
the initial constant. -/
theorem word_addCarry (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) (c : Bool) :
    Synthesis interpretation s
      (wordWires fun x => a x + b x + BitVec.setWidth w (BitVec.ofBool c)) (12 * w + 1) := by
  let C := stages (fun t => {fun x => BitVec.carry t (a x) (b x) c}) w
  have hsum := family (I := interpretation) (s := s ∪ C)
    (fun i : Fin w => fun x =>
      (a x).getLsbD i.val ^^ ((b x).getLsbD i.val ^^ BitVec.carry i.val (a x) (b x) c))
    (fun _ => 8) fun i =>
      (of_mem (Or.inl (ha i))).xor ((of_mem (Or.inl (hb i))).xor
        (of_mem (Or.inr (subset_stages _ i.isLt.le rfl))))
  have h := (word_carries a b ha hb c).trans hsum
  have heq : (fun i : Fin w => fun x =>
      (a x + b x + BitVec.setWidth w (BitVec.ofBool c)).getLsbD i.val) =
      fun i : Fin w => fun x =>
        (a x).getLsbD i.val ^^ ((b x).getLsbD i.val ^^ BitVec.carry i.val (a x) (b x) c) :=
    funext fun i => funext fun x => BitVec.getLsbD_add_add_bool i.isLt (a x) (b x) c
  rw [wordWires, heq]
  exact h.mono Set.Subset.rfl Set.Subset.rfl
    (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; omega)

/-- Ripple-carry addition modulo the word width. -/
theorem word_add (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => a x + b x) (12 * w + 1) := by
  simpa using word_addCarry a b ha hb false

/-- A hardwired word uses one constant gate per bit. -/
theorem word_const (v : BitVec w) : Synthesis interpretation s (wordWires fun _ => v) w := by
  simpa [wordWires] using family (I := interpretation) (s := s)
    (fun i : Fin w => fun _ => v.getLsbD i.val) (fun _ => 1) fun _ => Synthesis.const _

/-- Bitwise complementation uses one gate per bit. -/
theorem word_not (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => ~~~b x) w := by
  have h := family (I := interpretation) (s := s)
    (fun i : Fin w => fun x => !(b x).getLsbD i.val) (fun _ => 1)
    fun i => (of_mem (hb i)).not
  simpa only [wordWires, BitVec.getLsbD_not, Fin.is_lt, decide_true, Bool.true_and,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

/-- Unsigned comparison, by the carry of `a + ~~~b + 1`. -/
theorem word_ult (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s {fun x => (a x).ult (b x)} (5 * w + 2) := by
  have hc := word_carry (s := s ∪ wordWires fun x => ~~~b x) a (fun x => ~~~b x)
    (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩) true le_rfl
  have h := (word_not b hb).trans hc.not
  simpa only [BitVec.ult_eq_not_carry, Nat.mul_succ, Nat.add_assoc,
    show w + (4 * w + 1 + 1) = 5 * w + 2 by omega] using h

/-- Subtraction modulo the word width, as `a + ~~~b + 1`. -/
theorem word_sub (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => a x - b x) (13 * w + 1) := by
  have hc := word_addCarry (s := s ∪ wordWires fun x => ~~~b x) a (fun x => ~~~b x)
    (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩) true
  have h := (word_not b hb).trans hc
  have heq (x : BitString n) :
      a x - b x = a x + ~~~b x + BitVec.setWidth w (BitVec.ofBool true) := by
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  simp only [← heq] at h
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- A word multiplexer shares one available control bit, four gates per bit. -/
theorem word_mux (flag : BooleanFunction n) (hf : flag ∈ s)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => if flag x then a x else b x) (4 * w) := by
  have h := family (I := interpretation) (s := s)
    (fun i : Fin w => fun x => if flag x then (a x).getLsbD i.val else (b x).getLsbD i.val)
    (fun _ => 4) fun i => mux hf (ha i) (hb i)
  have heq : (fun i : Fin w => fun x => (if flag x then a x else b x).getLsbD i.val) =
      fun i : Fin w => fun x => if flag x then (a x).getLsbD i.val else (b x).getLsbD i.val := by
    funext i x
    split <;> rfl
  rw [wordWires, heq]
  simpa [Nat.mul_comm] using h

end Arithmetic

/-- Testing a word against a constant needs one literal per bit and a conjunction. -/
theorem word_eq_const (a : BitString n → BitVec k)
    (ha : ∀ i : Fin k, (fun x => (a x).getLsbD i.val) ∈ s) (v : BitVec k) :
    Synthesis interpretation s {fun x => decide (a x = v)} (2 * k + 1) := by
  have hlit (i : Fin k) : Synthesis interpretation s
      {fun x => decide ((a x).getLsbD i.val = v.getLsbD i.val)} 1 := by
    have h := of_mem (I := interpretation) (ha i)
    cases hv : v.getLsbD i.val
    · simpa only [hv, Bool.decide_eq_false] using h.not
    · simpa only [hv, Bool.decide_eq_true] using
        h.mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le 1)
  have h := forall_mem (s := s) Finset.univ
    (fun i : Fin k => fun x => decide ((a x).getLsbD i.val = v.getLsbD i.val))
    (fun _ => 1) fun i _ => hlit i
  have heq (x : BitString n) : (∀ i : Fin k, (a x).getLsbD i.val = v.getLsbD i.val) ↔ a x = v :=
    ⟨fun h => BitVec.eq_of_getLsbD_eq fun i hi => h ⟨i, hi⟩,
      fun h i => congrArg (fun a => a.getLsbD i.val) h⟩
  simpa only [Finset.mem_univ, forall_true_left, decide_eq_true_eq, heq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_comm] using h

/-- Selecting among available bit strings by an available index charges one comparison with
each position for every output bit. -/
theorem selectBits (index : BitString n → BitVec k) (values : Fin R → BitString n → BitString w)
    (hi : ∀ i : Fin k, (fun x => (index x).getLsbD i.val) ∈ s)
    (hv : ∀ j bit, (fun x => values j x bit) ∈ s) :
    Synthesis interpretation s
      (Set.range fun bit x => Boolean.selectBits (index x) (fun j => values j x) bit)
      (w * (R * (2 * k + 3) + 1)) := by
  have hs := family (I := interpretation) (s := s)
    (fun bit x => Boolean.selectBits (index x) (fun j => values j x) bit)
    (fun _ => R * (2 * k + 3) + 1) fun bit => ?_
  · simpa using hs
  · have h := exists_mem (s := s) Finset.univ
      (fun j : Fin R => fun x => decide ((index x).toNat = j.val) && values j x bit)
      (fun _ => 2 * k + 2) fun j _ => ?_
    · simpa [Boolean.selectBits, Nat.add_assoc] using h
    by_cases hj : j.val < 2 ^ k
    · have heq : (fun x => decide ((index x).toNat = j.val)) =
          fun x => decide (index x = BitVec.ofNat k j.val) := by
        funext x
        simp only [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
      rw [show (fun x => decide ((index x).toNat = j.val) && values j x bit) =
          fun x => decide (index x = BitVec.ofNat k j.val) && values j x bit from
        funext fun x => by rw [congrFun heq x]]
      exact (word_eq_const index hi _).and (of_mem (hv j bit))
    · have hfalse : (fun x => decide ((index x).toNat = j.val) && values j x bit) =
          fun _ => false := by
        funext x
        have := (index x).isLt
        simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
        omega
      rw [hfalse]
      exact (Synthesis.const false).mono Set.Subset.rfl Set.Subset.rfl (by omega)

end Synthesis

end Cslib.Circuits
