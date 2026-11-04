/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Layout
public import Complexity.Logics.FirstOrder.Ordered.BitArithmetic

/-!
# First-order access to the native structure encoding

The canonical power structure supplies the original relation tables and their domains. Native
ordered arithmetic defines the length and every bit of `encStructure` directly, without guessing
auxiliary relations. The power universe must contain the complete encoded word and its endpoint.

The machine input is the existing unary-cardinality, framed-table encoding. Numeric symbols of
the power universe have their canonical meanings, rather than being extra input tables.

## Main definitions

* `Cslib.Logic.Vocabulary.inputLength`: the endpoint of the raw native input encoding.
* `Cslib.Logic.Vocabulary.inputBit`: the set bits of the raw native input encoding.

## Main results

* `Cslib.Logic.Vocabulary.realize_inputLength`, `Cslib.Logic.Vocabulary.realize_inputBit`:
  exact length and bit semantics, uniformly over sufficiently large power universes.

## References

* [N. Immerman, *Relational Queries Computable in Polynomial Time*][Immerman1986], Section 3,
  Lemma 3.1: first-order definition of the machine's input. The construction here uses the
  library's framed encoding and canonical BIT arithmetic.
-/

public section

namespace Cslib.Logic.Vocabulary

open FirstOrder Language Structure Turing.MultiTapeTM
open FO.Ordered

variable {L : Language} (v : Vocabulary L)

private abbrev inputLanguage := language v.powerLanguage

private def elementDomain : v.inputLanguage.Formula (Fin 1) :=
  FO.rel₁ (Sum.inl v.powerIsElem) 0

private def tableDomain (i : Fin v.count) : v.inputLanguage.Formula (Fin 1) :=
  FO.rel₁ (Sum.inl (v.powerInTable i)) 0

private def tableBit (i : Fin v.count) : v.inputLanguage.Formula (Fin 1) :=
  FO.rel₁ (Sum.inl (v.powerTableBit i)) 0

private noncomputable def frameEnd {α : Type*}
    (dom : v.inputLanguage.Formula (Fin 1)) (base last : v.inputLanguage.Term α) :
    v.inputLanguage.Formula α := Formula.iExs (Fin 3)
  (FO.isFirstOut (Sum.inl v.powerLt) dom (.inr 0) ⊓
    scaleEq v.powerLanguage 2 (.var (.inr 0)) (.var (.inr 1)) ⊓
    addEq v.powerLanguage (base.relabel Sum.inl) (.var (.inr 1)) (.var (.inr 2)) ⊓
    addEq v.powerLanguage (.var (.inr 2)) (one v.powerLanguage) (last.relabel Sum.inl))

private noncomputable def frameBit {α : Type*}
    (dom bit : v.inputLanguage.Formula (Fin 1)) (base pos : v.inputLanguage.Term α) :
    v.inputLanguage.Formula α := Formula.iExs (Fin 3)
  (FO.atVar dom (.inr 0) ⊓
    scaleEq v.powerLanguage 2 (.var (.inr 0)) (.var (.inr 1)) ⊓
    addEq v.powerLanguage (base.relabel Sum.inl) (.var (.inr 1)) (.var (.inr 2)) ⊓
    ((pos.relabel Sum.inl).equal (.var (.inr 2)) ⊔
      (FO.atVar bit (.inr 0) ⊓
        addEq v.powerLanguage (.var (.inr 2)) (one v.powerLanguage) (pos.relabel Sum.inl))))

section Semantics

variable {v} {B : ℕ} [Fact (2 ≤ B)] [v.powerLanguage.Structure (Fin B)]

private theorem realize_frameEnd {α : Type*}
    (dom : v.inputLanguage.Formula (Fin 1)) (base last : v.inputLanguage.Term α)
    (env : α → Fin B) (len : ℕ) (hlen : len < B)
    (hlt : ∀ x : Fin 2 → Fin B,
      RelMap (L := v.inputLanguage) (Sum.inl v.powerLt) x ↔ x 0 < x 1)
    (hdom : ∀ j : Fin B, dom.Realize ![j] ↔ (j : ℕ) < len) :
    (v.frameEnd dom base last).Realize env ↔
      (base.realize env).val + 2 * len + 1 = (last.realize env).val := by
  simp only [frameEnd, Formula.realize_iExs, Formula.realize_inf,
    FO.realize_isFirstOut hlt hlen hdom, realize_scaleEq, realize_addEq,
    Term.realize_var, Term.realize_relabel, realize_one_val, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, and_assoc]
  constructor
  · rintro ⟨u, hu, hd, hb, he⟩
    change (base.realize env).val + (u 1).val = (u 2).val at hb
    change (u 2).val + 1 = (last.realize env).val at he
    omega
  · intro h
    have hb := (last.realize env).isLt
    exact ⟨![⟨len, hlen⟩, ⟨2 * len, by omega⟩,
      ⟨(base.realize env).val + 2 * len, by omega⟩], rfl, rfl, rfl, h⟩

private theorem realize_frameBit {α : Type*}
    (dom bit : v.inputLanguage.Formula (Fin 1)) (base pos : v.inputLanguage.Term α)
    (env : α → Fin B) (w : List Bool)
    (hdom : ∀ j : Fin B, dom.Realize ![j] ↔ (j : ℕ) < w.length)
    (hbit : ∀ j : Fin B, (j : ℕ) < w.length → (bit.Realize ![j] ↔ w[j.val]? = some true)) :
    (v.frameBit dom bit base pos).Realize env ↔
      ∃ j < w.length, (pos.realize env).val = (base.realize env).val + 2 * j ∨
        (w[j]? = some true ∧ (pos.realize env).val = (base.realize env).val + 2 * j + 1) := by
  simp only [frameBit, Formula.realize_iExs, Formula.realize_inf, FO.realize_atVar,
    realize_scaleEq, realize_addEq, Formula.realize_sup, Formula.realize_equal,
    Term.realize_var, Term.realize_relabel, realize_one_val, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, and_assoc]
  constructor
  · rintro ⟨u, hd, hs, hb, he⟩
    change (base.realize env).val + (u 1).val = (u 2).val at hb
    have hj := (hdom (u 0)).mp hd
    refine ⟨(u 0).val, hj, ?_⟩
    rcases he with he | ⟨hw, he⟩
    · change (pos.realize env).val = (u 2).val at he
      exact Or.inl (by omega)
    · change (u 2).val + 1 = (pos.realize env).val at he
      exact Or.inr ⟨(hbit (u 0) hj).mp hw, by omega⟩
  · rintro ⟨j, hj, he⟩
    have hp := (pos.realize env).isLt
    have hbound : (base.realize env).val + 2 * j < B := by rcases he with h | ⟨_, h⟩ <;> omega
    let u : Fin 3 → Fin B :=
      ![⟨j, by omega⟩, ⟨2 * j, by omega⟩, ⟨(base.realize env).val + 2 * j, hbound⟩]
    refine ⟨u, (hdom (u 0)).mpr hj, rfl, rfl, ?_⟩
    rcases he with he | ⟨hw, he⟩
    · exact Or.inl he
    · exact Or.inr ⟨(hbit (u 0) hj).mpr hw, he.symm⟩

end Semantics

private noncomputable def prefixEnd : ℕ → {α : Type*} →
    v.inputLanguage.Term α → v.inputLanguage.Formula α
  | 0, _, last => v.frameEnd v.elementDomain (zero v.powerLanguage) last
  | m + 1, _, last => if h : m < v.count then Formula.iExs Unit
      (prefixEnd m (.var (.inr ())) ⊓
        v.frameEnd (v.tableDomain ⟨m, h⟩) (.var (.inr ())) (last.relabel Sum.inl))
    else ⊥

private noncomputable def prefixBit : ℕ → {α : Type*} →
    v.inputLanguage.Term α → v.inputLanguage.Formula α
  | 0, _, pos => v.frameBit v.elementDomain ⊤ (zero v.powerLanguage) pos
  | m + 1, _, pos => if h : m < v.count then prefixBit m pos ⊔ Formula.iExs Unit
      (v.prefixEnd m (.var (.inr ())) ⊓
        v.frameBit (v.tableDomain ⟨m, h⟩) (v.tableBit ⟨m, h⟩)
          (.var (.inr ())) (pos.relabel Sum.inl))
    else ⊥

/-- The length of the native source-only encoding, inside the canonically ordered power domain. -/
noncomputable def inputLength : (language v.powerLanguage).Formula (Fin 1) :=
  v.prefixEnd v.count (.var 0)

/-- A set bit of the native source-only encoding. Positions outside the encoded word are false. -/
noncomputable def inputBit : (language v.powerLanguage).Formula (Fin 1) :=
  v.prefixBit v.count (.var 0)

private theorem frame_true_iff (w : List Bool) (p : ℕ) :
    (frame w)[p]? = some true ↔
      ∃ j < w.length, p = 2 * j ∨ (w[j]? = some true ∧ p = 2 * j + 1) := by
  constructor
  · intro h
    have hp := (List.getElem?_eq_some_iff.mp h).choose
    rw [length_frame] at hp
    have hne : p ≠ 2 * w.length := by
      intro he
      rw [he, getElem?_frame_two_mul_length] at h
      contradiction
    have hj : p / 2 < w.length := by omega
    refine ⟨p / 2, hj, ?_⟩
    rcases Nat.mod_two_eq_zero_or_one p with hm | hm
    · exact Or.inl (by omega)
    · have he : p = 2 * (p / 2) + 1 := by omega
      have hb : (frame w)[2 * (p / 2) + 1]? = some true := by rw [← he]; exact h
      rw [getElem?_frame_two_mul_add_one hj] at hb
      exact Or.inr ⟨hb, he⟩
  · rintro ⟨j, hj, he | ⟨hb, he⟩⟩
    · rw [he, getElem?_frame_two_mul hj]
    · rw [he, getElem?_frame_two_mul_add_one hj]
      exact hb

private theorem shifted_frame_true_iff (w : List Bool) (base p : ℕ) :
    base ≤ p ∧ (frame w)[p - base]? = some true ↔
      ∃ j < w.length, p = base + 2 * j ∨
        (w[j]? = some true ∧ p = base + 2 * j + 1) := by
  rw [frame_true_iff]
  constructor
  · rintro ⟨hp, j, hj, he | ⟨hb, he⟩⟩
    · exact ⟨j, hj, Or.inl (by omega)⟩
    · exact ⟨j, hj, Or.inr ⟨hb, by omega⟩⟩
  · rintro ⟨j, hj, he | ⟨hb, he⟩⟩
    · exact ⟨by omega, j, hj, Or.inl (by omega)⟩
    · exact ⟨by omega, j, hj, Or.inr ⟨hb, by omega⟩⟩

private theorem append_true_iff (u w : List Bool) (p : ℕ) :
    (u ++ w)[p]? = some true ↔
      u[p]? = some true ∨ (u.length ≤ p ∧ w[p - u.length]? = some true) := by
  by_cases hp : p < u.length
  · simp [List.getElem?_append_left hp, Nat.not_le.mpr hp]
  · simp [List.getElem?_append_right (Nat.le_of_not_gt hp), Nat.le_of_not_gt hp]

private theorem prefix_length_lt {a : EncodedStructure} (ha : v.WellFormed a)
    {B : ℕ} (hB : (encStructure a).length < B) {m : ℕ} (hm : m ≤ v.count) :
    (v.encStructurePrefix a m).length < B := by
  rw [v.length_encStructurePrefix (ha.1.symm ▸ hm) hm]
  exact (tableStart_le_length a m).trans_lt hB

private theorem realize_prefixEnd {a : EncodedStructure} (ha : v.WellFormed a)
    {B : ℕ} [Fact (2 ≤ B)] (hB : (encStructure a).length < B)
    {m : ℕ} (hm : m ≤ v.count) {α : Type*}
    (last : v.inputLanguage.Term α) (env : α → Fin B) :
    letI := v.powerStructure a B
    (v.prefixEnd m last).Realize env ↔
      (v.encStructurePrefix a m).length = (last.realize env).val := by
  let _ := v.powerStructure a B
  have hlt (x : Fin 2 → Fin B) :
      RelMap (L := v.inputLanguage) (Sum.inl v.powerLt) x ↔ x 0 < x 1 := Iff.rfl
  induction m generalizing α with
  | zero =>
    have hn : a.1 < B := (card_le_length_encStructure a).trans_lt hB
    rw [prefixEnd, realize_frameEnd _ _ _ _ a.1 hn hlt (fun _ => Iff.rfl)]
    simp only [realize_zero_val, Nat.zero_add, encStructurePrefix_zero, length_frame,
      encUnary_apply, List.length_replicate]
  | succ m ih =>
    have hm' : m < v.count := by omega
    let i : Fin v.count := ⟨m, hm'⟩
    have hp := v.prefix_length_lt ha hB (Nat.le_of_lt hm')
    have hs := v.prefix_length_lt ha hB hm
    have hs' : (v.encStructurePrefix a m).length +
        2 * (v.table a (v.symbol i)).length + 1 < B := by
      simpa only [show m + 1 = i.val + 1 from rfl, encStructurePrefix_succ,
        List.length_append, length_frame, Nat.add_assoc] using hs
    have hlen : (v.table a (v.symbol i)).length < B := by omega
    have hdom (j : Fin B) : (v.tableDomain i).Realize ![j] ↔
        j.val < (v.table a (v.symbol i)).length := by
      rw [ha.length_table]
      exact Iff.rfl
    rw [prefixEnd, dite_eq_left hm']
    simp only [Formula.realize_iExs, Formula.realize_inf]
    constructor
    · rintro ⟨u, hu, hf⟩
      have hb := (ih (Nat.le_of_lt hm') _ (Sum.elim env u)).mp hu
      have he := (realize_frameEnd _ _ _ _ _ hlen hlt hdom).mp hf
      simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
        Sum.elim_inl, Sum.elim_inr] at hb he
      change (u ()).val + 2 * (v.table a (v.symbol i)).length + 1 =
        (last.realize env).val at he
      rw [show m + 1 = i.val + 1 from rfl, encStructurePrefix_succ, List.length_append,
        length_frame]
      change (v.encStructurePrefix a m).length +
        (2 * (v.table a (v.symbol i)).length + 1) = (last.realize env).val
      omega
    · intro he
      let u : Unit → Fin B := fun _ => ⟨(v.encStructurePrefix a m).length, hp⟩
      refine ⟨u, (ih (Nat.le_of_lt hm') _ _).mpr rfl, ?_⟩
      apply (realize_frameEnd _ _ _ _ _ hlen hlt hdom).mpr
      simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
        Sum.elim_inl, Sum.elim_inr]
      simpa only [show m + 1 = i.val + 1 from rfl, encStructurePrefix_succ,
        List.length_append, length_frame, Nat.add_assoc] using he

/-- The direct first-order length formula equals the length of the native machine input.
The endpoint must be an element of the canonical power universe. -/
@[fo_realize]
theorem realize_inputLength {a : EncodedStructure} (ha : v.WellFormed a)
    {B : ℕ} [Fact (2 ≤ B)] (hB : (encStructure a).length < B) (p : Fin B) :
    letI := v.powerStructure a B
    v.inputLength.Realize ![p] ↔ (encStructure a).length = p.val := by
  let _ := v.powerStructure a B
  simpa only [inputLength, encStructurePrefix_count v ha, Term.realize_var,
    Matrix.cons_val_zero] using v.realize_prefixEnd ha hB (le_refl v.count) (.var 0) ![p]

private theorem realize_prefixBit {a : EncodedStructure} (ha : v.WellFormed a)
    {B : ℕ} [Fact (2 ≤ B)] (hB : (encStructure a).length < B)
    {m : ℕ} (hm : m ≤ v.count) {α : Type*}
    (pos : v.inputLanguage.Term α) (env : α → Fin B) :
    letI := v.powerStructure a B
    (v.prefixBit m pos).Realize env ↔
      (v.encStructurePrefix a m)[(pos.realize env).val]? = some true := by
  let _ := v.powerStructure a B
  induction m generalizing α with
  | zero =>
    have hdom (j : Fin B) : v.elementDomain.Realize ![j] ↔ j.val < (encUnary a.1).length := by
      simp only [encUnary_apply, List.length_replicate]
      exact Iff.rfl
    have hbit (j : Fin B) (hj : j.val < (encUnary a.1).length) :
        (⊤ : v.inputLanguage.Formula (Fin 1)).Realize ![j] ↔
          (encUnary a.1)[j.val]? = some true := by
      have hj' : j.val < a.1 := by simpa using hj
      simp only [encUnary_apply, Formula.realize_top, List.getElem?_replicate, ite_eq_left hj']
    have hf := realize_frameBit v.elementDomain ⊤ (zero v.powerLanguage) pos env
      (encUnary a.1) hdom hbit
    simp only [realize_zero_val, Nat.zero_add] at hf
    simpa only [prefixBit, encStructurePrefix_zero] using
      hf.trans (frame_true_iff _ _).symm
  | succ m ih =>
    have hm' : m < v.count := by omega
    let i : Fin v.count := ⟨m, hm'⟩
    have hp := v.prefix_length_lt ha hB (Nat.le_of_lt hm')
    have hdom (j : Fin B) : (v.tableDomain i).Realize ![j] ↔
        j.val < (v.table a (v.symbol i)).length := by
      rw [ha.length_table]
      exact Iff.rfl
    have hbit (j : Fin B) (hj : j.val < (v.table a (v.symbol i)).length) :
        (v.tableBit i).Realize ![j] ↔ (v.table a (v.symbol i))[j.val]? = some true := by
      change (j.val < a.1 ^ (v.symbol i).1 ∧
        (v.table a (v.symbol i)).getD j.val false = true) ↔ _
      rw [← WellFormed.length_table v ha (v.symbol i)]
      simp [hj]
    rw [prefixBit, dite_eq_left hm', Formula.realize_sup, Formula.realize_iExs]
    simp only [Formula.realize_inf]
    rw [show m + 1 = i.val + 1 from rfl,
      encStructurePrefix_succ, append_true_iff]
    apply or_congr (ih (Nat.le_of_lt hm') pos env)
    constructor
    · rintro ⟨u, hu, hf⟩
      have hb := (v.realize_prefixEnd ha hB (Nat.le_of_lt hm') _ _).mp hu
      have hf' := (realize_frameBit _ _ _ _ _ _ hdom hbit).mp hf
      simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
        Sum.elim_inl, Sum.elim_inr] at hb hf'
      rw [← hb] at hf'
      exact (shifted_frame_true_iff _ _ _).mpr hf'
    · intro hf
      let u : Unit → Fin B := fun _ => ⟨(v.encStructurePrefix a m).length, hp⟩
      refine ⟨u, (v.realize_prefixEnd ha hB (Nat.le_of_lt hm') _ _).mpr rfl, ?_⟩
      apply (realize_frameBit _ _ _ _ _ _ hdom hbit).mpr
      simp only [Term.realize_var, Term.realize_relabel, Function.comp_def,
        Sum.elim_inl, Sum.elim_inr]
      exact (shifted_frame_true_iff _ _ _).mp hf

/-- The direct first-order input-bit formula recognizes precisely the set bits of the existing
native machine encoding, including its frame markers and rejecting terminators and padding. -/
@[fo_realize]
theorem realize_inputBit {a : EncodedStructure} (ha : v.WellFormed a)
    {B : ℕ} [Fact (2 ≤ B)] (hB : (encStructure a).length < B) (p : Fin B) :
    letI := v.powerStructure a B
    v.inputBit.Realize ![p] ↔ (encStructure a)[p.val]? = some true := by
  let _ := v.powerStructure a B
  simpa only [inputBit, encStructurePrefix_count v ha, Term.realize_var,
    Matrix.cons_val_zero] using v.realize_prefixBit ha hB (le_refl v.count) (.var 0) ![p]

end Cslib.Logic.Vocabulary
