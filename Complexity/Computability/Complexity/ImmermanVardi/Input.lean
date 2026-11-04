/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Run

/-!
# First-order input symbols for native deterministic machines

The direct length and bit formulas for `encStructure` yield formulas for all three native
input-tape symbols. Position zero is the left endmarker; the first data bit is at position one.
The formulas include the right endmarker and padding, and use no guessed relations.
-/

public section

open FirstOrder Language Turing Turing.MultiTapeTM

namespace Cslib.Logic.Vocabulary

open FO.Ordered

variable {L : Language} (v : Vocabulary L)

/-- The native input-tape symbol, including both endmarkers, defined from the encoded input. -/
noncomputable def inputSymbol : Option Bool → (language v.powerLanguage).Formula (Fin 1)
  | none => natEq v.powerLanguage 0 (.var 0) ⊔ Formula.iExs (Fin 1)
      (v.inputLength.relabel (fun _ => .inr 0) ⊓
        ∼(le v.powerLanguage (.var (.inl 0)) (.var (.inr 0))))
  | some b => Formula.iExs (Fin 2)
      (v.inputLength.relabel (fun _ => .inr 1) ⊓
        ∼(le v.powerLanguage (.var (.inr 1)) (.var (.inr 0))) ⊓
        addEq v.powerLanguage (.var (.inr 0)) (one v.powerLanguage) (.var (.inl 0)) ⊓
        (if b then v.inputBit.relabel (fun _ => .inr 0)
          else ∼(v.inputBit.relabel (fun _ => .inr 0))))

/-- The first-order input-symbol formula agrees exactly with the native machine input lookup. -/
theorem realize_inputSymbol {a : EncodedStructure} (ha : v.WellFormed a)
    {B : ℕ} [Fact (2 ≤ B)] (hB : (encStructure a).length < B)
    (s : Option Bool) (p : Fin B) :
    letI := v.powerStructure a B
    (v.inputSymbol s).Realize ![p] ↔ inputAt (encStructure a) p.val = s := by
  let _ := v.powerStructure a B
  have hlen (x : Fin B) := v.realize_inputLength ha hB x
  have hbit (x : Fin B) := v.realize_inputBit ha hB x
  rcases s with _ | b
  · simp only [inputSymbol, Formula.realize_sup, realize_natEq, Term.realize_var,
      Matrix.cons_val_zero, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_relabel, Formula.realize_not, realize_le, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr, not_le]
    constructor
    · rintro (hz | ⟨xs, hx, hp⟩)
      · simp [inputAt, hz]
      · have hx' : (encStructure a).length = (xs 0).val := by
          apply (hlen (xs 0)).mp
          simpa only [Matrix.cons_fin_one] using hx
        have hn : p.val ≠ 0 := by change (xs 0).val < p.val at hp; omega
        simp only [inputAt, hn, ite_false, List.getElem?_eq_none_iff]
        change (xs 0).val < p.val at hp
        omega
    · intro h
      by_cases hp : p.val = 0
      · exact Or.inl hp
      · right
        simp only [inputAt, hp, ite_false, List.getElem?_eq_none_iff] at h
        let l : Fin B := ⟨(encStructure a).length, hB⟩
        refine ⟨![l], ?_, ?_⟩
        · simpa only [Matrix.cons_fin_one] using (hlen l).mpr rfl
        · change (encStructure a).length < p.val
          omega
  · have hdata (q : Fin B) (hq : q.val < (encStructure a).length) :
        (if b then v.inputBit.Realize ![q] else ¬v.inputBit.Realize ![q]) ↔
          (encStructure a)[q.val]? = some b := by
      rw [hbit q, List.getElem?_eq_getElem hq]
      cases b <;> cases (encStructure a)[q.val] <;> simp
    have hform : (v.inputSymbol (some b)).Realize ![p] ↔
        ∃ xs : Fin 2 → Fin B,
          (encStructure a).length = (xs 1).val ∧
          (xs 0).val < (xs 1).val ∧ (xs 0).val + 1 = p.val ∧
          (if b then v.inputBit.Realize ![xs 0] else ¬v.inputBit.Realize ![xs 0]) := by
      simp only [inputSymbol, Formula.realize_iExs, Formula.realize_inf]
      apply exists_congr
      intro xs
      have hl : v.inputLength.Realize (fun _ : Fin 1 => xs 1) ↔
          (encStructure a).length = (xs 1).val := by
        simpa only [Matrix.cons_fin_one] using hlen (xs 1)
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Formula.realize_relabel,
        Formula.realize_not, realize_le, realize_addEq, realize_one_val,
        Term.realize_var, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        hl, not_le, Fin.lt_def, Matrix.cons_fin_one, and_assoc]
    rw [hform]
    constructor
    · rintro ⟨xs, hlen, hlt, hs, hb⟩
      have hq : (xs 0).val < (encStructure a).length := by omega
      have hp : p.val ≠ 0 := by omega
      have he : p.val - 1 = (xs 0).val := by omega
      simpa only [inputAt, hp, ite_false, he] using (hdata (xs 0) hq).mp hb
    · intro h
      have hp : p.val ≠ 0 := by intro hp; simp [inputAt, hp] at h
      simp only [inputAt, hp, ite_false] at h
      have hq : p.val - 1 < (encStructure a).length :=
        (List.getElem?_eq_some_iff.mp h).choose
      let q : Fin B := ⟨p.val - 1, by omega⟩
      let l : Fin B := ⟨(encStructure a).length, hB⟩
      exact ⟨![q, l], rfl, hq, by dsimp [q]; omega, (hdata q hq).mpr h⟩

end Cslib.Logic.Vocabulary
