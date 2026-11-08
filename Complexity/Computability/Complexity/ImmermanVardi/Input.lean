/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Run
import Complexity.Computability.Machines.Turing.MultiTape.InputAt

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
  have hlen (x : Fin B) : v.inputLength.Realize (fun _ : Fin 1 => x) ↔
      (encStructure a).length = x.val := by
    simpa only [Matrix.cons_fin_one] using v.realize_inputLength ha hB x
  rcases s with _ | b
  · simp only [inputSymbol, Formula.realize_sup, realize_natEq, Term.realize_var,
      Matrix.cons_val_zero, Formula.realize_iExs, Formula.realize_inf,
      Formula.realize_relabel, Formula.realize_not, realize_le, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr, not_le, hlen, Fin.lt_def, inputAt_eq_none_iff]
    refine or_congr Iff.rfl ⟨fun ⟨xs, hx, hp⟩ => by omega, fun hp => ?_⟩
    exact ⟨![⟨(encStructure a).length, hB⟩], rfl, hp⟩
  · have hdata (q : Fin B) (hq : q.val < (encStructure a).length) :
        (if b then v.inputBit.Realize ![q] else ¬v.inputBit.Realize ![q]) ↔
          (encStructure a)[q.val]? = some b := by
      rw [v.realize_inputBit ha hB q, List.getElem?_eq_getElem hq]
      cases b <;> cases (encStructure a)[q.val] <;> simp
    have hform : (v.inputSymbol (some b)).Realize ![p] ↔
        ∃ xs : Fin 2 → Fin B,
          (encStructure a).length = (xs 1).val ∧
          (xs 0).val < (xs 1).val ∧ (xs 0).val + 1 = p.val ∧
          (if b then v.inputBit.Realize ![xs 0] else ¬v.inputBit.Realize ![xs 0]) := by
      simp only [inputSymbol, Formula.realize_iExs, Formula.realize_inf]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Formula.realize_relabel,
        Formula.realize_not, realize_le, realize_addEq, realize_one_val,
        Term.realize_var, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        hlen, not_le, Fin.lt_def, Matrix.cons_fin_one, and_assoc]
    rw [hform, inputAt_eq_some_iff]
    constructor
    · rintro ⟨xs, hlen, hlt, hs, hb⟩
      exact ⟨(xs 0).val, hs.symm, (hdata (xs 0) (by omega)).mp hb⟩
    · rintro ⟨q, hpq, h⟩
      have hq : q < (encStructure a).length := (List.getElem?_eq_some_iff.mp h).choose
      exact ⟨![⟨q, by omega⟩, ⟨(encStructure a).length, hB⟩], rfl, hq, hpq.symm,
        (hdata ⟨q, by omega⟩ hq).mpr h⟩

end Cslib.Logic.Vocabulary
