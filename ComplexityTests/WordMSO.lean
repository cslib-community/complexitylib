/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.SecondOrder.WordMSO.Separation

/-!
# Tests: monadic second-order logic over words and the Büchi–Elgot–Trakhtenbrot theorem

* an explicit first-order sentence ("some `true` strictly before some `false`"), its language,
  a word in it and a word outside it, its `IsFO` certificate, and its regularity;
* the even-length sentence on words of length `0`, `1` and `2`, and that it is not syntactically
  first-order;
* the run sentence `dfaSentence` of a concrete parity DFA on accepted and rejected words;
* the equivalence `definable_iff_isRegular` instantiated at a concrete regular language;
* MSO ⇒ regular over the infinite alphabet `ℕ`, and the extended-alphabet languages of formulas
  with free variables;
* a Mathlib first-order sentence over the word vocabulary, evaluated on concrete words, and its
  language's first-order definability and regularity;
* `FO[<] ⊊ MSO`: even length is not first-order definable over a nonempty alphabet, including
  for Mathlib sentences, while over the empty alphabet it is (by `⊤`), so nonemptiness is needed.
-/

namespace ComplexityTests.WordMSO

open Cslib.Logic.WordMSO Cslib.Logic.WordMSO.Formula

/-! ### An explicit first-order sentence -/

/-- "Some position carrying `true` is strictly before some position carrying `false`". -/
def trueBeforeFalse : Sentence Bool :=
  ex (ex (and (lt (Fin.castSucc (Fin.last 0)) (Fin.last 1))
    (and (letter true (Fin.castSucc (Fin.last 0))) (letter false (Fin.last 1)))))

theorem mem_trueBeforeFalse (w : List Bool) :
    w ∈ trueBeforeFalse.language ↔ ∃ i j : Fin w.length, i < j ∧ w[i] = true ∧ w[j] = false := by
  change trueBeforeFalse.Realize (fun i : Fin w.length => w[i]) Fin.elim0 Fin.elim0 ↔ _
  simp only [trueBeforeFalse, realize_ex, realize_and, realize_lt, realize_letter, Fin.snoc_last,
    Fin.snoc_castSucc]

example : [true, false] ∈ trueBeforeFalse.language :=
  (mem_trueBeforeFalse _).2 ⟨0, 1, by decide, rfl, rfl⟩

example : [false, true] ∉ trueBeforeFalse.language := by
  rw [mem_trueBeforeFalse]
  decide

example : [] ∉ trueBeforeFalse.language := by
  rw [mem_trueBeforeFalse]
  decide

/-- The sentence is first-order, so its language is `FO[<]`-definable. -/
example : FODefinable trueBeforeFalse.language :=
  ⟨trueBeforeFalse, by simp [trueBeforeFalse], rfl⟩

example : trueBeforeFalse.language.IsRegular :=
  trueBeforeFalse.isRegular_language

/-! ### Even length -/

example : [(), ()] ∈ (evenSentence : Sentence Unit).language := by
  rw [evenSentence_language]
  exact ⟨1, rfl⟩

example : [()] ∉ (evenSentence : Sentence Unit).language := by
  rw [evenSentence_language]
  exact Nat.not_even_one

example : [] ∈ (evenSentence : Sentence Unit).language := by
  rw [evenSentence_language]
  exact ⟨0, rfl⟩

/-- `evenSentence` quantifies a set variable, so it is not a first-order sentence. (No first-order
sentence defines even length: see `not_foDefinable_even` below.) -/
example : ¬ (evenSentence : Sentence Unit).IsFO :=
  not_isFO_exSet _

example : Language.IsRegular {w : List Unit | Even w.length} :=
  definable_even.isRegular

/-! ### The run sentence of a concrete DFA -/

/-- The DFA over `Bool` accepting the words with an even number of `true` letters. -/
def parity : DFA Bool Bool := ⟨fun s a => xor s a, false, {false}⟩

example : [true, true] ∈ (dfaSentence parity).language := by
  rw [dfaSentence_language, DFA.mem_accepts]
  rfl

example : [] ∈ (dfaSentence parity).language := by
  rw [dfaSentence_language, DFA.mem_accepts]
  rfl

example : [true, false] ∉ (dfaSentence parity).language := by
  rw [dfaSentence_language, DFA.mem_accepts]
  change parity.eval [true, false] ≠ false
  decide

/-! ### The equivalence -/

example : Definable ({[true]} : Language Bool) :=
  definable_iff_isRegular.2 (Cslib.Language.IsRegular.char true)

example : Definable parity.accepts :=
  definable_iff_isRegular.2 ⟨Bool, inferInstance, parity, rfl⟩

/-! ### Infinite alphabets and free variables -/

/-- Over the infinite alphabet `ℕ`, the words containing the letter `0` are MSO-definable and hence
regular; the direction MSO ⇒ regular needs no finiteness of the alphabet. -/
example : Language.IsRegular {w : List ℕ | 0 ∈ w} := by
  refine Definable.isRegular ⟨ex (letter 0 (Fin.last 0)), ?_⟩
  ext w
  change (∃ i : Fin w.length, w[i] = 0) ↔ 0 ∈ w
  rw [List.mem_iff_getElem]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, i.isLt, hi⟩, fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩⟩

/-- A formula with one free first-order and one free set variable, read over the extended
alphabet, has a regular language. -/
example : (mem (Fin.last 0) (Fin.last 0) : Formula Bool 1 1).extLanguage.IsRegular :=
  isRegular_extLanguage _

/-- The extended word `[(true, x ↦ 1, X ↦ 1)]` marks position `0` as `x` and puts it in `X`, so it
satisfies `x ∈ X`. -/
example : [⟨true, fun _ => true, fun _ => true⟩] ∈
    (mem (Fin.last 0) (Fin.last 0) : Formula Bool 1 1).extLanguage :=
  mem_extLanguage.2 ⟨fun _ => 0, fun i x => by
    rw [Fin.fin_one_eq_zero i]
    exact ⟨fun _ => rfl, fun _ => rfl⟩, rfl⟩

/-- An extended word marking `x` twice is not in the extended language of any formula. -/
example (φ : Formula Bool 1 0) :
    [⟨true, fun _ => true, Fin.elim0⟩, ⟨true, fun _ => true, Fin.elim0⟩] ∉ φ.extLanguage := by
  rintro ⟨v, hv, -⟩
  have h0 := (hv ⟨0, by decide⟩ 0).1 rfl
  have h1 := (hv ⟨1, by decide⟩ 0).1 rfl
  exact absurd (h0.symm.trans h1) (by decide)

/-! ### Mathlib first-order sentences over the word vocabulary -/

section MathlibFO

open FirstOrder Language

/-- "Some position carries `true`", as a Mathlib sentence over the word vocabulary. -/
def someTrue : (wordLanguage Bool).Sentence :=
  ((wordLanguage.letterSymb true).boundedFormula₁ (Term.var (Sum.inr 0))).ex

theorem mem_someTrue (w : List Bool) :
    w ∈ WordFO.language someTrue ↔ ∃ i : Fin w.length, w[i] = true := by
  let := wordStructure w
  change BoundedFormula.Realize someTrue (default : Empty → Fin w.length) default ↔ _
  simp only [someTrue, BoundedFormula.realize_ex, BoundedFormula.realize_rel₁, Term.realize_var,
    Sum.elim_inr, wordStructure.relMap_letterSymb, Matrix.cons_val_fin_one, Fin.snoc_zero]

example : [false, true] ∈ WordFO.language someTrue :=
  (mem_someTrue _).2 ⟨1, rfl⟩

example : [false, false] ∉ WordFO.language someTrue := by
  rw [mem_someTrue]
  decide

example : FODefinable (WordFO.language someTrue) :=
  WordFO.foDefinable_language someTrue

example : (WordFO.language someTrue).IsRegular :=
  (WordFO.foDefinable_language someTrue).isRegular

/-- A first-order word sentence translates back to a Mathlib sentence with the same language. -/
example : ∃ φ : (wordLanguage Bool).Sentence,
    WordFO.language φ = trueBeforeFalse.language :=
  foDefinable_iff_exists_sentence.1 ⟨trueBeforeFalse, by simp [trueBeforeFalse], rfl⟩

end MathlibFO

/-! ### `FO[<] ⊊ MSO` -/

example : ¬ FODefinable {w : List Unit | Even w.length} :=
  not_foDefinable_even

example : ∃ L : Language Bool, Definable L ∧ ¬ FODefinable L :=
  exists_definable_not_foDefinable

example : ∃ L : Language ℕ, L.IsRegular ∧ ¬ FODefinable L :=
  exists_isRegular_not_foDefinable

example : ¬ ∃ φ : (wordLanguage Bool).Sentence,
    WordFO.language φ = {w : List Bool | Even w.length} :=
  not_exists_sentence_language_eq_even

/-- Over the empty alphabet the only word is `[]`, so even length is defined by `⊤`: the
hypothesis `Nonempty α` of `not_foDefinable_even` is needed. -/
example : FODefinable {w : List Empty | Even w.length} := by
  refine ⟨top, by simp, Set.ext fun w => ?_⟩
  match w with
  | [] => exact iff_of_true realize_top ⟨0, rfl⟩

end ComplexityTests.WordMSO
