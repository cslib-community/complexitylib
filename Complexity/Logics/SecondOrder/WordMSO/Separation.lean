/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder
public import Complexity.Logics.SecondOrder.WordMSO.FirstOrder
public import Complexity.Logics.SecondOrder.WordMSO.OfRegular

/-!
# First-order logic is strictly weaker than MSO over words

The language of even-length words is MSO-definable (`definable_even`) and regular, but not
first-order definable over any nonempty alphabet, so `FO[<] ⊊ MSO` over finite words. Over a
one-letter alphabet `{a}` the language is `(aa)*`, and this is Libkin's Corollary 7.27
[Libkin2004]: `(aa)*` is regular but not star-free, that is, not first-order definable by
Theorem 7.26 there. Over larger alphabets it is the same statement for `(ΣΣ)*`, with the same
proof. The proof follows Libkin's: on a word whose letters
are all equal to `c`, a first-order word formula is equivalent to a sentence of Mathlib's language
of orders (`Formula.toOrder`, with `P_c` true and every other letter predicate false), so EVEN would
be first-order definable on finite linear orders. That contradicts the Ehrenfeucht–Fraïssé bound for
finite linear orders [Libkin, Theorem 3.6 and Corollary 3.12][Libkin2004], which is
`Cslib.Logic.FO.FiniteLinearOrder.realize_iff_of_two_pow_le_card`. The library's version is applied
to the orders of sizes `2 ^ k` and `2 ^ k + 1`, where `k` is the quantifier rank of the translated
sentence.

Nonemptiness of the alphabet is needed: over the empty alphabet the only word is the empty word, so
every language is first-order definable (by `⊤` or `⊥`).

## Main definitions

* `Cslib.Logic.WordMSO.Formula.toOrder`: a word formula as a formula of Mathlib's language of
  orders, for words with all letters equal to a fixed letter.

## Main results

* `Cslib.Logic.WordMSO.Formula.realize_toOrder`: on a word with all letters equal, a first-order
  word formula and its translation agree.
* `Cslib.Logic.WordMSO.not_foDefinable_even`: even length is not first-order definable.
* `Cslib.Logic.WordMSO.exists_definable_not_foDefinable`: `FO[<] ⊊ MSO` over words.
* `Cslib.Logic.WordMSO.exists_isRegular_not_foDefinable`: some regular language is not first-order
  definable.
* `Cslib.Logic.WordMSO.not_exists_sentence_language_eq_even`: the separation for Mathlib's
  first-order sentences over the word vocabulary.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

open FirstOrder Language Structure

universe u

namespace Cslib.Logic.WordMSO

variable {α : Type u}

namespace Formula

/-- Translation of a word formula into Mathlib's language of orders, for words all of whose letters
are `c`: `P_c(x)` becomes `⊤` and every other letter predicate `⊥`. Set atoms and set quantifiers,
which do not occur in first-order formulas without free set variables, become `⊥`. -/
noncomputable def toOrder (c : α) : {m n : ℕ} → Formula α m n →
    Language.order.BoundedFormula Empty m
  | _, _, letter a _ => by classical exact if a = c then ⊤ else ⊥
  | _, _, lt x y => Term.lt (Term.var (Sum.inr x)) (Term.var (Sum.inr y))
  | _, _, mem _ _ => ⊥
  | _, _, falsum => ⊥
  | _, _, imp φ ψ => (toOrder c φ).imp (toOrder c ψ)
  | _, _, ex φ => (toOrder c φ).ex
  | _, _, exSet _ => ⊥

/-- On a word all of whose letters are `c`, with positions ordered by an ordered structure for
Mathlib's language of orders, a first-order word formula without free set variables holds iff its
translation `toOrder c` does. -/
theorem realize_toOrder {ℓ : ℕ} [Language.order.Structure (Fin ℓ)]
    [Language.order.OrderedStructure (Fin ℓ)] (c : α) (w : Fin ℓ → α) (hw : ∀ i, w i = c) :
    ∀ {m : ℕ} (φ : Formula α m 0), φ.IsFO → ∀ (v : Fin m → Fin ℓ) (V : Fin 0 → Set (Fin ℓ)),
      ((toOrder c φ).Realize (Empty.elim : Empty → Fin ℓ) v ↔ φ.Realize w v V)
  | _, letter a x, _, v, V => by
    classical
    simp only [toOrder, realize_letter, hw]
    split_ifs with h
    · simp only [BoundedFormula.realize_top, h]
    · simp only [BoundedFormula.realize_bot, false_iff]
      exact fun h' => h h'.symm
  | _, lt x y, _, v, V => by
    simp only [toOrder, Term.realize_lt, Term.realize_var, Sum.elim_inr, realize_lt]
  | _, mem _ X, _, _, _ => X.elim0
  | _, falsum, _, v, V => by
    simp only [toOrder, BoundedFormula.realize_bot, realize_falsum]
  | _, imp φ ψ, h, v, V => by
    simp only [toOrder, BoundedFormula.realize_imp, realize_imp,
      realize_toOrder c w hw φ (isFO_imp.1 h).1 v V,
      realize_toOrder c w hw ψ (isFO_imp.1 h).2 v V]
  | _, ex φ, h, v, V => by
    simp only [toOrder, BoundedFormula.realize_ex, realize_ex]
    exact exists_congr fun i => realize_toOrder c w hw φ (isFO_ex.1 h) _ V
  | _, exSet _, h, _, _ => absurd h (not_isFO_exSet _)

end Formula

/-- **Even length is not first-order definable** (in `FO[<]` with letter predicates), over any
nonempty alphabet. Over a one-letter alphabet this is `(aa)*` [Libkin, Corollary 7.27][Libkin2004].
-/
theorem not_foDefinable_even [Nonempty α] : ¬ FODefinable {w : List α | Even w.length} := by
  classical
  rintro ⟨φ, hFO, hφ⟩
  obtain ⟨c⟩ := ‹Nonempty α›
  let ψ : Language.order.Sentence := φ.toOrder c
  -- On a word all of whose letters are `c`, `φ` and `ψ` agree, so `ψ` holds in the order
  -- `Fin w.length` iff the length is even.
  have key : ∀ w : List α, (∀ a ∈ w, a = c) →
      ((let := orderStructure (Fin w.length); Fin w.length ⊨ ψ) ↔ Even w.length) := by
    intro w hw
    let := orderStructure (Fin w.length)
    have : Language.order.OrderedStructure (Fin w.length) := ⟨fun _ => Iff.rfl⟩
    have h1 : w ∈ φ.language ↔ Even w.length := by rw [hφ]; exact Iff.rfl
    rw [← h1]
    have hdef : (default : Empty → Fin w.length) = Empty.elim := funext fun e => e.elim
    have hdef' : (default : Fin 0 → Fin w.length) = Fin.elim0 := funext fun x => x.elim0
    change (φ.toOrder c).Realize (default : Empty → Fin w.length)
      (default : Fin 0 → Fin w.length) ↔
        φ.Realize (fun i : Fin w.length => w[i]) Fin.elim0 Fin.elim0
    rw [hdef, hdef']
    exact Formula.realize_toOrder c _ (fun i => hw _ (List.getElem_mem _)) φ hFO Fin.elim0
      Fin.elim0
  -- The orders of sizes `2 ^ k` and `2 ^ k + 1` agree on `ψ` (Ehrenfeucht–Fraïssé).
  let k := FO.quantifierRank ψ
  let w₁ := List.replicate (2 ^ k) c
  let w₂ := List.replicate (2 ^ k + 1) c
  let := orderStructure (Fin w₁.length)
  let := orderStructure (Fin w₂.length)
  have : Language.order.OrderedStructure (Fin w₁.length) := ⟨fun _ => Iff.rfl⟩
  have : Language.order.OrderedStructure (Fin w₂.length) := ⟨fun _ => Iff.rfl⟩
  have h := FO.FiniteLinearOrder.realize_iff_of_two_pow_le_card (M := Fin w₁.length)
    (N := Fin w₂.length) (by simp [w₁]) (by simp [w₂]; omega) (le_refl k)
  have k₁ := key w₁ fun a ha => List.eq_of_mem_replicate ha
  have k₂ := key w₂ fun a ha => List.eq_of_mem_replicate ha
  rw [k₁, k₂] at h
  simp only [w₁, w₂, List.length_replicate, Nat.even_add_one] at h
  exact iff_not_self h

/-- **`FO[<] ⊊ MSO` over finite words**: over any nonempty alphabet, some MSO-definable language
(even length) is not first-order definable. -/
theorem exists_definable_not_foDefinable [Nonempty α] :
    ∃ L : Language α, Definable L ∧ ¬ FODefinable L :=
  ⟨_, definable_even, not_foDefinable_even⟩

/-- Over any nonempty alphabet, some regular language (even length) is not first-order
definable. -/
theorem exists_isRegular_not_foDefinable [Nonempty α] :
    ∃ L : Language α, L.IsRegular ∧ ¬ FODefinable L :=
  ⟨_, definable_even.isRegular, not_foDefinable_even⟩

/-- **Even length is not definable by a Mathlib first-order sentence** over the word vocabulary
(with `<` and letter predicates), over any nonempty alphabet. -/
theorem not_exists_sentence_language_eq_even [Nonempty α] :
    ¬ ∃ φ : (wordLanguage α).Sentence, WordFO.language φ = {w : List α | Even w.length} :=
  fun h => not_foDefinable_even (foDefinable_iff_exists_sentence.2 h)

end Cslib.Logic.WordMSO
