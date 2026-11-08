/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.SecondOrder.WordMSO.Basic
public import Mathlib.ModelTheory.Semantics
import Complexity.Logics.FirstOrder.Interpretation

/-!
# First-order logic over words in Mathlib's model theory

The word vocabulary over an alphabet `α` as a Mathlib first-order language `wordLanguage α`: no
function symbols, a binary relation symbol `<`, and a unary relation symbol `P_a` for each letter
`a` [Libkin, Sections 1.3 and 7.4][Libkin2004]. `wordStructure w` interprets it on the positions
`Fin w.length` of a word `w`, with the natural order and `P_a = {i | w[i] = a}`.

The sentences of `wordLanguage α` define exactly the first-order definable languages of
`Cslib.Logic.WordMSO`. `WordFO.toFormula` translates a Mathlib formula into the first-order
fragment `Formula.IsFO`, and `Formula.toWordFO` translates a formula of that fragment back.
Equality, which is primitive in Mathlib's formulas, becomes the derived `Formula.eq`. So results
about `FODefinable`, such as the regularity of first-order definable languages, apply to Mathlib's
first-order sentences over words, and conversely.

## Main definitions

* `Cslib.Logic.WordMSO.wordLanguage`, `Cslib.Logic.WordMSO.wordStructure`: the word vocabulary and
  the word structure of a word; `wordLanguage.ltSymb` and `wordLanguage.letterSymb` are its
  relation symbols.
* `Cslib.Logic.WordMSO.WordFO.toFormula`: Mathlib formulas over the word vocabulary to word
  formulas.
* `Cslib.Logic.WordMSO.Formula.toWordFO`: first-order word formulas to Mathlib formulas.
* `Cslib.Logic.WordMSO.WordFO.language`: the language of a Mathlib sentence over the word
  vocabulary.

## Main results

* `Cslib.Logic.WordMSO.WordFO.realize_toFormula`, `Cslib.Logic.WordMSO.Formula.realize_toWordFO`:
  both translations preserve satisfaction.
* `Cslib.Logic.WordMSO.WordFO.foDefinable_language`: the language of a Mathlib sentence is
  first-order definable.
* `Cslib.Logic.WordMSO.foDefinable_iff_exists_sentence`: a language is first-order definable iff it
  is the language of a Mathlib sentence over the word vocabulary.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

open FirstOrder Language Structure

universe u

namespace Cslib.Logic.WordMSO

variable {α : Type u}

/-- Relation symbols of the word vocabulary over `α`: the binary order `<` and, for each letter
`a`, the unary letter predicate `P_a`. -/
inductive WordRel (α : Type u) : ℕ → Type u
  /-- The order `<` of positions. -/
  | lt : WordRel α 2
  /-- The letter predicate `P_a`. -/
  | letter (a : α) : WordRel α 1

/-- The first-order language of words over `α`: no function symbols, the order `<`, and `P_a` for
every letter `a`. -/
@[expose] def wordLanguage (α : Type u) : FirstOrder.Language.{0, u} where
  Functions := fun _ => Empty
  Relations := WordRel α

instance (n : ℕ) : IsEmpty ((wordLanguage α).Functions n) := inferInstanceAs (IsEmpty Empty)

/-- For finitely many letters, the word vocabulary has finitely many relation symbols. -/
instance [Finite α] : Finite (Σ l, (wordLanguage α).Relations l) :=
  Finite.of_surjective
    (fun o : Option α => o.elim (⟨2, WordRel.lt⟩ : Σ l, (wordLanguage α).Relations l)
      fun a => ⟨1, WordRel.letter a⟩)
    fun
      | ⟨_, .lt⟩ => ⟨none, rfl⟩
      | ⟨_, .letter a⟩ => ⟨some a, rfl⟩

namespace wordLanguage

/-- The relation symbol `<` of the word vocabulary. -/
@[expose] protected def ltSymb : (wordLanguage α).Relations 2 := WordRel.lt

/-- The relation symbol `P_a` of the word vocabulary. -/
@[expose] protected def letterSymb (a : α) : (wordLanguage α).Relations 1 := WordRel.letter a

end wordLanguage

/-- The word structure of `w`: the positions `Fin w.length`, their natural order, and
`P_a = {i | w[i] = a}`. It is not an instance, since the universe `Fin w.length` does not
determine `w`. -/
@[instance_reducible]
def wordStructure (w : List α) : (wordLanguage α).Structure (Fin w.length) where
  funMap := fun f => Empty.elim f
  RelMap := fun {n} R xs => match n, R with
    | _, .lt => xs 0 < xs 1
    | _, .letter a => w[xs 0] = a

namespace wordStructure

@[simp] theorem relMap_ltSymb (w : List α) (xs : Fin 2 → Fin w.length) :
    @RelMap _ _ (wordStructure w) _ wordLanguage.ltSymb xs ↔ xs 0 < xs 1 :=
  Iff.rfl

@[simp] theorem relMap_letterSymb (w : List α) (a : α) (xs : Fin 1 → Fin w.length) :
    @RelMap _ _ (wordStructure w) _ (wordLanguage.letterSymb a) xs ↔ w[xs 0] = a :=
  Iff.rfl

end wordStructure

namespace WordFO

/-- The word-formula variable of a variable of a Mathlib formula without free variables. -/
private def var {m : ℕ} (b : Empty ⊕ Fin m) : Fin m := Sum.elim Empty.elim id b

/-- The atomic word formula of a relation symbol applied to variables. -/
private def relFormula {m n : ℕ} :
    {l : ℕ} → (wordLanguage α).Relations l → (Fin l → Fin m) → Formula α m n
  | _, .lt, xs => .lt (xs 0) (xs 1)
  | _, .letter a, xs => .letter a (xs 0)

/-- Translation of a Mathlib formula over the word vocabulary, with no free variables and `m`
bound variables in scope, into a first-order word formula with `m` free position variables (and
any number of unused set variables). Relation symbols become atoms, and equality becomes the
derived `Formula.eq`. -/
def toFormula {n : ℕ} : {m : ℕ} → (wordLanguage α).BoundedFormula Empty m → Formula α m n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .eq (var (FO.termVar t₁)) (var (FO.termVar t₂))
  | _, .rel R ts => relFormula R fun i => var (FO.termVar (ts i))
  | _, .imp φ ψ => .imp (toFormula φ) (toFormula ψ)
  | _, .all φ => .all (toFormula φ)

/-- The translation lands in the first-order fragment. -/
theorem isFO_toFormula {n : ℕ} :
    ∀ {m : ℕ} (φ : (wordLanguage α).BoundedFormula Empty m), (toFormula φ : Formula α m n).IsFO
  | _, .falsum => by simp [toFormula]
  | _, .equal _ _ => by simp [toFormula]
  | _, .rel R _ => by cases R <;> simp [toFormula, relFormula]
  | _, .imp φ ψ => by simpa [toFormula] using ⟨isFO_toFormula φ, isFO_toFormula ψ⟩
  | _, .all φ => by simpa [toFormula] using isFO_toFormula φ

private theorem sumElim_eq_var {ℓ m : ℕ} (xs : Fin m → Fin ℓ) (b : Empty ⊕ Fin m) :
    Sum.elim (Empty.elim : Empty → Fin ℓ) xs b = xs (var b) := by
  rcases b with e | i
  exacts [e.elim, rfl]

/-- The translation preserves satisfaction: the word formula holds at an assignment of positions
iff the Mathlib formula holds in the word structure. -/
theorem realize_toFormula (w : List α) {n : ℕ} (V : Fin n → Set (Fin w.length)) :
    ∀ {m : ℕ} (φ : (wordLanguage α).BoundedFormula Empty m) (xs : Fin m → Fin w.length),
      (toFormula φ : Formula α m n).Realize (fun i : Fin w.length => w[i]) xs V ↔
        (let := wordStructure w; φ.Realize (Empty.elim : Empty → Fin w.length) xs)
  | _, .falsum, xs => Iff.rfl
  | _, .equal t₁ t₂, xs => by
    let := wordStructure w
    change _ ↔ t₁.realize (Sum.elim Empty.elim xs) = t₂.realize (Sum.elim Empty.elim xs)
    rw [FO.realize_termVar, FO.realize_termVar, sumElim_eq_var, sumElim_eq_var]
    simp only [toFormula, Formula.realize_eq]
  | _, .rel R ts, xs => by
    let := wordStructure w
    change _ ↔ RelMap R (fun i => (ts i).realize (Sum.elim Empty.elim xs))
    simp only [FO.realize_termVar, sumElim_eq_var]
    cases R with
    | lt => exact Iff.rfl
    | letter a => exact Iff.rfl
  | _, .imp φ ψ, xs => by
    simp only [toFormula, Formula.realize_imp, realize_toFormula w V φ xs,
      realize_toFormula w V ψ xs]
    exact Iff.rfl
  | _, .all φ, xs => by
    simp only [toFormula, Formula.realize_all, realize_toFormula w V φ]
    exact Iff.rfl

/-- The language of a Mathlib first-order sentence over the word vocabulary: the words whose word
structure satisfies it. -/
@[expose] def language (φ : (wordLanguage α).Sentence) : Language α :=
  {w | let := wordStructure w; Fin w.length ⊨ φ}

/-- A sentence and its translation define the same language. -/
theorem toFormula_language (φ : (wordLanguage α).Sentence) :
    Sentence.language (toFormula φ) = language φ := by
  refine Set.ext fun w => ?_
  have hdef : (default : Empty → Fin w.length) = Empty.elim := funext fun e => e.elim
  have hdef' : (default : Fin 0 → Fin w.length) = Fin.elim0 := funext fun x => x.elim0
  change (toFormula φ : Sentence α).Realize (fun i : Fin w.length => w[i]) Fin.elim0 Fin.elim0 ↔
    (let := wordStructure w;
      BoundedFormula.Realize φ (default : Empty → Fin w.length) default)
  rw [hdef, hdef']
  exact realize_toFormula w Fin.elim0 φ Fin.elim0

/-- The language of a Mathlib first-order sentence over the word vocabulary is first-order
definable. -/
theorem foDefinable_language (φ : (wordLanguage α).Sentence) : FODefinable (language φ) :=
  ⟨toFormula φ, isFO_toFormula φ, toFormula_language φ⟩

end WordFO

namespace Formula

/-- Translation of a word formula with `m` free position variables into a Mathlib formula over the
word vocabulary with `m` bound variables in scope. Set atoms and set quantifiers, which do not
occur in first-order formulas without free set variables, become `⊥`. -/
def toWordFO : {m n : ℕ} → Formula α m n → (wordLanguage α).BoundedFormula Empty m
  | _, _, letter a x => (wordLanguage.letterSymb a).boundedFormula₁ (Term.var (Sum.inr x))
  | _, _, lt x y =>
    wordLanguage.ltSymb.boundedFormula₂ (Term.var (Sum.inr x)) (Term.var (Sum.inr y))
  | _, _, mem _ _ => ⊥
  | _, _, falsum => ⊥
  | _, _, imp φ ψ => (toWordFO φ).imp (toWordFO ψ)
  | _, _, ex φ => (toWordFO φ).ex
  | _, _, exSet _ => ⊥

/-- The translation preserves satisfaction on first-order formulas without free set variables. -/
theorem realize_toWordFO (w : List α) :
    ∀ {m : ℕ} (φ : Formula α m 0), φ.IsFO →
      ∀ (xs : Fin m → Fin w.length) (V : Fin 0 → Set (Fin w.length)),
        ((let := wordStructure w; (toWordFO φ).Realize (Empty.elim : Empty → Fin w.length) xs) ↔
          φ.Realize (fun i : Fin w.length => w[i]) xs V)
  | _, letter a x, _, xs, V => Iff.rfl
  | _, lt x y, _, xs, V => Iff.rfl
  | _, mem _ X, _, _, _ => X.elim0
  | _, falsum, _, xs, V => Iff.rfl
  | _, imp φ ψ, h, xs, V => by
    let := wordStructure w
    simp only [toWordFO, BoundedFormula.realize_imp, realize_imp,
      ← realize_toWordFO w φ (isFO_imp.1 h).1 xs V, ← realize_toWordFO w ψ (isFO_imp.1 h).2 xs V]
  | _, ex φ, h, xs, V => by
    let := wordStructure w
    simp only [toWordFO, BoundedFormula.realize_ex, realize_ex]
    exact exists_congr fun i => realize_toWordFO w φ (isFO_ex.1 h) _ V
  | _, exSet _, h, _, _ => absurd h (not_isFO_exSet _)

/-- A first-order sentence and its translation define the same language. -/
theorem language_toWordFO {φ : Sentence α} (hφ : φ.IsFO) :
    WordFO.language (toWordFO φ) = φ.language := by
  refine Set.ext fun w => ?_
  have hdef : (default : Empty → Fin w.length) = Empty.elim := funext fun e => e.elim
  have hdef' : (default : Fin 0 → Fin w.length) = Fin.elim0 := funext fun x => x.elim0
  change (let := wordStructure w;
      BoundedFormula.Realize (toWordFO φ) (default : Empty → Fin w.length) default) ↔
    φ.Realize (fun i : Fin w.length => w[i]) Fin.elim0 Fin.elim0
  rw [hdef, hdef']
  exact realize_toWordFO w φ hφ Fin.elim0 Fin.elim0

end Formula

/-- **First-order definability in Mathlib's model theory.** A language is first-order definable iff
it is the language of a Mathlib first-order sentence over the word vocabulary. -/
theorem foDefinable_iff_exists_sentence {L : Language α} :
    FODefinable L ↔ ∃ φ : (wordLanguage α).Sentence, WordFO.language φ = L := by
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ.toWordFO, Formula.language_toWordFO hφ⟩
  · rintro ⟨φ, rfl⟩
    exact WordFO.foDefinable_language φ

end Cslib.Logic.WordMSO
