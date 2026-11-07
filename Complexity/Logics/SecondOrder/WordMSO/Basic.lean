/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Computability.Language
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Monadic second-order logic over words

Monadic second-order logic (MSO) over finite words with alphabet `α`
[Libkin, Section 7.4][Libkin2004], [Thomas, Section 3][Thomas1997]. A word `w` of length `ℓ` is the
structure with universe the positions `Fin ℓ`, their natural order `<`, and for each letter `a` the
unary predicate `P_a = {i | w i = a}`. Formulas have first-order variables ranging over positions
and monadic second-order (set) variables ranging over sets of positions, with atoms `P_a(x)`,
`x < y` and `x ∈ X`, the connectives `⊥` and `→`, and existential quantifiers over both sorts.

Variables are de Bruijn-style: `Formula α m n` has `m` free first-order and `n` free set
variables, indexed by `Fin m` and `Fin n`. As for Mathlib's `FirstOrder.Language.BoundedFormula`,
a quantifier binds the last index (`Fin.last`), so an assignment is extended with `Fin.snoc`. A
sentence is a formula without free variables, and defines the language of the words whose
structure satisfies it.

Unlike the existential second-order sentences of `Cslib.Logic.ESO` (one block of existential
relation quantifiers over a first-order matrix), MSO allows arbitrary nesting and alternation of
set quantifiers, restricted to unary relations.

## Main definitions

* `Cslib.Logic.WordMSO.Formula`, `Cslib.Logic.WordMSO.Formula.Realize`: formulas and their
  satisfaction in a word structure under assignments of the free variables.
* `Cslib.Logic.WordMSO.Formula.not`, `top`, `and`, `or`, `all`, `allSet`, `eq`, `iInf`, `iSup`:
  derived connectives, quantifiers, equality, and finite conjunctions and disjunctions.
* `Cslib.Logic.WordMSO.Formula.first`, `last`, `succ`: the first and last positions and the
  successor relation, defined from `<`.
* `Cslib.Logic.WordMSO.Formula.IsFO`: the first-order fragment, without set quantifiers.
* `Cslib.Logic.WordMSO.Sentence`, `Cslib.Logic.WordMSO.Sentence.language`: sentences and the
  language they define.
* `Cslib.Logic.WordMSO.Definable`, `Cslib.Logic.WordMSO.FODefinable`: MSO- and FO-definability
  of a language.

## Main results

* `Cslib.Logic.WordMSO.Formula.realize_and`, `realize_all`, `realize_eq`, `realize_iInf`, ...:
  semantics of the derived connectives.
* `Cslib.Logic.WordMSO.Formula.realize_first`, `realize_last`, `realize_succ`: semantics of the
  defined position predicates.
* `Cslib.Logic.WordMSO.Formula.isFO_and`, `isFO_all`, `not_isFO_exSet`, ...: the first-order
  fragment is closed under the derived first-order connectives and excludes set quantifiers.
* `Cslib.Logic.WordMSO.FODefinable.definable`: first-order definable languages are MSO-definable.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
* [W. Thomas, *Languages, automata, and logic*][Thomas1997]
-/

public section

universe u

namespace Cslib.Logic.WordMSO

/-- Formulas of monadic second-order logic over words with alphabet `α`, with `m` free
first-order (position) variables and `n` free monadic second-order (set) variables. Quantifiers
bind the last variable of their sort. -/
inductive Formula (α : Type u) : ℕ → ℕ → Type u where
  /-- `P_a(x)`: position `x` carries the letter `a`. -/
  | letter {m n : ℕ} (a : α) (x : Fin m) : Formula α m n
  /-- `x < y` in the order of positions. -/
  | lt {m n : ℕ} (x y : Fin m) : Formula α m n
  /-- `x ∈ X`: position `x` belongs to the set `X`. -/
  | mem {m n : ℕ} (x : Fin m) (X : Fin n) : Formula α m n
  /-- Falsity. -/
  | falsum {m n : ℕ} : Formula α m n
  /-- Implication. -/
  | imp {m n : ℕ} (φ ψ : Formula α m n) : Formula α m n
  /-- Existential quantification over positions, binding first-order variable `Fin.last m`. -/
  | ex {m n : ℕ} (φ : Formula α (m + 1) n) : Formula α m n
  /-- Existential quantification over sets of positions, binding set variable `Fin.last n`. -/
  | exSet {m n : ℕ} (φ : Formula α m (n + 1)) : Formula α m n

namespace Formula

variable {α : Type u}

/-- Satisfaction of a formula in the word structure with positions `Fin ℓ` and letters `w`, under
the assignment `v` of positions to the first-order variables and `V` of sets of positions to the
set variables. -/
@[expose] def Realize {ℓ : ℕ} (w : Fin ℓ → α) : {m n : ℕ} → Formula α m n →
    (Fin m → Fin ℓ) → (Fin n → Set (Fin ℓ)) → Prop
  | _, _, letter a x, v, _ => w (v x) = a
  | _, _, lt x y, v, _ => v x < v y
  | _, _, mem x X, v, V => v x ∈ V X
  | _, _, falsum, _, _ => False
  | _, _, imp φ ψ, v, V => Realize w φ v V → Realize w ψ v V
  | _, _, ex φ, v, V => ∃ i, Realize w φ (Fin.snoc v i) V
  | _, _, exSet φ, v, V => ∃ S, Realize w φ v (Fin.snoc V S)

variable {m n : ℕ}

/-- Negation. -/
def not (φ : Formula α m n) : Formula α m n := imp φ falsum

/-- Truth. -/
def top : Formula α m n := imp falsum falsum

/-- Conjunction. -/
def and (φ ψ : Formula α m n) : Formula α m n := not (imp φ (not ψ))

/-- Disjunction. -/
def or (φ ψ : Formula α m n) : Formula α m n := imp (not φ) ψ

/-- Universal quantification over positions. -/
def all (φ : Formula α (m + 1) n) : Formula α m n := not (ex (not φ))

/-- Universal quantification over sets of positions. -/
def allSet (φ : Formula α m (n + 1)) : Formula α m n := not (exSet (not φ))

/-- Equality of positions, defined from the order. -/
def eq (x y : Fin m) : Formula α m n := and (not (lt x y)) (not (lt y x))

/-- The conjunction of the formulas `φ i` for `i ∈ s`. -/
noncomputable def iInf {ι : Type*} (s : Finset ι) (φ : ι → Formula α m n) : Formula α m n :=
  (s.toList.map φ).foldr and top

/-- The disjunction of the formulas `φ i` for `i ∈ s`. -/
noncomputable def iSup {ι : Type*} (s : Finset ι) (φ : ι → Formula α m n) : Formula α m n :=
  (s.toList.map φ).foldr or falsum

/-- `x` is the first position: no position is below it. -/
def first (x : Fin m) : Formula α m n := all (not (lt (Fin.last m) x.castSucc))

/-- `x` is the last position: no position is above it. -/
def last (x : Fin m) : Formula α m n := all (not (lt x.castSucc (Fin.last m)))

/-- `y` is the successor of `x`: `x < y` and no position lies strictly between them. -/
def succ (x y : Fin m) : Formula α m n :=
  and (lt x y) (all (not (and (lt x.castSucc (Fin.last m)) (lt (Fin.last m) y.castSucc))))

/-- The first-order fragment: formulas without set quantifiers. -/
def IsFO : {m n : ℕ} → Formula α m n → Prop
  | _, _, letter _ _ => True
  | _, _, lt _ _ => True
  | _, _, mem _ _ => True
  | _, _, falsum => True
  | _, _, imp φ ψ => IsFO φ ∧ IsFO ψ
  | _, _, ex φ => IsFO φ
  | _, _, exSet _ => False

section Realize

variable {ℓ : ℕ} {w : Fin ℓ → α} {v : Fin m → Fin ℓ} {V : Fin n → Set (Fin ℓ)}

@[simp] theorem realize_letter (a : α) (x : Fin m) :
    (letter a x : Formula α m n).Realize w v V ↔ w (v x) = a := Iff.rfl

@[simp] theorem realize_lt (x y : Fin m) :
    (lt x y : Formula α m n).Realize w v V ↔ v x < v y := Iff.rfl

@[simp] theorem realize_mem (x : Fin m) (X : Fin n) :
    (mem x X : Formula α m n).Realize w v V ↔ v x ∈ V X := Iff.rfl

@[simp] theorem realize_falsum : (falsum : Formula α m n).Realize w v V ↔ False := Iff.rfl

@[simp] theorem realize_imp {φ ψ : Formula α m n} :
    (imp φ ψ).Realize w v V ↔ (φ.Realize w v V → ψ.Realize w v V) := Iff.rfl

@[simp] theorem realize_ex {φ : Formula α (m + 1) n} :
    (ex φ).Realize w v V ↔ ∃ i, φ.Realize w (Fin.snoc v i) V := Iff.rfl

@[simp] theorem realize_exSet {φ : Formula α m (n + 1)} :
    (exSet φ).Realize w v V ↔ ∃ S, φ.Realize w v (Fin.snoc V S) := Iff.rfl

@[simp] theorem realize_not {φ : Formula α m n} :
    (not φ).Realize w v V ↔ ¬ φ.Realize w v V := Iff.rfl

@[simp] theorem realize_top : (top : Formula α m n).Realize w v V := fun h => h

@[simp] theorem realize_and {φ ψ : Formula α m n} :
    (and φ ψ).Realize w v V ↔ φ.Realize w v V ∧ ψ.Realize w v V := by
  simp only [and, realize_not, realize_imp]
  tauto

@[simp] theorem realize_or {φ ψ : Formula α m n} :
    (or φ ψ).Realize w v V ↔ φ.Realize w v V ∨ ψ.Realize w v V := by
  simp only [or, realize_not, realize_imp]
  tauto

@[simp] theorem realize_all {φ : Formula α (m + 1) n} :
    (all φ).Realize w v V ↔ ∀ i, φ.Realize w (Fin.snoc v i) V := by
  simp only [all, realize_not, realize_ex, not_exists, not_not]

@[simp] theorem realize_allSet {φ : Formula α m (n + 1)} :
    (allSet φ).Realize w v V ↔ ∀ S, φ.Realize w v (Fin.snoc V S) := by
  simp only [allSet, realize_not, realize_exSet, not_exists, not_not]

@[simp] theorem realize_eq (x y : Fin m) :
    (eq x y : Formula α m n).Realize w v V ↔ v x = v y := by
  simp only [eq, realize_and, realize_not, realize_lt, not_lt]
  exact ⟨fun ⟨h₁, h₂⟩ => le_antisymm h₂ h₁, fun h => ⟨h.ge, h.le⟩⟩

private theorem realize_foldr_and (l : List (Formula α m n)) :
    (l.foldr and top).Realize w v V ↔ ∀ φ ∈ l, φ.Realize w v V := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

private theorem realize_foldr_or (l : List (Formula α m n)) :
    (l.foldr or falsum).Realize w v V ↔ ∃ φ ∈ l, φ.Realize w v V := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp] theorem realize_iInf {ι : Type*} (s : Finset ι) (φ : ι → Formula α m n) :
    (iInf s φ).Realize w v V ↔ ∀ i ∈ s, (φ i).Realize w v V := by
  simp [iInf, realize_foldr_and]

@[simp] theorem realize_iSup {ι : Type*} (s : Finset ι) (φ : ι → Formula α m n) :
    (iSup s φ).Realize w v V ↔ ∃ i ∈ s, (φ i).Realize w v V := by
  simp [iSup, realize_foldr_or]

@[simp] theorem realize_first (x : Fin m) :
    (first x : Formula α m n).Realize w v V ↔ (v x : ℕ) = 0 := by
  simp only [first, realize_all, realize_not, realize_lt, Fin.snoc_last, Fin.snoc_castSucc,
    not_lt, Fin.le_def]
  constructor
  · intro h
    have := h ⟨0, Fin.pos (v x)⟩
    simp only at this
    omega
  · intro h i
    omega

@[simp] theorem realize_last (x : Fin m) :
    (last x : Formula α m n).Realize w v V ↔ (v x : ℕ) + 1 = ℓ := by
  simp only [last, realize_all, realize_not, realize_lt, Fin.snoc_last, Fin.snoc_castSucc,
    not_lt, Fin.le_def]
  have hx := (v x).isLt
  constructor
  · intro h
    by_contra hne
    have := h ⟨v x + 1, by omega⟩
    simp only at this
    omega
  · intro h i
    have := i.isLt
    omega

@[simp] theorem realize_succ (x y : Fin m) :
    (succ x y : Formula α m n).Realize w v V ↔ (v y : ℕ) = v x + 1 := by
  simp only [succ, realize_and, realize_lt, realize_all, realize_not, Fin.snoc_last,
    Fin.snoc_castSucc, Fin.lt_def]
  have hy := (v y).isLt
  constructor
  · rintro ⟨hxy, h⟩
    by_contra hne
    exact h ⟨v x + 1, by omega⟩ ⟨by simp, by simp only; omega⟩
  · intro h
    exact ⟨by omega, fun i ⟨h₁, h₂⟩ => by omega⟩

end Realize

section IsFO

@[simp] theorem isFO_letter (a : α) (x : Fin m) : (letter a x : Formula α m n).IsFO := trivial

@[simp] theorem isFO_lt (x y : Fin m) : (lt x y : Formula α m n).IsFO := trivial

@[simp] theorem isFO_mem (x : Fin m) (X : Fin n) : (mem x X : Formula α m n).IsFO := trivial

@[simp] theorem isFO_falsum : (falsum : Formula α m n).IsFO := trivial

@[simp] theorem isFO_imp {φ ψ : Formula α m n} : (imp φ ψ).IsFO ↔ φ.IsFO ∧ ψ.IsFO := Iff.rfl

@[simp] theorem isFO_ex {φ : Formula α (m + 1) n} : (ex φ).IsFO ↔ φ.IsFO := Iff.rfl

@[simp] theorem not_isFO_exSet (φ : Formula α m (n + 1)) : ¬ (exSet φ).IsFO := id

@[simp] theorem isFO_not {φ : Formula α m n} : (not φ).IsFO ↔ φ.IsFO := by
  simp only [not, isFO_imp, isFO_falsum, and_true]

@[simp] theorem isFO_top : (top : Formula α m n).IsFO := ⟨trivial, trivial⟩

@[simp] theorem isFO_and {φ ψ : Formula α m n} : (and φ ψ).IsFO ↔ φ.IsFO ∧ ψ.IsFO := by
  simp only [and, isFO_not, isFO_imp]

@[simp] theorem isFO_or {φ ψ : Formula α m n} : (or φ ψ).IsFO ↔ φ.IsFO ∧ ψ.IsFO := by
  simp only [or, isFO_not, isFO_imp]

@[simp] theorem isFO_all {φ : Formula α (m + 1) n} : (all φ).IsFO ↔ φ.IsFO := by
  simp only [all, isFO_not, isFO_ex]

@[simp] theorem isFO_eq (x y : Fin m) : (eq x y : Formula α m n).IsFO := by
  simp only [eq, isFO_and, isFO_not, isFO_lt, and_self]

@[simp] theorem isFO_first (x : Fin m) : (first x : Formula α m n).IsFO := by
  simp only [first, isFO_all, isFO_not, isFO_lt]

@[simp] theorem isFO_last (x : Fin m) : (last x : Formula α m n).IsFO := by
  simp only [last, isFO_all, isFO_not, isFO_lt]

@[simp] theorem isFO_succ (x y : Fin m) : (succ x y : Formula α m n).IsFO := by
  simp only [succ, isFO_and, isFO_all, isFO_not, isFO_lt, and_self]

end IsFO

end Formula

/-- An MSO sentence over the alphabet `α`: a formula without free variables. -/
abbrev Sentence (α : Type u) := Formula α 0 0

/-- The language defined by a sentence: the words whose word structure satisfies it. -/
@[expose] def Sentence.language {α : Type u} (φ : Sentence α) : Language α :=
  {w | φ.Realize (fun i : Fin w.length => w[i]) Fin.elim0 Fin.elim0}

/-- A language is **MSO-definable** when it is the language of some MSO sentence. -/
@[expose] def Definable {α : Type u} (L : Language α) : Prop :=
  ∃ φ : Sentence α, φ.language = L

/-- A language is **first-order definable** (in `FO[<]` with letter predicates) when it is the
language of some sentence without set quantifiers. -/
@[expose] def FODefinable {α : Type u} (L : Language α) : Prop :=
  ∃ φ : Sentence α, φ.IsFO ∧ φ.language = L

/-- First-order definable languages are MSO-definable. -/
theorem FODefinable.definable {α : Type u} {L : Language α} (h : FODefinable L) :
    Definable L :=
  let ⟨φ, _, hφ⟩ := h
  ⟨φ, hφ⟩

end Cslib.Logic.WordMSO
