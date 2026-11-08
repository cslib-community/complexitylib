/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Languages.RegularLanguage

/-!
# Star-free languages

A star-free expression is built from `∅` and single letters by union, complement and
concatenation [Libkin, Definition 7.25][Libkin2004], with complement taken relative to all words
`List α`. A language is star-free when some star-free expression denotes it. Star-free languages
are regular, by the closure properties of regular languages.

Libkin works over a finite alphabet [Libkin, Section 7.4][Libkin2004]. This file allows an
arbitrary alphabet, where the finiteness matters: `{ε}` is star-free exactly when the alphabet is
finite (`isStarFree_one_iff`). Over a finite alphabet `{ε}` is the complement of `⊤ · Σ`; over an
infinite alphabet some letter `c` does not occur in a given expression, and on the words `cⁿ` the
expression's language is all or nothing.

Other presentations start from `∅`, `{ε}` and the letters, or from all finite languages. Over a
finite alphabet they define the same class, because `{ε}` and every finite language are star-free
in the sense above (`IsStarFree.one`, `IsStarFree.of_finite`).

## Main definitions

* `Cslib.Language.StarFreeExpression`: star-free expressions.
* `Cslib.Language.StarFreeExpression.matches'`: the language denoted by an expression.
* `Cslib.Language.IsStarFree`: some star-free expression denotes the language.

## Main results

* `Cslib.Language.StarFreeExpression.isRegular_matches'`, `Cslib.Language.IsStarFree.isRegular`:
  star-free languages are regular.
* `Cslib.Language.IsStarFree.zero`, `char`, `add`, `compl`, `mul`, `top`, `inf`, `iSup`, `iInf`:
  closure properties, the last two for finite unions and intersections.
* `Cslib.Language.IsStarFree.one`, `Cslib.Language.IsStarFree.singleton`,
  `Cslib.Language.IsStarFree.of_finite`: over a finite alphabet, `{ε}`, every one-word language
  and every finite language are star-free.
* `Cslib.Language.isStarFree_one_iff`: `{ε}` is star-free if and only if the alphabet is finite.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

universe u

namespace Cslib.Language

variable {α : Type u}

/-- Star-free expressions over the alphabet `α` [Libkin, Definition 7.25][Libkin2004]. -/
inductive StarFreeExpression (α : Type u) : Type u
  /-- The empty language `∅`. -/
  | zero : StarFreeExpression α
  /-- The language `{a}` of the one-letter word `a`. -/
  | char : α → StarFreeExpression α
  /-- Union. -/
  | plus : StarFreeExpression α → StarFreeExpression α → StarFreeExpression α
  /-- Complement, relative to all words. -/
  | compl : StarFreeExpression α → StarFreeExpression α
  /-- Concatenation. -/
  | comp : StarFreeExpression α → StarFreeExpression α → StarFreeExpression α

namespace StarFreeExpression

/-- The language denoted by a star-free expression. -/
@[expose] def matches' : StarFreeExpression α → _root_.Language α
  | zero => 0
  | char a => {[a]}
  | plus e f => e.matches' + f.matches'
  | compl e => (e.matches')ᶜ
  | comp e f => e.matches' * f.matches'

@[simp] theorem matches'_zero : (zero : StarFreeExpression α).matches' = 0 := rfl

@[simp] theorem matches'_char (a : α) : (char a).matches' = {[a]} := rfl

@[simp] theorem matches'_plus (e f : StarFreeExpression α) :
    (plus e f).matches' = e.matches' + f.matches' := rfl

@[simp] theorem matches'_compl (e : StarFreeExpression α) :
    (compl e).matches' = (e.matches')ᶜ := rfl

@[simp] theorem matches'_comp (e f : StarFreeExpression α) :
    (comp e f).matches' = e.matches' * f.matches' := rfl

/-- Whether the empty word belongs to the language of an expression, computed structurally. -/
def matchEpsilon : StarFreeExpression α → Bool
  | zero => false
  | char _ => false
  | plus e f => e.matchEpsilon || f.matchEpsilon
  | compl e => !e.matchEpsilon
  | comp e f => e.matchEpsilon && f.matchEpsilon

theorem matchEpsilon_iff : ∀ e : StarFreeExpression α, e.matchEpsilon = true ↔ [] ∈ e.matches'
  | zero => by
    simp only [matchEpsilon, matches'_zero, Bool.false_eq_true, false_iff]
    exact Language.notMem_zero _
  | char a => by simp [matchEpsilon]
  | plus e f => by
    simp only [matchEpsilon, Bool.or_eq_true, matches'_plus, Language.mem_add, matchEpsilon_iff e,
      matchEpsilon_iff f]
  | compl e => by
    simp only [matchEpsilon, Bool.not_eq_true', matches'_compl]
    rw [← Bool.not_eq_true, matchEpsilon_iff e]
    exact Iff.rfl
  | comp e f => by
    simp only [matchEpsilon, Bool.and_eq_true, matches'_comp, Language.mem_mul, matchEpsilon_iff e,
      matchEpsilon_iff f]
    constructor
    · rintro ⟨he, hf⟩
      exact ⟨[], he, [], hf, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hab
      exact ⟨ha, hb⟩

/-- The language of a star-free expression is regular. -/
theorem isRegular_matches' : ∀ e : StarFreeExpression α, e.matches'.IsRegular
  | zero => IsRegular.zero
  | char a => IsRegular.char a
  | plus e f => IsRegular.add (isRegular_matches' e) (isRegular_matches' f)
  | compl e => IsRegular.compl (isRegular_matches' e)
  | comp e f => IsRegular.mul (isRegular_matches' e) (isRegular_matches' f)

/-- The letters occurring in an expression. -/
def letters : StarFreeExpression α → Set α
  | zero => ∅
  | char a => {a}
  | plus e f => e.letters ∪ f.letters
  | compl e => e.letters
  | comp e f => e.letters ∪ f.letters

theorem letters_finite : ∀ e : StarFreeExpression α, e.letters.Finite
  | zero => Set.finite_empty
  | char a => Set.finite_singleton a
  | plus e f => (letters_finite e).union (letters_finite f)
  | compl e => letters_finite e
  | comp e f => (letters_finite e).union (letters_finite f)

/-- On the words `cⁿ` over a letter `c` that does not occur in `e`, the language of `e` is all or
nothing. -/
theorem replicate_mem_or_notMem {c : α} : ∀ e : StarFreeExpression α, c ∉ e.letters →
    (∀ n, List.replicate n c ∈ e.matches') ∨ (∀ n, List.replicate n c ∉ e.matches')
  | zero, _ => .inr fun n => Language.notMem_zero _
  | char a, hc => .inr fun n h => hc (List.eq_of_mem_replicate (by
      change List.replicate n c = [a] at h
      exact h ▸ List.mem_singleton_self a)).symm
  | plus e f, hc => by
    simp only [letters, Set.mem_union, not_or] at hc
    simp only [matches'_plus, Language.mem_add]
    rcases replicate_mem_or_notMem e hc.1 with he | he <;>
      rcases replicate_mem_or_notMem f hc.2 with hf | hf
    exacts [.inl fun n => .inl (he n), .inl fun n => .inl (he n), .inl fun n => .inr (hf n),
      .inr fun n h => h.elim (he n) (hf n)]
  | compl e, hc => by
    simp only [matches'_compl]
    rcases replicate_mem_or_notMem e hc with he | he
    exacts [.inr fun n h => h (he n), .inl fun n h => he n h]
  | comp e f, hc => by
    simp only [letters, Set.mem_union, not_or] at hc
    simp only [matches'_comp]
    rcases replicate_mem_or_notMem e hc.1 with he | he
    · rcases replicate_mem_or_notMem f hc.2 with hf | hf
      · exact .inl fun n => Language.mem_mul.2 ⟨[], he 0, _, hf n, List.nil_append _⟩
      · refine .inr fun n h => ?_
        obtain ⟨x, -, y, hy, hxy⟩ := Language.mem_mul.1 h
        obtain ⟨-, -, hy'⟩ := List.append_eq_replicate_iff.1 hxy
        exact hf _ (hy' ▸ hy)
    · refine .inr fun n h => ?_
      obtain ⟨x, hx, y, -, hxy⟩ := Language.mem_mul.1 h
      obtain ⟨-, hx', -⟩ := List.append_eq_replicate_iff.1 hxy
      exact he _ (hx' ▸ hx)

end StarFreeExpression

/-- A language is **star-free** when some star-free expression denotes it
[Libkin, Definition 7.25][Libkin2004]. -/
@[expose] def IsStarFree (L : _root_.Language α) : Prop :=
  ∃ e : StarFreeExpression α, e.matches' = L

namespace IsStarFree

theorem zero : IsStarFree (0 : _root_.Language α) := ⟨.zero, rfl⟩

theorem char (a : α) : IsStarFree ({[a]} : _root_.Language α) := ⟨.char a, rfl⟩

theorem add {L M : _root_.Language α} (hL : IsStarFree L) (hM : IsStarFree M) :
    IsStarFree (L + M) :=
  let ⟨e, he⟩ := hL
  let ⟨f, hf⟩ := hM
  ⟨.plus e f, by rw [StarFreeExpression.matches'_plus, he, hf]⟩

theorem compl {L : _root_.Language α} (hL : IsStarFree L) : IsStarFree Lᶜ :=
  let ⟨e, he⟩ := hL
  ⟨.compl e, by rw [StarFreeExpression.matches'_compl, he]⟩

theorem mul {L M : _root_.Language α} (hL : IsStarFree L) (hM : IsStarFree M) :
    IsStarFree (L * M) :=
  let ⟨e, he⟩ := hL
  let ⟨f, hf⟩ := hM
  ⟨.comp e f, by rw [StarFreeExpression.matches'_comp, he, hf]⟩

/-- All words form a star-free language, the complement of `∅`. -/
theorem top : IsStarFree (⊤ : _root_.Language α) := by
  have h : (0 : _root_.Language α)ᶜ = ⊤ := by
    ext x
    exact iff_of_true (Language.notMem_zero x) trivial
  exact h ▸ zero.compl

theorem inf {L M : _root_.Language α} (hL : IsStarFree L) (hM : IsStarFree M) :
    IsStarFree (L ⊓ M) := by
  have h : (Lᶜ + Mᶜ)ᶜ = L ⊓ M := by
    ext x
    constructor
    · intro hx
      exact ⟨by_contra fun h => hx ((Language.mem_add _ _ x).2 (.inl h)),
        by_contra fun h => hx ((Language.mem_add _ _ x).2 (.inr h))⟩
    · rintro ⟨hL, hM⟩ hx
      rcases (Language.mem_add _ _ x).1 hx with h | h
      exacts [h hL, h hM]
  exact h ▸ (hL.compl.add hM.compl).compl

/-- A finite union of star-free languages is star-free. -/
theorem iSup {ι : Type*} [Finite ι] {L : ι → _root_.Language α} (hL : ∀ i, IsStarFree (L i)) :
    IsStarFree (⨆ i, L i) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, IsStarFree (s.sup L) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact zero
    | insert i s _ ih =>
      rw [Finset.sup_insert]
      exact (hL i).add ih
  rw [← Finset.sup_univ_eq_iSup]
  exact key Finset.univ

/-- A finite intersection of star-free languages is star-free. -/
theorem iInf {ι : Type*} [Finite ι] {L : ι → _root_.Language α} (hL : ∀ i, IsStarFree (L i)) :
    IsStarFree (⨅ i, L i) := by
  rw [← compl_compl (⨅ i, L i), compl_iInf]
  exact (IsStarFree.iSup fun i => (hL i).compl).compl

/-- Star-free languages are regular. -/
theorem isRegular {L : _root_.Language α} (h : IsStarFree L) : L.IsRegular :=
  let ⟨e, he⟩ := h
  he ▸ e.isRegular_matches'

/-- Over a finite alphabet, the words of length one form a star-free language, the finite union
of the letters. -/
theorem setOf_length_eq_one [Finite α] : IsStarFree {w : List α | w.length = 1} := by
  have := Fintype.ofFinite α
  classical
  have key : ∀ s : Finset α, IsStarFree {w : List α | ∃ a ∈ s, w = [a]} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine cast (congrArg IsStarFree ?_) zero
      ext w
      exact iff_of_false (Language.notMem_zero w) fun ⟨b, hb, _⟩ => Finset.notMem_empty b hb
    | insert a s _ ih =>
      refine cast (congrArg IsStarFree ?_) ((char a).add ih)
      ext w
      refine (Language.mem_add _ _ w).trans ?_
      change w = [a] ∨ (∃ b ∈ s, w = [b]) ↔ ∃ b ∈ insert a s, w = [b]
      simp [or_and_right, exists_or]
  refine cast (congrArg IsStarFree ?_) (key Finset.univ)
  ext w
  simp [List.length_eq_one_iff]

/-- Over a finite alphabet, `{ε}` is star-free: it is the complement of `⊤ · Σ`. -/
theorem one [Finite α] : IsStarFree (1 : _root_.Language α) := by
  refine cast (congrArg IsStarFree ?_) (top.mul (setOf_length_eq_one (α := α))).compl
  ext w
  rw [Language.mem_one]
  constructor
  · intro h
    rcases List.eq_nil_or_concat w with hw | ⟨x, b, rfl⟩
    · exact hw
    · exact (h (Language.mem_mul.2 ⟨x, trivial, [b], rfl, List.concat_eq_append.symm⟩)).elim
  · rintro rfl h
    obtain ⟨x, -, y, hy, hxy⟩ := Language.mem_mul.1 h
    have := congrArg List.length hxy
    simp only [List.length_append, List.length_nil] at this
    change y.length = 1 at hy
    omega

/-- Over a finite alphabet, every one-word language `{w}` is star-free: `{ε}` is, and
`{a :: w} = {a} · {w}`. -/
theorem singleton [Finite α] (w : List α) : IsStarFree ({w} : _root_.Language α) := by
  induction w with
  | nil => exact one
  | cons a w ih =>
    refine cast (congrArg IsStarFree ?_) ((char a).mul ih)
    ext u
    rw [Language.mem_mul]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      change x = [a] at hx
      change y = w at hy
      subst hx hy
      rfl
    · intro hu
      change u = a :: w at hu
      exact ⟨[a], rfl, w, rfl, hu.symm⟩

/-- Over a finite alphabet, every finite language is star-free, as a finite union of one-word
languages. -/
theorem of_finite [Finite α] {L : _root_.Language α} (hL : Set.Finite (L : Set (List α))) :
    IsStarFree L := by
  classical
  have key : ∀ s : Finset (List α), IsStarFree {w : List α | w ∈ s} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine cast (congrArg IsStarFree ?_) zero
      ext w
      exact iff_of_false (Language.notMem_zero w) (Finset.notMem_empty w)
    | insert a s _ ih =>
      refine cast (congrArg IsStarFree ?_) ((singleton a).add ih)
      ext w
      refine (Language.mem_add _ _ w).trans ?_
      change w = a ∨ w ∈ s ↔ w ∈ insert a s
      rw [Finset.mem_insert]
  refine cast (congrArg IsStarFree ?_) (key hL.toFinset)
  ext w
  exact hL.mem_toFinset

end IsStarFree

/-- Over an infinite alphabet, `{ε}` is not star-free: an expression mentions finitely many
letters, and on the powers of a letter that it does not mention its language is all or nothing. -/
theorem not_isStarFree_one [Infinite α] : ¬ IsStarFree (1 : _root_.Language α) := by
  rintro ⟨e, he⟩
  obtain ⟨c, hc⟩ := e.letters_finite.exists_notMem
  rcases e.replicate_mem_or_notMem hc with h | h
  · have h1 := h 1
    rw [he, Language.mem_one] at h1
    exact List.cons_ne_nil _ _ h1
  · exact h 0 (he ▸ (Language.mem_one _).2 rfl)

/-- `{ε}` is star-free if and only if the alphabet is finite. -/
theorem isStarFree_one_iff : IsStarFree (1 : _root_.Language α) ↔ Finite α := by
  refine ⟨fun h => ?_, fun _ => IsStarFree.one⟩
  by_contra hfin
  have := not_finite_iff_infinite.1 hfin
  exact not_isStarFree_one h

end Cslib.Language
