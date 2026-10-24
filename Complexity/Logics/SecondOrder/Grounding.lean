/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Problems.CNF
public import Complexity.Logics.FirstOrder.Subformula
public import Complexity.Logics.SecondOrder.Reduction
import Mathlib.Tactic.FinCases

/-!
# Existential second-order definable classes reduce to SAT by order-free interpretations

The reductions in this module use order-free first-order interpretations. Input structures have
no built-in order or numeric predicates; these results are order-free variants of the standard ones.

Every existential second-order definable class of finite structures that contains every empty
structure is order-free reducible to the class `cnf.SAT` of satisfiable CNF structures
(`Cslib.Logic.ESO.Definable.reduces_SAT`). With Fagin's theorem this gives the NP-completeness
of SAT under order-free reductions, for classes containing every empty structure; see
`Complexity.Computability.Complexity.Fagin.SAT`. This is an adaptation of the descriptive form of
the Cook–Levin theorem [Immerman, Chapter 7][Immerman1999]: Immerman's structures are ordered and
have at least two elements, and his reductions are first-order projections, while this module
uses first-order interpretations, with quantifiers, of unordered structures. Neither statement
implies the other.

The reduction grounds the sentence. Let `Φ = ∃ R₁ … Rₖ, φ` and let `M` be a finite structure. For
every subformula `ψ` of `φ` with `k` bound variables and every tuple `a ∈ Mᵏ` there is a
propositional variable `X(ψ, a)`, read as "`ψ` holds of `a`", and for every relation variable `R`
of arity `m` and every `b ∈ Mᵐ` a propositional variable `V(R, b)`, read as "`R` holds of `b`".
Clauses force each `X(ψ, a)` to agree with the meaning of `ψ`, in the manner of Tseitin's
encoding: `X(⊥, a)` is false, an equation or an atom of the input language is decided by `M`, an
atom `R(t)` is equivalent to `V(R, t(a))`, `X(ψ → χ, a)` is equivalent to `X(ψ, a) → X(χ, a)`, and
`X(∀x ψ, a)` is equivalent to the conjunction of the `X(ψ, a b)`; a last clause asserts
`X(φ, ())`. Each satisfying assignment then defines relations `Rᵢ` making `φ` true, and conversely.

The propositional variables and clauses are of finitely many kinds, which are the tags of a tagged
interpretation (`Cslib.Logic.ESO.Sentence.groundInterpretation`) whose literals are defined by
templates. On structures with at most one element, where tags cannot be told apart, the reduction
evaluates `Φ` directly: every relation is empty or full, so a finite disjunction of first-order
sentences decides it (`Cslib.Logic.ESO.Sentence.subsingletonSentence`). Every empty structure is
mapped to the empty CNF structure, which is satisfiable; this is why the class must contain every
empty structure.

## Main definitions

* `Cslib.Logic.ESO.Sentence.Subformula`, `Cslib.Logic.ESO.Sentence.GroundTag`,
  `Cslib.Logic.ESO.Sentence.GroundTag.Coord`: the subformulas, variable and clause tags, and
  coordinate types of the grounding of an existential second-order sentence.
* `Cslib.Logic.ESO.Sentence.termCoord`, `Cslib.Logic.ESO.Sentence.selfVar`,
  `Cslib.Logic.ESO.Sentence.clauseTemplates`, `Cslib.Logic.ESO.Sentence.groundTemplates`: the
  literal templates of the grounding.
* `Cslib.Logic.ESO.Sentence.groundInterpretation`: the grounding of an existential second-order
  sentence, a tagged interpretation in CNF structures.
* `Cslib.Logic.ESO.Sentence.constInterpretation`,
  `Cslib.Logic.ESO.Sentence.subsingletonSentence`,
  `Cslib.Logic.ESO.Sentence.subsingletonInterpretation`: the constant-relation interpretation,
  defining first-order sentence, and CNF reduction on structures with at most one element.

## Main results

* `Cslib.Logic.ESO.Sentence.satisfiable_groundInterpretation_iff`: the grounding of `Φ` in a
  nonempty structure `M` is satisfiable exactly when `Φ` holds in `M`.
* `Cslib.Logic.ESO.Sentence.realize_subsingletonSentence`: correctness of the sentence on
  structures with at most one element.
* `Cslib.Logic.ESO.Definable.reduces_SAT`: every existential second-order definable class
  containing every empty structure is order-free reducible to SAT.
* `Cslib.Logic.ESO.definable_iff_reduces_SAT`: for classes containing every empty structure,
  existential second-order definability is order-free reducibility to SAT.
* `Cslib.Logic.ESO.Definable.exists_interpretation_SAT_of_nonempty`: every existential second-order
  definable class is order-free reducible to SAT on the nonempty finite structures.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
-/

@[expose] public section

universe u v w

open FirstOrder Language Structure CategoryTheory

/-! ### The grounding -/

namespace Cslib.Logic.ESO.Sentence

open FO FO.TaggedInterpretation FO.cnf

variable {L : Language.{u, v}} [L.IsRelational] (Φ : ESO.Sentence L)

/-- The subformulas of the first-order part of `Φ`. -/
abbrev Subformula : Type _ :=
  ↥(subformulas Φ.matrix)

/-- The type `Φ.Subformula` of subformulas of `Φ.matrix` is finite. -/
instance : Finite Φ.Subformula :=
  (finite_subformulas Φ.matrix).to_subtype

/-- The kinds of propositional variables and clauses of the grounding of `Φ`: a variable for each
subformula and each relation variable, the clause asserting the first-order part, and up to three
clauses for each subformula. -/
inductive GroundTag : Type _
  /-- The variables `X(ψ, a)`: the subformula `ψ` holds of the tuple `a`. -/
  | var (s : Φ.Subformula)
  /-- The variables `V(R, b)`: the relation variable `R` holds of the tuple `b`. -/
  | relVar (r : Φ.Var)
  /-- The clause `X(φ, ())`. -/
  | top
  /-- The clauses defining `X(ψ, a)`. -/
  | clause (s : Φ.Subformula) (i : Fin 3)

/-- The kinds, as a sum type. -/
private def GroundTag.toSum : Φ.GroundTag → Φ.Subformula ⊕ Φ.Var ⊕ Unit ⊕ (Φ.Subformula × Fin 3)
  | .var s => .inl s
  | .relVar r => .inr (.inl r)
  | .top => .inr (.inr (.inl ()))
  | .clause s i => .inr (.inr (.inr (s, i)))

/-- The type `Φ.GroundTag` of variable and clause kinds in the grounding of `Φ` is finite. -/
instance : Finite Φ.GroundTag := by
  refine Finite.of_injective (GroundTag.toSum Φ) ?_
  intro a b h
  cases a <;> cases b <;> simp_all [GroundTag.toSum]

variable {Φ}

/-- The coordinates of the elements of each kind: those of `X(ψ, a)` are the bound variables of
`ψ`, those of `V(R, b)` the arguments of `R`, and those of a clause defining `X(ψ, a)` are the
bound variables of `ψ` and one more, the value of the quantified variable when `ψ = ∀x χ`. -/
def GroundTag.Coord : Φ.GroundTag → Type
  | .var s => Fin s.1.1
  | .relVar r => Fin (Φ.arity r)
  | .top => Fin 0
  | .clause s _ => Fin (s.1.1 + 1)

/-- Every tag `t : Φ.GroundTag` has a finite coordinate type `t.Coord`. -/
instance instFiniteGroundTagCoord : ∀ t : Φ.GroundTag, Finite t.Coord
  | .var _ => inferInstanceAs (Finite (Fin _))
  | .relVar _ => inferInstanceAs (Finite (Fin _))
  | .top => inferInstanceAs (Finite (Fin _))
  | .clause _ _ => inferInstanceAs (Finite (Fin _))

/-- The coordinate of a clause holding the value of a term, a variable of the subformula. -/
def termCoord {k : ℕ} (t : (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)) : Fin (k + 1) :=
  (termVar t).elim Empty.elim Fin.castSucc

/-- The template relating a clause to the variable `X(ψ, a)` of its subformula. -/
def selfVar (s : Φ.Subformula) (i : Fin 3) (guard : L.Formula (Fin (s.1.1 + 1))) :
    Template L GroundTag.Coord (GroundTag.clause s i) :=
  ⟨.var s, guard, fun j => some j.castSucc⟩

/-- The templates of the literals of polarity `b` of the clauses `i` of a subformula. -/
def clauseTemplates : (s : Φ.Subformula) → (i : Fin 3) → Bool →
    List (Template L GroundTag.Coord (GroundTag.clause s i))
  | ⟨⟨k, .falsum⟩, hs⟩, 0, false => [selfVar ⟨⟨k, .falsum⟩, hs⟩ 0 ⊤]
  | ⟨⟨k, .equal t₁ t₂⟩, hs⟩, 0, b =>
    [selfVar ⟨⟨k, .equal t₁ t₂⟩, hs⟩ 0 (if b then varEq (termCoord t₁) (termCoord t₂)
      else ∼(varEq (termCoord t₁) (termCoord t₂)))]
  | ⟨⟨k, .rel (.inl R) ts⟩, hs⟩, 0, b =>
    [selfVar ⟨⟨k, .rel (.inl R) ts⟩, hs⟩ 0 (if b then R.formula (fun j => .var (termCoord (ts j)))
      else ∼(R.formula fun j => .var (termCoord (ts j))))]
  | ⟨⟨k, .rel (.inr r) ts⟩, hs⟩, 0, false => [selfVar ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ 0 ⊤]
  | ⟨⟨_, .rel (.inr r) ts⟩, _⟩, 0, true =>
    [⟨.relVar r.1, ⊤, fun j => some (termCoord (ts (Fin.cast r.2 j)))⟩]
  | ⟨⟨k, .rel (.inr r) ts⟩, hs⟩, 1, true => [selfVar ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ 1 ⊤]
  | ⟨⟨_, .rel (.inr r) ts⟩, _⟩, 1, false =>
    [⟨.relVar r.1, ⊤, fun j => some (termCoord (ts (Fin.cast r.2 j)))⟩]
  | ⟨⟨k, .imp ψ χ⟩, hs⟩, 0, false =>
    [selfVar ⟨⟨k, .imp ψ χ⟩, hs⟩ 0 ⊤,
      ⟨.var ⟨⟨k, ψ⟩, mem_subformulas_of_imp_left hs⟩, ⊤, fun j => some j.castSucc⟩]
  | ⟨⟨k, .imp _ χ⟩, hs⟩, 0, true =>
    [⟨.var ⟨⟨k, χ⟩, mem_subformulas_of_imp_right hs⟩, ⊤, fun j => some j.castSucc⟩]
  | ⟨⟨k, .imp ψ χ⟩, hs⟩, 1, true =>
    [selfVar ⟨⟨k, .imp ψ χ⟩, hs⟩ 1 ⊤,
      ⟨.var ⟨⟨k, ψ⟩, mem_subformulas_of_imp_left hs⟩, ⊤, fun j => some j.castSucc⟩]
  | ⟨⟨k, .imp ψ χ⟩, hs⟩, 2, true => [selfVar ⟨⟨k, .imp ψ χ⟩, hs⟩ 2 ⊤]
  | ⟨⟨k, .imp _ χ⟩, hs⟩, 2, false =>
    [⟨.var ⟨⟨k, χ⟩, mem_subformulas_of_imp_right hs⟩, ⊤, fun j => some j.castSucc⟩]
  | ⟨⟨k, .all ψ⟩, hs⟩, 0, false => [selfVar ⟨⟨k, .all ψ⟩, hs⟩ 0 ⊤]
  | ⟨⟨k, .all ψ⟩, hs⟩, 0, true => [⟨.var ⟨⟨k + 1, ψ⟩, mem_subformulas_of_all hs⟩, ⊤, some⟩]
  | ⟨⟨k, .all ψ⟩, hs⟩, 1, true => [selfVar ⟨⟨k, .all ψ⟩, hs⟩ 1 ⊤]
  | ⟨⟨k, .all ψ⟩, hs⟩, 1, false =>
    [⟨.var ⟨⟨k + 1, ψ⟩, mem_subformulas_of_all hs⟩, ⊤, Fin.lastCases none fun j => some j.castSucc⟩]
  | _, _, _ => []

variable (Φ) in
/-- The templates of the literals of polarity `b` of the elements of each kind. A variable names
the tautology `x ∨ ¬x` of itself. -/
def groundTemplates : (t : Φ.GroundTag) → Bool → List (Template L GroundTag.Coord t)
  | .var s, _ => [⟨.var s, ⊤, some⟩]
  | .relVar r, _ => [⟨.relVar r, ⊤, some⟩]
  | .top, true => [⟨.var ⟨⟨0, Φ.matrix⟩, self_mem_subformulas _⟩, ⊤, Fin.elim0⟩]
  | .top, false => []
  | .clause s i, b => clauseTemplates s i b

variable (Φ) in
/-- The **grounding** of `Φ`, a tagged interpretation in CNF structures. A clause kind without
templates has no elements. -/
noncomputable def groundInterpretation :
    TaggedInterpretation L cnf Φ.GroundTag GroundTag.Coord where
  domain
    | .clause s i => if (clauseTemplates s i true).isEmpty && (clauseTemplates s i false).isEmpty
        then ⊥ else ⊤
    | _ => ⊤
  rel R := match R with
    | .pos => binaryRel fun t w => Template.listFormula (Φ.groundTemplates t true) w
    | .neg => binaryRel fun t w => Template.listFormula (Φ.groundTemplates t false) w

private theorem groundInterpretation_rel_lit (b : Bool) (ts : Fin 2 → Φ.GroundTag) :
    Φ.groundInterpretation.rel (lit b) ts =
      binaryRel (fun t w => Template.listFormula (Φ.groundTemplates t b) w) ts := by
  cases b <;> rfl

/-! ### Correctness of the clauses -/

section Clauses

variable {M : Type w} [L.Structure M]

/-- The variable `X(ψ, a)`. -/
private def atom (s : Φ.Subformula) (a : Fin s.1.1 → M) : Φ.groundInterpretation.Model M :=
  ⟨.var s, a, formula_realize_top⟩

/-- The variable `V(R, b)`. -/
private def relAtom (r : Φ.Var) (b : Fin (Φ.arity r) → M) : Φ.groundInterpretation.Model M :=
  ⟨.relVar r, b, formula_realize_top⟩

private theorem clauseSat_iff (A : Φ.groundInterpretation.Model M → Prop)
    (c : Φ.groundInterpretation.Model M) :
    ClauseSatisfied A c ↔
      (∃ τ ∈ Φ.groundTemplates c.1 true, τ.guard.Realize c.2.1 ∧
        ∃ y hy, τ.Compat c.2.1 y ∧ A ⟨τ.target, y, hy⟩) ∨
      (∃ τ ∈ Φ.groundTemplates c.1 false, τ.guard.Realize c.2.1 ∧
        ∃ y hy, τ.Compat c.2.1 y ∧ ¬A ⟨τ.target, y, hy⟩) :=
  clauseSatisfied_iff_of_templates groundInterpretation_rel_lit A c

omit [L.Structure M] in
private theorem term_realize {k : ℕ} [(L.sum (varLanguage Φ.arity)).Structure M]
    (t : (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)) (x : Fin (k + 1) → M) :
    t.realize (Sum.elim default (Fin.init x)) = x (termCoord t) := by
  rw [realize_termVar, termCoord]
  rcases termVar t with e | j
  · exact e.elim
  · rfl

/-- The clauses of a kind with literal templates are in the domain. -/
private theorem realize_domain_clause {k : ℕ}
    {ψ : (L.sum (varLanguage Φ.arity)).BoundedFormula Empty k}
    (hs : ⟨k, ψ⟩ ∈ subformulas Φ.matrix) (i : Fin 3) (x : Fin (k + 1) → M)
    (h : ((clauseTemplates ⟨_, hs⟩ i true).isEmpty &&
      (clauseTemplates ⟨_, hs⟩ i false).isEmpty) = false := by rfl) :
    (Φ.groundInterpretation.domain (.clause ⟨_, hs⟩ i)).Realize x := by
  simp only [groundInterpretation, h, Bool.false_eq_true, ↓reduceIte]
  exact formula_realize_top

/-- The clause kinds without literal templates have no elements. -/
private theorem not_realize_domain_clause {k : ℕ}
    {ψ : (L.sum (varLanguage Φ.arity)).BoundedFormula Empty k}
    (hs : ⟨k, ψ⟩ ∈ subformulas Φ.matrix) (i : Fin 3) (x : Fin (k + 1) → M)
    (h : ((clauseTemplates ⟨_, hs⟩ i true).isEmpty &&
      (clauseTemplates ⟨_, hs⟩ i false).isEmpty) = true := by rfl) :
    ¬(Φ.groundInterpretation.domain (.clause ⟨_, hs⟩ i)).Realize x := by
  simp only [groundInterpretation, h, ↓reduceIte]
  exact id

variable (A : Φ.groundInterpretation.Model M → Prop)

/-- Every variable names the tautology `x ∨ ¬x`. -/
private theorem clauseSat_var (s : Φ.Subformula) (a : Fin s.1.1 → M) (ha) :
    ClauseSatisfied A ⟨.var s, a, ha⟩ := by
  refine (clauseSat_iff A _).2 ?_
  by_cases h : A ⟨.var s, a, ha⟩
  · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, a, ha, fun j i hj => by
      cases Option.some.inj hj; rfl, h⟩
  · exact .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, a, ha, fun j i hj => by
      cases Option.some.inj hj; rfl, h⟩

private theorem clauseSat_relVar (r : Φ.Var) (b : Fin (Φ.arity r) → M) (hb) :
    ClauseSatisfied A ⟨.relVar r, b, hb⟩ := by
  refine (clauseSat_iff A _).2 ?_
  by_cases h : A ⟨.relVar r, b, hb⟩
  · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, b, hb, fun j i hj => by
      cases Option.some.inj hj; rfl, h⟩
  · exact .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, b, hb, fun j i hj => by
      cases Option.some.inj hj; rfl, h⟩

private theorem clauseSat_top (x : Fin 0 → M) (hx) :
    ClauseSatisfied A ⟨.top, x, hx⟩ ↔ A (atom ⟨⟨0, Φ.matrix⟩, self_mem_subformulas _⟩ x) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -, y, hy, -, ha⟩ | ⟨τ, hτ, -⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : x = y := funext fun j => Fin.elim0 j
      exact ha
    · exact (List.not_mem_nil hτ).elim
  · intro h
    exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, x, formula_realize_top,
        fun j => j.elim0, h⟩

variable {k : ℕ} (x : Fin (k + 1) → M)

private theorem clauseSat_falsum (hs : ⟨k, .falsum⟩ ∈ subformulas Φ.matrix) (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, .falsum⟩, hs⟩ 0, x, hx⟩ ↔
      ¬A (atom ⟨⟨k, .falsum⟩, hs⟩ (Fin.init x)) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -⟩ | ⟨τ, hτ, -, y, hy, hc, ha⟩)
    · exact (List.not_mem_nil hτ).elim
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact ha
  · intro h
    exact .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.init x, formula_realize_top,
      fun j i hj => by cases Option.some.inj hj; rfl, h⟩

private theorem clauseSat_equal {t₁ t₂ : (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)}
    (hs : ⟨k, .equal t₁ t₂⟩ ∈ subformulas Φ.matrix) (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, .equal t₁ t₂⟩, hs⟩ 0, x, hx⟩ ↔
      (A (atom ⟨⟨k, .equal t₁ t₂⟩, hs⟩ (Fin.init x)) ↔ x (termCoord t₁) = x (termCoord t₂)) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, hg, y, hy, hc, ha⟩ | ⟨τ, hτ, hg, y, hy, hc, ha⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact iff_of_true ha ((realize_varEq _ _ _).1 hg)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact iff_of_false ha fun h => hg ((realize_varEq _ _ _).2 h)
  · intro h
    by_cases he : x (termCoord t₁) = x (termCoord t₂)
    · exact .inl ⟨_, List.mem_singleton.2 rfl, (realize_varEq _ _ _).2 he, Fin.init x,
        formula_realize_top, fun j i hj => by cases Option.some.inj hj; rfl, h.2 he⟩
    · exact .inr ⟨_, List.mem_singleton.2 rfl,
        fun h => he ((realize_varEq _ _ _).1 h), Fin.init x,
        formula_realize_top, fun j i hj => by cases Option.some.inj hj; rfl, mt h.1 he⟩

private theorem clauseSat_relInl {l : ℕ} {R : L.Relations l}
    {ts : Fin l → (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)}
    (hs : ⟨k, .rel (.inl R) ts⟩ ∈ subformulas Φ.matrix) (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, .rel (.inl R) ts⟩, hs⟩ 0, x, hx⟩ ↔
      (A (atom ⟨⟨k, .rel (.inl R) ts⟩, hs⟩ (Fin.init x)) ↔
        RelMap R fun j => x (termCoord (ts j))) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, hg, y, hy, hc, ha⟩ | ⟨τ, hτ, hg, y, hy, hc, ha⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact iff_of_true ha (Formula.realize_rel.1 hg)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact iff_of_false ha fun h => hg (Formula.realize_rel.2 h)
  · intro h
    by_cases he : RelMap R fun j => x (termCoord (ts j))
    · exact .inl ⟨_, List.mem_singleton.2 rfl, Formula.realize_rel.2 he, Fin.init x,
        formula_realize_top, fun j i hj => by cases Option.some.inj hj; rfl, h.2 he⟩
    · exact .inr ⟨_, List.mem_singleton.2 rfl,
        fun h => he (Formula.realize_rel.1 h), Fin.init x,
        formula_realize_top, fun j i hj => by cases Option.some.inj hj; rfl, mt h.1 he⟩

/-- The arguments of an atom of a relation variable, read from the coordinates of a clause. -/
private def relArgs {l : ℕ} (r : (varLanguage Φ.arity).Relations l)
    (ts : Fin l → (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)) :
    Fin (Φ.arity r.1) → M :=
  fun j => x (termCoord (ts (Fin.cast r.2 j)))

private theorem clauseSat_relInr₀ {l : ℕ} {r : (varLanguage Φ.arity).Relations l}
    {ts : Fin l → (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)}
    (hs : ⟨k, .rel (.inr r) ts⟩ ∈ subformulas Φ.matrix) (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ 0, x, hx⟩ ↔
      (A (atom ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ (Fin.init x)) → A (relAtom r.1 (relArgs x r ts))) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -, y, hy, hc, ha⟩ | ⟨τ, hτ, -, y, hy, hc, ha⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = relArgs x r ts := funext fun j => hc j _ rfl
      exact fun _ => ha
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact fun h => (ha h).elim
  · intro h
    by_cases ha : A (atom ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ (Fin.init x))
    · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, relArgs x r ts,
          formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h ha⟩
    · exact .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.init x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, ha⟩

private theorem clauseSat_relInr₁ {l : ℕ} {r : (varLanguage Φ.arity).Relations l}
    {ts : Fin l → (L.sum (varLanguage Φ.arity)).Term (Empty ⊕ Fin k)}
    (hs : ⟨k, .rel (.inr r) ts⟩ ∈ subformulas Φ.matrix) (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ 1, x, hx⟩ ↔
      (A (relAtom r.1 (relArgs x r ts)) → A (atom ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ (Fin.init x))) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -, y, hy, hc, ha⟩ | ⟨τ, hτ, -, y, hy, hc, ha⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact fun _ => ha
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = relArgs x r ts := funext fun j => hc j _ rfl
      exact fun h => (ha h).elim
  · intro h
    by_cases ha : A (relAtom r.1 (relArgs x r ts))
    · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.init x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h ha⟩
    · exact .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, relArgs x r ts,
          formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, ha⟩

section Imp

variable {ψ χ : (L.sum (varLanguage Φ.arity)).BoundedFormula Empty k}
  (hs : ⟨k, ψ.imp χ⟩ ∈ subformulas Φ.matrix)

private theorem clauseSat_imp₀ (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, ψ.imp χ⟩, hs⟩ 0, x, hx⟩ ↔
      (A (atom ⟨⟨k, ψ.imp χ⟩, hs⟩ (Fin.init x)) →
        A (atom ⟨⟨k, ψ⟩, mem_subformulas_of_imp_left hs⟩ (Fin.init x)) →
        A (atom ⟨⟨k, χ⟩, mem_subformulas_of_imp_right hs⟩ (Fin.init x))) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -, y, hy, hc, ha⟩ | ⟨τ, hτ, -, y, hy, hc, ha⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact fun _ _ => ha
    · rcases List.mem_cons.1 hτ with rfl | hτ
      · obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
        exact fun h => (ha h).elim
      · obtain rfl := List.mem_singleton.1 hτ
        obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
        exact fun _ h => (ha h).elim
  · intro h
    by_cases h₁ : A (atom ⟨⟨k, ψ.imp χ⟩, hs⟩ (Fin.init x))
    · by_cases h₂ : A (atom ⟨⟨k, ψ⟩, mem_subformulas_of_imp_left hs⟩ (Fin.init x))
      · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.init x,
            formula_realize_top,
          fun j i hj => by cases Option.some.inj hj; rfl, h h₁ h₂⟩
      · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), formula_realize_top,
          Fin.init x, formula_realize_top, fun j i hj => by cases Option.some.inj hj; rfl, h₂⟩
    · exact .inr ⟨_, List.mem_cons_self, formula_realize_top, Fin.init x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h₁⟩

private theorem clauseSat_imp₁ (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, ψ.imp χ⟩, hs⟩ 1, x, hx⟩ ↔
      (A (atom ⟨⟨k, ψ.imp χ⟩, hs⟩ (Fin.init x)) ∨
        A (atom ⟨⟨k, ψ⟩, mem_subformulas_of_imp_left hs⟩ (Fin.init x))) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -, y, hy, hc, ha⟩ | ⟨τ, hτ, -⟩)
    · rcases List.mem_cons.1 hτ with rfl | hτ
      · obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
        exact .inl ha
      · obtain rfl := List.mem_singleton.1 hτ
        obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
        exact .inr ha
    · exact (List.not_mem_nil hτ).elim
  · rintro (h | h)
    · exact .inl ⟨_, List.mem_cons_self, formula_realize_top, Fin.init x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h⟩
    · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_singleton.2 rfl), formula_realize_top,
        Fin.init x, formula_realize_top, fun j i hj => by cases Option.some.inj hj; rfl, h⟩

private theorem clauseSat_imp₂ (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, ψ.imp χ⟩, hs⟩ 2, x, hx⟩ ↔
      (A (atom ⟨⟨k, χ⟩, mem_subformulas_of_imp_right hs⟩ (Fin.init x)) →
        A (atom ⟨⟨k, ψ.imp χ⟩, hs⟩ (Fin.init x))) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -, y, hy, hc, ha⟩ | ⟨τ, hτ, -, y, hy, hc, ha⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact fun _ => ha
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact fun h => (ha h).elim
  · intro h
    by_cases h₂ : A (atom ⟨⟨k, χ⟩, mem_subformulas_of_imp_right hs⟩ (Fin.init x))
    · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.init x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h h₂⟩
    · exact .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.init x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h₂⟩

end Imp

section All

variable {ψ : (L.sum (varLanguage Φ.arity)).BoundedFormula Empty (k + 1)}
  (hs : ⟨k, ψ.all⟩ ∈ subformulas Φ.matrix)

private theorem clauseSat_all₀ (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, ψ.all⟩, hs⟩ 0, x, hx⟩ ↔
      (A (atom ⟨⟨k, ψ.all⟩, hs⟩ (Fin.init x)) →
        A (atom ⟨⟨k + 1, ψ⟩, mem_subformulas_of_all hs⟩ x)) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -, y, hy, hc, ha⟩ | ⟨τ, hτ, -, y, hy, hc, ha⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : x = y := funext fun j => (hc j _ rfl).symm
      exact fun _ => ha
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact fun h => (ha h).elim
  · intro h
    by_cases h₁ : A (atom ⟨⟨k, ψ.all⟩, hs⟩ (Fin.init x))
    · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h h₁⟩
    · exact .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.init x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h₁⟩

private theorem clauseSat_all₁ (hx) :
    ClauseSatisfied A ⟨.clause ⟨⟨k, ψ.all⟩, hs⟩ 1, x, hx⟩ ↔
      ((∀ b, A (atom ⟨⟨k + 1, ψ⟩, mem_subformulas_of_all hs⟩ (Fin.snoc (Fin.init x) b))) →
        A (atom ⟨⟨k, ψ.all⟩, hs⟩ (Fin.init x))) := by
  refine (clauseSat_iff A _).trans ?_
  constructor
  · rintro (⟨τ, hτ, -, y, hy, hc, ha⟩ | ⟨τ, hτ, -, y, hy, hc, ha⟩)
    · obtain rfl := List.mem_singleton.1 hτ
      obtain rfl : y = Fin.init x := funext fun j => hc j _ rfl
      exact fun _ => ha
    · obtain rfl := List.mem_singleton.1 hτ
      have : y = Fin.snoc (Fin.init x) (y (Fin.last k)) := by
        refine funext fun j => ?_
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa [Fin.init] using hc j.castSucc _ (by simp)
      exact fun h => (ha (this ▸ h _)).elim
  · intro h
    by_cases h₁ : ∀ b, A (atom ⟨⟨k + 1, ψ⟩, mem_subformulas_of_all hs⟩ (Fin.snoc (Fin.init x) b))
    · exact .inl ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.init x, formula_realize_top,
        fun j i hj => by cases Option.some.inj hj; rfl, h h₁⟩
    · obtain ⟨b, hb⟩ := not_forall.1 h₁
      refine .inr ⟨_, List.mem_singleton.2 rfl, formula_realize_top, Fin.snoc (Fin.init x) b,
          formula_realize_top,
        fun j i hj => ?_, hb⟩
      induction j using Fin.lastCases with
      | last => simp at hj
      | cast j =>
        have hj' : Fin.lastCases (motive := fun _ => Option (Fin (k + 1))) none
            (fun j => some j.castSucc) j.castSucc = some i := hj
        rw [Fin.lastCases_castSucc] at hj'
        obtain rfl := Option.some.inj hj'
        change Fin.snoc (Fin.init x) b j.castSucc = x j.castSucc
        simp [Fin.init]

end All

end Clauses

/-! ### Correctness of the grounding -/

section Correctness

variable {M : Type w} [L.Structure M]

/-- The relations read from an assignment: `R` holds of `b` when `V(R, b)` is true. -/
private def assignmentRel (A : Φ.groundInterpretation.Model M → Prop) (r : Φ.Var) :
    Set (Fin (Φ.arity r) → M) :=
  {b | A (relAtom r b)}

private theorem exists_init_eq [Nonempty M] {k : ℕ} (a : Fin k → M) : ∃ x : Fin (k + 1) → M,
    Fin.init x = a :=
  ⟨Fin.snoc a (Classical.arbitrary M), Fin.init_snoc _ _⟩

/-- **Soundness of the grounding**: under a satisfying assignment, each variable `X(ψ, a)` is true
exactly when `ψ` holds of `a` for the relations read from the assignment. -/
private theorem atom_iff_realize [Nonempty M] {A : Φ.groundInterpretation.Model M → Prop}
    (hA : cnf.Satisfies A) {k : ℕ} (ψ : (L.sum (varLanguage Φ.arity)).BoundedFormula Empty k)
    (hs : ⟨k, ψ⟩ ∈ subformulas Φ.matrix) (a : Fin k → M) :
    A (atom ⟨⟨k, ψ⟩, hs⟩ a) ↔
      (letI := varLanguage.structure (assignmentRel A); ψ.Realize default a) := by
  let _ := varLanguage.structure (assignmentRel A)
  induction ψ with
  | falsum =>
    obtain ⟨x, rfl⟩ := exists_init_eq a
    exact iff_of_false ((clauseSat_falsum A x hs (realize_domain_clause hs 0 x)).1 (hA _)) id
  | equal t₁ t₂ =>
    obtain ⟨x, rfl⟩ := exists_init_eq a
    rw [(clauseSat_equal A x hs (realize_domain_clause hs 0 x)).1 (hA _)]
    change _ ↔ t₁.realize _ = t₂.realize _
    rw [term_realize, term_realize]
  | rel R ts =>
    obtain ⟨x, rfl⟩ := exists_init_eq a
    rcases R with R | r
    · rw [(clauseSat_relInl A x hs (realize_domain_clause hs 0 x)).1 (hA _)]
      change _ ↔ RelMap R fun i => (ts i).realize _
      simp only [term_realize]
    · have h₀ := (clauseSat_relInr₀ A x hs (realize_domain_clause hs 0 x)).1 (hA _)
      have h₁ := (clauseSat_relInr₁ A x hs (realize_domain_clause hs 1 x)).1 (hA _)
      refine Iff.trans ⟨h₀, h₁⟩ ?_
      change _ ↔ A (relAtom r.1 fun j => (ts (Fin.cast r.2 j)).realize _)
      simp only [term_realize]
      rfl
  | imp ψ χ ih₁ ih₂ =>
    obtain ⟨x, rfl⟩ := exists_init_eq a
    have h₀ := (clauseSat_imp₀ A x hs (realize_domain_clause hs 0 x)).1 (hA _)
    have h₁ := (clauseSat_imp₁ A x hs (realize_domain_clause hs 1 x)).1 (hA _)
    have h₂ := (clauseSat_imp₂ A x hs (realize_domain_clause hs 2 x)).1 (hA _)
    have e₁ := ih₁ (mem_subformulas_of_imp_left hs) (Fin.init x)
    have e₂ := ih₂ (mem_subformulas_of_imp_right hs) (Fin.init x)
    rw [BoundedFormula.realize_imp]
    exact ⟨fun h hψ => e₂.1 (h₀ h (e₁.2 hψ)),
      fun h => h₁.elim id fun h' => h₂ (e₂.2 (h (e₁.1 h')))⟩
  | all ψ ih =>
    rw [BoundedFormula.realize_all]
    constructor
    · intro h b
      refine (ih (mem_subformulas_of_all hs) _).1 ?_
      have := (clauseSat_all₀ A (Fin.snoc a b) hs (realize_domain_clause hs 0 _)).1 (hA _)
      rw [Fin.init_snoc] at this
      exact this h
    · intro h
      have := (clauseSat_all₁ A (Fin.snoc a (Classical.arbitrary M)) hs
        (realize_domain_clause hs 1 _)).1 (hA _)
      simp only [Fin.init_snoc] at this
      exact this fun b => (ih (mem_subformulas_of_all hs) _).2 (h b)

/-- The assignment given by relations `R`: `X(ψ, a)` is true when `ψ` holds of `a`, and `V(R, b)`
when `R` holds of `b`. -/
private def canonicalAssignment (R : ∀ i, Set (Fin (Φ.arity i) → M)) :
    Φ.groundInterpretation.Model M → Prop
  | ⟨.var s, a, _⟩ => letI := varLanguage.structure R; s.1.2.Realize default a
  | ⟨.relVar r, b, _⟩ => b ∈ R r
  | _ => False

/-- **Completeness of the grounding**: relations making the first-order part true give a
satisfying assignment. -/
private theorem satisfies_canonicalAssignment (R : ∀ i, Set (Fin (Φ.arity i) → M))
    (h : letI := varLanguage.structure R; M ⊨ Φ.matrix) :
    cnf.Satisfies (canonicalAssignment R) := by
  let _ := varLanguage.structure R
  rintro ⟨t, x, hx⟩
  cases t with
  | var s => exact clauseSat_var _ s x hx
  | relVar r => exact clauseSat_relVar _ r x hx
  | top =>
    refine (clauseSat_top _ x hx).2 ?_
    obtain rfl : x = Fin.elim0 := funext fun j => Fin.elim0 j
    have h0 : (Fin.elim0 : Fin 0 → M) = default := Subsingleton.elim _ _
    change BoundedFormula.Realize Φ.matrix default Fin.elim0
    rw [h0]
    exact h
  | clause s i =>
    obtain ⟨⟨k, ψ⟩, hs⟩ := s
    change Fin (k + 1) → M at x
    cases ψ with
    | falsum =>
      fin_cases i
      · exact (clauseSat_falsum _ x hs hx).2 id
      · exact absurd hx (not_realize_domain_clause hs _ x)
      · exact absurd hx (not_realize_domain_clause hs _ x)
    | equal t₁ t₂ =>
      fin_cases i
      · refine (clauseSat_equal _ x hs hx).2 ?_
        change t₁.realize _ = t₂.realize _ ↔ _
        rw [term_realize, term_realize]
      · exact absurd hx (not_realize_domain_clause hs _ x)
      · exact absurd hx (not_realize_domain_clause hs _ x)
    | rel R ts =>
      rcases R with R | r
      · fin_cases i
        · refine (clauseSat_relInl _ x hs hx).2 ?_
          change (RelMap R fun i => (ts i).realize _) ↔ _
          simp only [term_realize]
        · exact absurd hx (not_realize_domain_clause hs _ x)
        · exact absurd hx (not_realize_domain_clause hs _ x)
      · have hiff : canonicalAssignment R (atom ⟨⟨k, .rel (.inr r) ts⟩, hs⟩ (Fin.init x)) ↔
            canonicalAssignment R (relAtom r.1 (relArgs x r ts)) := by
          change (fun j => (ts (Fin.cast r.2 j)).realize _) ∈ R r.1 ↔ _
          simp only [term_realize]
          rfl
        fin_cases i
        · exact (clauseSat_relInr₀ _ x hs hx).2 hiff.1
        · exact (clauseSat_relInr₁ _ x hs hx).2 hiff.2
        · exact absurd hx (not_realize_domain_clause hs _ x)
    | imp ψ χ =>
      fin_cases i
      · exact (clauseSat_imp₀ _ x hs hx).2 fun h h₁ => h h₁
      · refine (clauseSat_imp₁ _ x hs hx).2 (or_iff_not_imp_right.2 fun h h' => (h h').elim)
      · exact (clauseSat_imp₂ _ x hs hx).2 fun h _ => h
    | all ψ =>
      fin_cases i
      · refine (clauseSat_all₀ _ x hs hx).2 fun h => ?_
        have := h (x (Fin.last k))
        rwa [Fin.snoc_init_self] at this
      · exact (clauseSat_all₁ _ x hs hx).2 fun h => h
      · exact absurd hx (not_realize_domain_clause hs _ x)

/-- **The grounding is correct**: the grounding of `Φ` in a nonempty structure `M` is satisfiable
exactly when `Φ` holds in `M`. -/
theorem satisfiable_groundInterpretation_iff [Nonempty M] :
    cnf.Satisfiable (Φ.groundInterpretation.Model M) ↔ Φ.Realize M := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨assignmentRel A, ?_⟩
    have := (clauseSat_top A (Fin.elim0 : Fin 0 → M) formula_realize_top).1 (hA _)
    have h := (atom_iff_realize hA Φ.matrix _ _).1 this
    let _ := varLanguage.structure (assignmentRel A)
    change BoundedFormula.Realize Φ.matrix default default
    rwa [Subsingleton.elim (default : Fin 0 → M) Fin.elim0]
  · rintro ⟨R, h⟩
    exact ⟨_, satisfies_canonicalAssignment R h⟩

end Correctness

/-! ### Structures with at most one element -/

section Subsingleton

variable (Φ) {M : Type w} [L.Structure M]

/-- The interpretation substituting `⊤` or `⊥` for each relation variable, according to `s`. -/
def constInterpretation (s : Φ.Var → Bool) :
    Interpretation L (L.sum (varLanguage Φ.arity)) Unit where
  domain := ⊤
  rel R := match R with
    | .inl R => R.formula fun i => .var (i, ())
    | .inr r => if s r.1 then ⊤ else ⊥

/-- On structures with at most one element, every relation is empty or full: the first-order
sentence that `Φ` holds for some choice of empty and full relations. -/
noncomputable def subsingletonSentence : L.Sentence :=
  Formula.iSup fun s : Φ.Var → Bool => (constInterpretation Φ s).onSentence Φ.matrix

variable {Φ}

/-- The empty or full relations chosen by `s`. -/
private def constRel (s : Φ.Var → Bool) (i : Φ.Var) : Set (Fin (Φ.arity i) → M) :=
  if s i then Set.univ else ∅

/-- The relations defined on `M` by the interpretation substituting `⊤` and `⊥` are those of the
expansion of `M` by the empty and full relations chosen by `s`. -/
private def constStructureEquiv (s : Φ.Var → Bool) :
    @Language.Equiv (L.sum (varLanguage Φ.arity)) M M ((constInterpretation Φ s).unitStructure M)
      (@sumStructure _ _ M _ (varLanguage.structure (constRel (M := M) s))) :=
  @Language.Equiv.mk _ M M ((constInterpretation Φ s).unitStructure M)
    (@sumStructure _ _ M _ (varLanguage.structure (constRel (M := M) s))) (Equiv.refl M)
    (fun f => isEmptyElim f) fun r x => match r with
      | .inl _ => Iff.rfl
      | .inr r => by
        change _ ∈ constRel s r.1 ↔ (if s r.1 then ⊤ else ⊥ : L.Formula _).Realize _
        unfold constRel
        cases s r.1 <;> simp

/-- The interpretation substituting `⊤` and `⊥` interprets the expansion by empty and full
relations. -/
private theorem realize_constInterpretation (s : Φ.Var → Bool) :
    (constInterpretation Φ s).Model M ⊨ Φ.matrix ↔
      (letI := varLanguage.structure (constRel (M := M) s); M ⊨ Φ.matrix) := by
  have h₁ := @StrongHomClass.realize_sentence _ ((constInterpretation Φ s).Model M) M _
    ((constInterpretation Φ s).unitStructure M) _ _ _
    ((constInterpretation Φ s).unitModelEquiv M fun _ => formula_realize_top) Φ.matrix
  have h₂ := @StrongHomClass.realize_sentence _ M M ((constInterpretation Φ s).unitStructure M)
    (@sumStructure _ _ M _ (varLanguage.structure (constRel (M := M) s))) _ _ _
    (constStructureEquiv s) Φ.matrix
  exact h₁.trans h₂

/-- **Correctness of the sentence for small structures.** -/
theorem realize_subsingletonSentence [Subsingleton M] :
    M ⊨ Φ.subsingletonSentence ↔ Φ.Realize M := by
  change (Formula.iSup _).Realize default ↔ _
  rw [Formula.realize_iSup]
  change (∃ s, M ⊨ (constInterpretation Φ s).onSentence Φ.matrix) ↔ _
  simp only [Interpretation.realize_onSentence]
  constructor
  · rintro ⟨s, h⟩
    exact ⟨constRel s, (realize_constInterpretation s).1 h⟩
  · rintro ⟨R, h⟩
    classical
    refine ⟨fun i => decide (R i).Nonempty, ?_⟩
    have hR : R = constRel fun i => decide (R i).Nonempty := by
      funext i
      ext z
      change z ∈ R i ↔ z ∈ if decide (R i).Nonempty = true then Set.univ else ∅
      by_cases hne : (R i).Nonempty
      · rw [decide_eq_true hne]
        obtain ⟨z', hz'⟩ := hne
        exact iff_of_true (Subsingleton.elim z' z ▸ hz') trivial
      · rw [decide_eq_false hne]
        exact iff_of_false (fun hz => hne ⟨z, hz⟩) id
    rw [hR] at h
    exact (realize_constInterpretation _).2 h

variable (Φ) in
/-- The reduction on structures with at most one element: a single element naming the clause
`x` if `Φ` holds and the empty clause otherwise. -/
noncomputable def subsingletonInterpretation : Interpretation L cnf Unit where
  domain := ⊤
  rel R := match R with
    | .pos => Φ.subsingletonSentence.relabel Empty.elim
    | .neg => ⊥

private theorem relMap_pos_subsingletonInterpretation (c y : Φ.subsingletonInterpretation.Model M) :
    RelMap cnf.pos ![c, y] ↔ M ⊨ Φ.subsingletonSentence := by
  change (Φ.subsingletonSentence.relabel Empty.elim).Realize _ ↔ _
  rw [Formula.realize_relabel]
  exact iff_of_eq (congrArg (Formula.Realize Φ.subsingletonSentence) (Subsingleton.elim _ _))

private theorem satisfiable_subsingletonInterpretation_iff [Nonempty M] :
    cnf.Satisfiable (Φ.subsingletonInterpretation.Model M) ↔ M ⊨ Φ.subsingletonSentence := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨y, hy | ⟨hy, -⟩⟩ := hA ⟨fun _ => Classical.arbitrary M, formula_realize_top⟩
    · exact (relMap_pos_subsingletonInterpretation _ _).1 hy.1
    · exact hy.elim
  · intro h
    exact ⟨fun _ => True, fun c => ⟨c, .inl ⟨(relMap_pos_subsingletonInterpretation _ _).2 h,
      trivial⟩⟩⟩

end Subsingleton

end Cslib.Logic.ESO.Sentence

/-! ### SAT is complete for existential second-order logic under order-free reductions -/

namespace Cslib.Logic.ESO

open FO FO.TaggedInterpretation

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Every existential second-order definable class containing every empty structure is
order-free reducible to SAT** [Immerman, Chapter 7][Immerman1999]. The reduction grounds the
defining sentence (`Cslib.Logic.ESO.Sentence.groundInterpretation`). The empty-structure hypothesis
cannot be dropped in general: an interpretation of positive dimension maps every empty input to
the empty CNF structure, which is satisfiable. -/
theorem Definable.reduces_SAT {K : Set (Bundled.{w} L.Structure)} (hK : Definable K)
    (hempty : ∀ M : Bundled.{w} L.Structure, IsEmpty M → M ∈ K) : Reduces K cnf.SAT.{w} := by
  obtain ⟨Φ, hΦ⟩ := hK
  let e := Finite.equivFin Φ.GroundTag
  have : ∀ t, Finite ((Sentence.GroundTag.Coord ∘ e.symm) t) := fun t =>
    inferInstanceAs (Finite (Sentence.GroundTag.Coord (e.symm t)))
  refine Reduces.of_tagged cnf.isoClosed_SAT cnf.copyInvariant_SAT
    (Φ.groundInterpretation.reindex e) Φ.subsingletonInterpretation (fun M _ hM => ?_)
    (fun M _ hM => ?_)
  · rw [hΦ M]
    change _ ↔ cnf.Satisfiable ((Φ.groundInterpretation.reindex e).Model M)
    rw [cnf.satisfiable_iff_of_equiv (reindexEquiv _ e M),
      Sentence.satisfiable_groundInterpretation_iff]
  · rcases isEmpty_or_nonempty M with hM' | hM'
    · have : IsEmpty (Φ.subsingletonInterpretation.Model M) := ⟨fun x => isEmptyElim (x.1 ())⟩
      exact iff_of_true (hempty M hM')
        (cnf.satisfiable_of_isEmpty (M := Φ.subsingletonInterpretation.Model M))
    · rw [hΦ M]
      change _ ↔ cnf.Satisfiable (Φ.subsingletonInterpretation.Model M)
      rw [Sentence.satisfiable_subsingletonInterpretation_iff,
        Sentence.realize_subsingletonSentence]

/-- **SAT is complete for existential second-order logic under order-free reductions**: a class
containing every empty structure is existential second-order definable exactly when it is
order-free reducible to SAT. -/
theorem definable_iff_reduces_SAT {K : Set (Bundled.{w} L.Structure)}
    (hempty : ∀ M : Bundled.{w} L.Structure, IsEmpty M → M ∈ K) :
    Definable K ↔ Reduces K cnf.SAT.{w} :=
  ⟨fun h => h.reduces_SAT hempty, fun h => cnf.definable_SAT.of_reduces h⟩

/-- **Every existential second-order definable class is order-free reducible to SAT on the
nonempty structures**: some first-order interpretation maps every nonempty finite structure inside
SAT exactly when it is in the class. This is an order-free variant of
[Immerman, Chapter 7][Immerman1999], whose structures are ordered and have at least two elements.
The construction reduces the class with every empty structure added. -/
theorem Definable.exists_interpretation_SAT_of_nonempty {K : Set (Bundled.{w} L.Structure)}
    (hK : Definable K) : ∃ (ι : Type) (_ : Finite ι) (I : Interpretation L cnf ι),
      ∀ (M : Bundled.{w} L.Structure) [Finite M] [Nonempty M],
        M ∈ K ↔ Bundled.of (c := cnf.Structure) (I.Model M) ∈ cnf.SAT.{w} := by
  obtain ⟨ι, hι, I, hI⟩ :=
    (hK.union (Definable.of_fo FO.Definable.isEmpty)).reduces_SAT fun M hM => .inr hM
  refine ⟨ι, hι, I, fun M _ _ => ?_⟩
  rw [← hI M]
  exact ⟨.inl, fun h => h.resolve_right (not_isEmpty_of_nonempty M)⟩

end Cslib.Logic.ESO
