/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.SecondOrder.Existential
public import Mathlib.ModelTheory.Complexity

/-!
# Existential second-order Horn logic

An SO∃-Horn sentence `∃ R₁ … Rₖ, ⋀ᵢ ∀ x̄ᵢ, Cᵢ` existentially quantifies finitely many relation
variables over a conjunction of universally closed clauses. Each clause has the form
`guard ∧ Rⱼ₁(ȳ₁) ∧ … ∧ Rⱼₘ(ȳₘ) → head`. Here `guard` is a formula of the base vocabulary,
the body atoms apply relation variables to clause variables, and `head` is either one such
atom (a definite clause) or `⊥` (a goal clause). The Horn restriction applies only to the
quantified relation variables: base-vocabulary symbols occur in the guard with either sign.
Grädel's fragment requires quantifier-free guards (`Sentence.IsQF`). A quantifier-free guard
in disjunctive normal form splits a clause into finitely many clauses in his CNF presentation.

The least relations closed under the definite clauses form a sentence's *least model*. A
sentence holds exactly when its least model satisfies its goal clauses. Truth therefore comes
from one canonical least fixed point, with no search over relations. `toESO` maps the syntax
into ordinary existential second-order logic and preserves truth.

## Main definitions

* `Cslib.Logic.ESO.Horn.Atom`, `Cslib.Logic.ESO.Horn.Clause`, `Cslib.Logic.ESO.Horn.Sentence`:
  relation-variable atoms, guarded Horn clauses and SO∃-Horn sentences.
* `Cslib.Logic.ESO.Horn.Sentence.Realize`, `Cslib.Logic.ESO.Horn.Sentence.IsQF`: truth and
  Grädel's quantifier-free restriction.
* `Cslib.Logic.ESO.Horn.Sentence.consequence`, `Cslib.Logic.ESO.Horn.Sentence.leastModel`: the
  immediate-consequence operator of the definite clauses and its least fixed point.
* `Cslib.Logic.ESO.Horn.Sentence.mapGuards`, `Cslib.Logic.ESO.Horn.Sentence.toESO`: guard
  translation and the existential second-order sentence with the same meaning.

## Main results

* `Cslib.Logic.ESO.Horn.Sentence.realize_iff_leastModel`: truth is decided by the least model.
* `Cslib.Logic.ESO.Horn.Sentence.closed_iff_consequence_le`: closed relations are exactly the
  pre-fixed points of the immediate-consequence operator.
* `Cslib.Logic.ESO.Horn.Sentence.realize_toESO`: SO∃-Horn is a fragment of SO∃.
* `Cslib.Logic.ESO.Horn.Sentence.realize_mapGuards`: truth-preserving guard translation.

## References

* [E. Grädel, *Capturing complexity classes by fragments of second-order logic*][Gradel1992],
  for the second-order Horn fragment and its successor-structure characterization of P.
  Section and theorem locators are unverified.
-/

@[expose] public section

universe u v w

namespace Cslib.Logic.ESO.Horn

open FirstOrder Language Structure

/-! ### Atoms and clauses -/

/-- A relation-variable atom `R(y₁, …, yₖ)` whose arguments are variables from `β`. -/
structure Atom {V : Type} (arity : V → ℕ) (β : Type) where
  /-- The relation variable. -/
  rel : V
  /-- The argument variables. -/
  args : Fin (arity rel) → β

variable {V : Type} {arity : V → ℕ} {M : Type w}

/-- An atom holds under relations `R` and a variable assignment `v`. -/
def Atom.Holds {β : Type} (a : Atom arity β) (R : ∀ i, Set (Fin (arity i) → M))
    (v : β → M) : Prop :=
  v ∘ a.args ∈ R a.rel

/-- Atoms are monotone in the interpretation of the relation variables. -/
theorem Atom.Holds.mono {β : Type} {a : Atom arity β} {R S : ∀ i, Set (Fin (arity i) → M)}
    (hRS : R ≤ S) {v : β → M} (h : a.Holds R v) : a.Holds S v :=
  hRS a.rel h

/-- A guarded Horn clause `∀ x̄, guard ∧ body → head`. Its variables are `Fin width`. The guard is
a base-vocabulary formula; the head is one atom (a definite clause) or `⊥` (a goal clause). -/
structure Clause (L : Language.{u, v}) {V : Type} (arity : V → ℕ) where
  /-- The number of universally quantified variables. -/
  width : ℕ
  /-- The base-vocabulary guard. -/
  guard : L.Formula (Fin width)
  /-- The relation-variable atoms of the body. -/
  body : List (Atom arity (Fin width))
  /-- The head atom; `none` is the goal clause `guard ∧ body → ⊥`. -/
  head : Option (Atom arity (Fin width))

variable {L : Language.{u, v}} {L' : Language.{u, v}}

/-- A clause holds under relations `R` when every assignment satisfying its guard and body
satisfies its head; a goal clause forbids such assignments. -/
def Clause.Holds [L.Structure M] (C : Clause L arity) (R : ∀ i, Set (Fin (arity i) → M)) :
    Prop :=
  ∀ v : Fin C.width → M, C.guard.Realize v → (∀ a ∈ C.body, a.Holds R v) →
    C.head.elim False fun a => a.Holds R v

/-- Replace the guard of a clause by its image under a formula translation. -/
def Clause.mapGuard (f : ∀ {α : Type}, L.Formula α → L'.Formula α) (C : Clause L arity) :
    Clause L' arity :=
  ⟨C.width, f C.guard, C.body, C.head⟩

/-- A truth-preserving guard translation preserves clause truth. -/
theorem Clause.holds_mapGuard [L.Structure M] [L'.Structure M]
    (f : ∀ {α : Type}, L.Formula α → L'.Formula α)
    (hf : ∀ {α : Type} (φ : L.Formula α) (v : α → M), (f φ).Realize v ↔ φ.Realize v)
    (C : Clause L arity) (R : ∀ i, Set (Fin (arity i) → M)) :
    (C.mapGuard f).Holds R ↔ C.Holds R :=
  forall_congr' fun v => imp_congr_left (hf C.guard v)

/-! ### Sentences -/

/-- An existential second-order Horn sentence: finitely many relation variables and a finite
conjunction of guarded Horn clauses over them. -/
structure Sentence (L : Language.{u, v}) where
  /-- The relation variables. -/
  Var : Type
  [finite : Finite Var]
  /-- The arity of each relation variable. -/
  arity : Var → ℕ
  /-- The clauses. -/
  clauses : List (Clause L arity)

attribute [instance] Sentence.finite

namespace Sentence

/-- An SO∃-Horn sentence holds in `M` when some relations satisfy all of its clauses. -/
def Realize (Φ : Sentence L) (M : Type w) [L.Structure M] : Prop :=
  ∃ R : ∀ i, Set (Fin (Φ.arity i) → M), ∀ C ∈ Φ.clauses, C.Holds R

/-- Grädel's restriction: every guard is quantifier-free. -/
def IsQF (Φ : Sentence L) : Prop :=
  ∀ C ∈ Φ.clauses, C.guard.IsQF

/-- Translate every guard, keeping the relation variables and the Horn structure. -/
def mapGuards (f : ∀ {α : Type}, L.Formula α → L'.Formula α) (Φ : Sentence L) :
    Sentence L' where
  Var := Φ.Var
  arity := Φ.arity
  clauses := Φ.clauses.map (Clause.mapGuard f)

/-- A truth-preserving guard translation preserves sentence truth. -/
theorem realize_mapGuards [L.Structure M] [L'.Structure M]
    (f : ∀ {α : Type}, L.Formula α → L'.Formula α)
    (hf : ∀ {α : Type} (φ : L.Formula α) (v : α → M), (f φ).Realize v ↔ φ.Realize v)
    (Φ : Sentence L) : (Φ.mapGuards f).Realize M ↔ Φ.Realize M := by
  refine exists_congr fun R => ?_
  change (∀ C ∈ Φ.clauses.map (Clause.mapGuard f), C.Holds R) ↔ _
  rw [List.forall_mem_map]
  exact forall₂_congr fun C _ => Clause.holds_mapGuard f hf C R

/-- The immediate-consequence operator of the definite clauses: one round of rule application.
A tuple is produced for a relation variable when some definite clause has it as an instance of
its head and its guard and body hold under `R`. -/
def consequence (Φ : Sentence L) (M : Type w) [L.Structure M] :
    (∀ i, Set (Fin (Φ.arity i) → M)) →o ∀ i, Set (Fin (Φ.arity i) → M) where
  toFun R i := {x | ∃ C ∈ Φ.clauses, ∃ a, C.head = some a ∧ ∃ v : Fin C.width → M,
    C.guard.Realize v ∧ (∀ b ∈ C.body, b.Holds R v) ∧
      (⟨a.rel, v ∘ a.args⟩ : Σ j, Fin (Φ.arity j) → M) = ⟨i, x⟩}
  monotone' R S hRS i := by
    rintro x ⟨C, hC, a, ha, v, hg, hb, he⟩
    exact ⟨C, hC, a, ha, v, hg, fun b hb' => (hb b hb').mono hRS, he⟩

/-- The least relations closed under the definite clauses: the least fixed point of the
immediate-consequence operator. -/
def leastModel (Φ : Sentence L) (M : Type w) [L.Structure M] : ∀ i, Set (Fin (Φ.arity i) → M) :=
  (Φ.consequence M).lfp

variable [L.Structure M]

/-- Relations closed under every definite clause. -/
def Closed (Φ : Sentence L) (R : ∀ i, Set (Fin (Φ.arity i) → M)) : Prop :=
  ∀ C ∈ Φ.clauses, C.head.isSome → C.Holds R

/-- Relations satisfying every goal clause. -/
def Consistent (Φ : Sentence L) (R : ∀ i, Set (Fin (Φ.arity i) → M)) : Prop :=
  ∀ C ∈ Φ.clauses, C.head = none → C.Holds R

/-- Truth splits into closure under the definite clauses and consistency with the goal
clauses. -/
theorem realize_iff (Φ : Sentence L) :
    Φ.Realize M ↔ ∃ R : ∀ i, Set (Fin (Φ.arity i) → M), Φ.Closed R ∧ Φ.Consistent R := by
  refine exists_congr fun R => ⟨fun h => ⟨fun C hC _ => h C hC, fun C hC _ => h C hC⟩,
    fun ⟨hcl, hco⟩ C hC => ?_⟩
  cases hh : C.head with
  | none => exact hco C hC hh
  | some a => exact hcl C hC (by simp only [hh, Option.isSome_some])

/-- Closure under the definite clauses is pre-fixedness for the immediate-consequence
operator. -/
theorem closed_iff_consequence_le (Φ : Sentence L) {R : ∀ i, Set (Fin (Φ.arity i) → M)} :
    Φ.Closed R ↔ Φ.consequence M R ≤ R := by
  constructor
  · rintro hR i x ⟨C, hC, a, ha, v, hg, hb, he⟩
    have h := hR C hC (by simp only [ha, Option.isSome_some]) v hg hb
    rw [ha] at h
    cases he
    exact h
  · intro hR C hC hh v hg hb
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hh
    rw [ha]
    change v ∘ a.args ∈ R a.rel
    exact hR a.rel ⟨C, hC, a, ha, v, hg, hb, rfl⟩

/-- The least model is below every closed family of relations. -/
theorem leastModel_le (Φ : Sentence L) {R : ∀ i, Set (Fin (Φ.arity i) → M)}
    (hR : Φ.Closed R) : Φ.leastModel M ≤ R :=
  (Φ.consequence M).lfp_le (Φ.closed_iff_consequence_le.mp hR)

/-- The least model is closed under the definite clauses. -/
theorem closed_leastModel (Φ : Sentence L) : Φ.Closed (Φ.leastModel M) :=
  Φ.closed_iff_consequence_le.mpr (Φ.consequence M).map_lfp.le

/-- **Least-model semantics.** An SO∃-Horn sentence holds exactly when the least relations
closed under its definite clauses satisfy its goal clauses. Truth is therefore decided by one
least fixed point, with no search over relations. -/
theorem realize_iff_leastModel (Φ : Sentence L) :
    Φ.Realize M ↔ Φ.Consistent (Φ.leastModel M) := by
  rw [realize_iff]
  refine ⟨fun ⟨R, hcl, hco⟩ C hC hh v hg hb => ?_,
    fun h => ⟨Φ.leastModel M, Φ.closed_leastModel, h⟩⟩
  have hRC := hco C hC hh v hg fun a ha => (hb a ha).mono (Φ.leastModel_le hcl)
  rw [hh] at hRC ⊢
  exact hRC

/-! ### The embedding into existential second-order logic -/

/-- An atom as an atomic formula of the base vocabulary extended by the relation variables. -/
def _root_.Cslib.Logic.ESO.Horn.Atom.formula {β : Type} (a : Atom arity β) :
    (L.sum (varLanguage arity)).Formula β :=
  Relations.formula (Sum.inr ⟨a.rel, rfl⟩ : (L.sum (varLanguage arity)).Relations _)
    fun i => .var (a.args i)

/-- A clause as its universal closure `∀ x̄, guard ∧ body → head`. -/
noncomputable def _root_.Cslib.Logic.ESO.Horn.Clause.formula (C : Clause L arity) :
    (L.sum (varLanguage arity)).Sentence :=
  Formula.iAlls (Fin C.width) (Formula.relabel Sum.inr
    (((LHom.sumInl : L →ᴸ L.sum (varLanguage arity)).onFormula C.guard ⊓
      (C.body.map Atom.formula).foldr (· ⊓ ·) ⊤).imp
      (C.head.elim ⊥ Atom.formula)))

/-- The existential second-order sentence with the same relation variables, whose matrix is
the conjunction of the clause formulas. -/
noncomputable def toESO (Φ : Sentence L) : ESO.Sentence L where
  Var := Φ.Var
  arity := Φ.arity
  matrix := (Φ.clauses.map Clause.formula).foldr (· ⊓ ·) ⊤

end Sentence

section Embedding

variable [L.Structure M]

/-- The atomic formula of an atom holds exactly when the atom does. -/
theorem Atom.realize_formula {β : Type} (a : Atom arity β) (R : ∀ i, Set (Fin (arity i) → M))
    (v : β → M) :
    letI := varLanguage.structure R
    (a.formula (L := L)).Realize v ↔ a.Holds R v := by
  let _ := varLanguage.structure R
  exact Formula.realize_rel

/-- The universal closure of a clause holds exactly when the clause does. -/
theorem Clause.realize_formula (C : Clause L arity) (R : ∀ i, Set (Fin (arity i) → M)) :
    letI := varLanguage.structure R
    M ⊨ C.formula ↔ C.Holds R := by
  let _ := varLanguage.structure R
  have hbody (v : Fin C.width → M) : Formula.Realize ((C.body.map Atom.formula).foldr (· ⊓ ·) ⊤ :
      (L.sum (varLanguage arity)).Formula _) v ↔ ∀ a ∈ C.body, a.Holds R v := by
    rw [Formula.Realize, BoundedFormula.realize_foldr_inf, List.forall_mem_map]
    exact forall₂_congr fun a _ => Atom.realize_formula a R v
  have hhead (v : Fin C.width → M) : Formula.Realize (C.head.elim ⊥ Atom.formula :
      (L.sum (varLanguage arity)).Formula _) v ↔ C.head.elim False fun a => a.Holds R v := by
    cases C.head with
    | none => exact Formula.realize_bot
    | some a => exact Atom.realize_formula a R v
  rw [Language.Sentence.Realize, Clause.formula, Formula.realize_iAlls]
  refine forall_congr' fun v => ?_
  rw [Formula.realize_relabel, Formula.realize_imp, Formula.realize_inf, LHom.realize_onFormula]
  exact and_imp.trans (imp_congr Iff.rfl (imp_congr (hbody v) (hhead v)))

/-- **SO∃-Horn is a fragment of SO∃.** The existential second-order sentence `Φ.toESO` holds
exactly when `Φ` does. -/
theorem Sentence.realize_toESO (Φ : Sentence L) : Φ.toESO.Realize M ↔ Φ.Realize M := by
  refine exists_congr fun (R : ∀ i, Set (Fin (Φ.arity i) → M)) => ?_
  let _ := varLanguage.structure R
  change M ⊨ ((Φ.clauses.map Clause.formula).foldr (· ⊓ ·) ⊤ :
    (L.sum (varLanguage Φ.arity)).Sentence) ↔ _
  rw [Language.Sentence.Realize, Formula.Realize, BoundedFormula.realize_foldr_inf,
    List.forall_mem_map]
  exact forall₂_congr fun C _ => Clause.realize_formula C R

end Embedding

end Cslib.Logic.ESO.Horn
