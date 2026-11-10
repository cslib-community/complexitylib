/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Boolean
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Instantiating fixed CNF templates for constraint relations

A local CNF template uses natural-number positions, with correctness stated against the tuple of
the declared arity. Instantiation replaces each position by the variable at that position of the
constraint scope. Repeated variables are allowed. On well-formed inputs this preserves evaluation
under every assignment, hence satisfiability, with no auxiliary variables.

## Main definitions

* `Cslib.Logic.PL.CSP.CNFTemplates`: correctness of fixed local CNF formulas.
* `Cslib.Logic.PL.Constraint.instantiateCNF`: instantiate one relation template.
* `Cslib.Logic.PL.CSP.instantiateCNF`: concatenate the instantiated constraint templates.

## Main results

* `Cslib.Logic.PL.CSP.eval_instantiateCNF`: exact evaluation equivalence on well-formed inputs.
-/

public section

namespace Cslib.Logic.PL

variable {Rel V : Type*}

/-- Correct local CNF templates, with natural numbers denoting positions in a relation tuple.
Correctness at every assignment also rules out semantic dependence on out-of-range positions. -/
@[expose] def CSP.CNFTemplates (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (template : Rel → CNF ℕ) : Prop :=
  ∀ R a, (template R).eval a = sem R (List.ofFn fun i : Fin (arity R) => a i)

/-- Definitions on the declared finite coordinates become natural-position CNF templates by
relabeling each finite index by its value. -/
theorem CSP.cnfTemplates_relabel_fin {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {φ : ∀ R, CNF (Fin (arity R))}
    (h : ∀ R a, a ∈ booleanRelation arity sem R ↔ (φ R).eval a = true) :
    CNFTemplates arity sem (fun R => (φ R).relabel Fin.val) := by
  intro R a
  rw [CNF.eval_relabel]
  exact Bool.eq_iff_iff.mpr ((h R (fun i : Fin (arity R) => a i)).symm)

/-- Instantiate one relation template at its scope, using `fallback` outside the scope. The
fallback is semantically irrelevant when the scope has the correct arity and the template is
correct. -/
@[expose] def Constraint.instantiateCNF (fallback : V) (template : Rel → CNF ℕ)
    (c : Constraint Rel V) : CNF V :=
  (template c.1).relabel (fun i => c.2.getD i fallback)

/-- Exact evaluation equivalence for a well-formed instantiated constraint. -/
theorem Constraint.eval_instantiateCNF {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {template : Rel → CNF ℕ} (h : CSP.CNFTemplates arity sem template) (fallback : V)
    {c : Constraint Rel V} (hc : c.2.length = arity c.1) (σ : V → Bool) :
    (c.instantiateCNF fallback template).eval σ = c.eval sem σ := by
  obtain ⟨R, vs⟩ := c
  simp only [instantiateCNF, CNF.eval_relabel]
  rw [h R]
  change sem R (List.ofFn (fun i : Fin (arity R) => σ (vs.getD i fallback))) = sem R (vs.map σ)
  congr 1
  rw [← hc]
  convert List.ofFn_getElem_eq_map vs σ using 1
  congr 1 with i : 1
  rw [List.getD_eq_getElem vs fallback i.isLt]

/-- Instantiate and concatenate a fixed CNF template for every constraint. -/
@[expose] def CSP.instantiateCNF (fallback : V) (template : Rel → CNF ℕ)
    (F : CSP Rel V) : CNF V :=
  F.flatMap (Constraint.instantiateCNF fallback template)

/-- Instantiation preserves any common clause-width bound of the templates. -/
theorem CSP.length_clause_mem_instantiateCNF {template : Rel → CNF ℕ} {k : ℕ}
    (h : ∀ R c, c ∈ template R → c.length ≤ k) (fallback : V) {F : CSP Rel V}
    {c : Clause V} (hc : c ∈ F.instantiateCNF fallback template) : c.length ≤ k := by
  obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  simpa [Clause.relabel] using h d.1 e he

/-- Instantiation preserves evaluation under every assignment to well-formed instances. -/
theorem CSP.eval_instantiateCNF {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {template : Rel → CNF ℕ} (h : CNFTemplates arity sem template) (fallback : V)
    {F : CSP Rel V} (hF : WellFormed arity F) (σ : V → Bool) :
    (F.instantiateCNF fallback template).eval σ = F.eval sem σ := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change ((c.instantiateCNF fallback template ++ instantiateCNF fallback template F).eval σ) =
      (c.eval sem σ && CSP.eval sem σ F)
    rw [CNF.eval_append, Constraint.eval_instantiateCNF h fallback (hF c List.mem_cons_self),
      ih (fun d hd => hF d (List.mem_cons_of_mem _ hd))]

/-- Instantiation preserves satisfiability of well-formed instances. -/
theorem CSP.satisfiable_instantiateCNF {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {template : Rel → CNF ℕ} (h : CNFTemplates arity sem template) (fallback : V)
    {F : CSP Rel V} (hF : WellFormed arity F) :
    (F.instantiateCNF fallback template).Satisfiable ↔ F.Satisfiable sem := by
  simp only [CNF.Satisfiable, Satisfiable, eval_instantiateCNF h fallback hF]

end Cslib.Logic.PL
