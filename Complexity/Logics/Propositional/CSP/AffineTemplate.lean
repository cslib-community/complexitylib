/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Affine
public import Complexity.Logics.Propositional.CSP.Boolean
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Instantiating fixed affine templates

A relation's affine normal form uses its finite coordinate type. Relabeling coordinates by their
natural values gives fixed local templates, instantiated by scope lookup and concatenation.
Repeated scope variables need no injectivity assumption: their occurrences cancel in the existing
Boolean ring. Empty systems, inconsistent constant equations and nullary relations are included.

This is the fixed-template substitution step in [Chen2006CSP], Theorem 4.3 and the following
Gaussian-elimination argument (arXiv v1, printed pp. 15–16). The normal forms are fixed with the
language; no efficient transformation of an input truth table is claimed.

## Main definitions

* `Cslib.Logic.PL.AffineEquation.relabel`, `Cslib.Logic.PL.AffineSystem.relabel`.
* `Cslib.Logic.PL.CSP.AffineTemplates`: correctness of fixed local systems.
* `Cslib.Logic.PL.CSP.instantiateAffine`: substitute scopes and concatenate systems.

## Main results

* `Cslib.Logic.PL.CSP.holds_instantiateAffine`: assignmentwise correctness on well-formed CSPs.
* `Cslib.Logic.PL.CSP.satisfiable_instantiateAffine`: satisfiability preservation.
-/

public section

namespace Cslib.Logic.PL

variable {Rel V W : Type*}

/-- Rename the variables of an affine equation, retaining all occurrences. -/
@[expose] def AffineEquation.relabel (f : V → W) (e : AffineEquation V) : AffineEquation W :=
  (e.1.map f, e.2)

/-- Substitution composes assignments; the variable map need not be injective. -/
@[simp] theorem AffineEquation.holds_relabel (f : V → W) (e : AffineEquation V)
    (a : W → Bool) : (e.relabel f).Holds a ↔ e.Holds (a ∘ f) := by
  simp [relabel, Holds, List.map_map, Function.comp_def]

/-- Rename every equation of an affine system. -/
@[expose] def AffineSystem.relabel (f : V → W) (F : AffineSystem V) : AffineSystem W :=
  F.map (AffineEquation.relabel f)

/-- System substitution preserves satisfaction under composed assignments, including repeated
images of distinct variables. -/
@[simp] theorem AffineSystem.holds_relabel (f : V → W) (F : AffineSystem V)
    (a : W → Bool) : (F.relabel f).Holds a ↔ F.Holds (a ∘ f) := by
  constructor
  · intro h e he
    exact (AffineEquation.holds_relabel f e a).mp (h _ (List.mem_map.mpr ⟨e, he, rfl⟩))
  · intro h e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    exact (AffineEquation.holds_relabel f q a).mpr (h q hq)

/-- Correct natural-position templates, evaluated at the declared finite tuple. -/
@[expose] def CSP.AffineTemplates (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (template : Rel → AffineSystem ℕ) : Prop :=
  ∀ R a, (template R).Holds a ↔ sem R (List.ofFn fun i : Fin (arity R) => a i) = true

/-- Finite-coordinate definitions yield correct natural-position templates. -/
theorem CSP.affineTemplates_relabel_fin {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {φ : ∀ R, AffineSystem (Fin (arity R))}
    (h : ∀ R a, a ∈ booleanRelation arity sem R ↔ (φ R).Holds a) :
    AffineTemplates arity sem (fun R => (φ R).relabel Fin.val) := by
  intro R a
  rw [AffineSystem.holds_relabel]
  exact (h R (fun i : Fin (arity R) => a i)).symm

/-- Instantiate a local system using scope lookup. The fallback is irrelevant on correctly
sized scopes for correct templates. -/
@[expose] def Constraint.instantiateAffine (fallback : V) (template : Rel → AffineSystem ℕ)
    (c : Constraint Rel V) : AffineSystem V :=
  (template c.1).relabel (fun i => c.2.getD i fallback)

/-- Correctness of an instantiated constraint under every assignment. -/
theorem Constraint.holds_instantiateAffine {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {template : Rel → AffineSystem ℕ} (h : CSP.AffineTemplates arity sem template)
    (fallback : V) {c : Constraint Rel V} (hc : c.2.length = arity c.1) (σ : V → Bool) :
    (c.instantiateAffine fallback template).Holds σ ↔ c.eval sem σ = true := by
  obtain ⟨R, vs⟩ := c
  rw [instantiateAffine, AffineSystem.holds_relabel, h R]
  change sem R (List.ofFn (fun i : Fin (arity R) => σ (vs.getD i fallback))) = true ↔
    sem R (vs.map σ) = true
  have heq : List.ofFn (fun i : Fin (arity R) => σ (vs.getD i fallback)) = vs.map σ := by
    rw [← hc]
    convert List.ofFn_getElem_eq_map vs σ using 1
    congr 1
    funext i
    rw [List.getD_eq_getElem vs fallback i.isLt]
  rw [heq]

/-- Instantiate each constraint and concatenate the resulting systems. -/
@[expose] def CSP.instantiateAffine (fallback : V) (template : Rel → AffineSystem ℕ)
    (F : CSP Rel V) : AffineSystem V :=
  F.flatMap (Constraint.instantiateAffine fallback template)

/-- Instantiation preserves satisfaction on every assignment of a well-formed instance. -/
theorem CSP.holds_instantiateAffine {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {template : Rel → AffineSystem ℕ} (h : AffineTemplates arity sem template) (fallback : V)
    {F : CSP Rel V} (hF : WellFormed arity F) (σ : V → Bool) :
    (F.instantiateAffine fallback template).Holds σ ↔ F.eval sem σ = true := by
  change (∀ e ∈ F.flatMap (Constraint.instantiateAffine fallback template), e.Holds σ) ↔ _
  simp only [List.mem_flatMap, forall_exists_index, and_imp]
  change (∀ e c, c ∈ F → e ∈ c.instantiateAffine fallback template → e.Holds σ) ↔ _
  rw [CSP.eval, List.all_eq_true]
  constructor
  · intro he c hc
    exact (Constraint.holds_instantiateAffine h fallback (hF c hc) σ).mp
      (fun e hec => he e c hc hec)
  · intro hc e c hmem he
    exact (Constraint.holds_instantiateAffine h fallback (hF c hmem) σ).mpr (hc c hmem) e he

/-- No auxiliary variables are needed to preserve satisfiability. -/
theorem CSP.satisfiable_instantiateAffine {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {template : Rel → AffineSystem ℕ} (h : AffineTemplates arity sem template) (fallback : V)
    {F : CSP Rel V} (hF : WellFormed arity F) :
    (∃ σ, (F.instantiateAffine fallback template).Holds σ) ↔ F.Satisfiable sem := by
  simp only [Satisfiable, holds_instantiateAffine h fallback hF]

end Cslib.Logic.PL
