/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.Basic
public import Complexity.Computability.PolyTime.CSP.CNFTemplate
public import Complexity.Computability.Complexity.Problems.HornSAT
public import Complexity.Logics.Propositional.CNF.Horn.Relabel
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Native tractability from common AND and OR polymorphisms

Every AND-preserved Boolean relation has a Horn CNF definition; every OR-preserved relation
has a dual Horn definition. For each fixed finite language these definitions are fixed templates.
Their certified instantiation reduces the original CSP to ordinary native HornSAT or dual
HornSAT. The exact-arity guard rejects malformed scopes with an empty clause. No bound on clause
width is imposed; repeated variables, empty relations, nullary relations and sparse binary labels
are allowed.

These are the AND and OR cases of [Chen2006CSP], Theorem 3.20, with the original framed CSP
encoding, fixed arbitrary relation arities and binary variable names. The normal forms are
[Bodirsky2026], Lemma 6.31 and its dual; the local normal-form module proves them without
auxiliary variables. Template selection is internal and nonuniform in the fixed language: no
solver, template or efficiency hypothesis is required, and no uniform bound in a supplied
language is claimed.

## Main results

* `Cslib.Complexity.CSPSAT.exists_hornCNF_templates`: fixed Horn templates from AND.
* `Cslib.Complexity.CSPSAT.exists_dualHornCNF_templates`: fixed dual Horn templates from OR.
* `Cslib.Complexity.CSPSAT.mem_P_of_and`: native polynomial time from a common AND polymorphism.
* `Cslib.Complexity.CSPSAT.mem_P_of_or`: native polynomial time from a common OR polymorphism.
-/

public section

namespace Cslib.Complexity.CSPSAT

open Cslib.Logic Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel : Type}

/-- A common AND polymorphism supplies correct fixed Horn templates, with no auxiliaries. -/
theorem exists_hornCNF_templates (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 && a 1)) :
    ∃ template : Rel → CNF ℕ, CSP.CNFTemplates arity sem template ∧
      ∀ R, (template R).IsHorn := by
  classical
  have hex (R : Rel) := (isPolymorphism_and_iff_exists_hornCNF
    (CSP.booleanRelation arity sem R)).mp (h R)
  choose φ hφ heval using hex
  exact ⟨fun R => (φ R).relabel Fin.val, CSP.cnfTemplates_relabel_fin heval,
    fun R => (CNF.isHorn_relabel _ _).mpr (hφ R)⟩

/-- A common OR polymorphism supplies correct fixed dual Horn templates, with no auxiliaries. -/
theorem exists_dualHornCNF_templates (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 || a 1)) :
    ∃ template : Rel → CNF ℕ, CSP.CNFTemplates arity sem template ∧
      ∀ R, (template R).IsDualHorn := by
  classical
  have hex (R : Rel) := (isPolymorphism_or_iff_exists_dualHornCNF
    (CSP.booleanRelation arity sem R)).mp (h R)
  choose φ hφ heval using hex
  exact ⟨fun R => (φ R).relabel Fin.val, CSP.cnfTemplates_relabel_fin heval,
    fun R => (CNF.isDualHorn_relabel _ _).mpr (hφ R)⟩

private def guardedCNF (arity : Rel → ℕ) (template : Rel → CNF ℕ)
    (F : CSP Rel ℕ) : CNF ℕ :=
  if F.validArity arity then F.instantiateCNF 0 template else [[]]

/-- Fixed correct Horn templates give a native polynomial-time reduction to ordinary HornSAT.
The guard rejects every malformed scope, regardless of the semantics on lists of wrong length. -/
theorem polyTimeReducible_HornSAT_of_templates [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (template : Rel → CNF ℕ)
    (ht : CSP.CNFTemplates arity sem template) (hh : ∀ R, (template R).IsHorn) :
    PolyTimeReducible (encCSP encRel encNat) encCNF (CSPSAT arity sem) HornSAT := by
  have hp : ComputableInPolyTime (guardedCNF arity template)
      (encCSP encRel encNat) encCNF :=
    (Cslib.Complexity.CSP.computableInPolyTime_validArity encRel arity).ite
      (CSP.computableInPolyTime_instantiateCNF encRel template)
      (ComputableInPolyTime.const [[]])
  refine ⟨guardedCNF arity template, hp, fun F => ?_⟩
  by_cases hF : F.WellFormed arity
  · have hsyntax : (F.instantiateCNF 0 template).IsHorn := by
      intro c hc
      obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hc
      exact ((CNF.isHorn_relabel _ _).mpr (hh d.1)) c hd
    have heq : guardedCNF arity template F = F.instantiateCNF 0 template := by
      simp [guardedCNF, (CSP.validArity_eq_true_iff arity F).mpr hF]
    change (F.WellFormed arity ∧ F.Satisfiable sem) ↔
      (guardedCNF arity template F).IsHorn ∧ (guardedCNF arity template F).Satisfiable
    rw [heq, CSP.satisfiable_instantiateCNF ht 0 hF]
    exact ⟨fun h => ⟨hsyntax, h.2⟩, fun h => ⟨hF, h.2⟩⟩
  · have hguard : F.validArity arity = false := by
      cases hg : F.validArity arity
      · rfl
      · exact (hF ((CSP.validArity_eq_true_iff arity F).mp hg)).elim
    simp [guardedCNF, hguard, mem_iff, hF, HornSAT, CNF.Satisfiable, CNF.eval, Clause.eval]

/-- Fixed correct dual Horn templates give a native polynomial-time reduction to dual HornSAT. -/
theorem polyTimeReducible_DualHornSAT_of_templates [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (template : Rel → CNF ℕ)
    (ht : CSP.CNFTemplates arity sem template) (hh : ∀ R, (template R).IsDualHorn) :
    PolyTimeReducible (encCSP encRel encNat) encCNF (CSPSAT arity sem) DualHornSAT := by
  have hp : ComputableInPolyTime (guardedCNF arity template)
      (encCSP encRel encNat) encCNF :=
    (Cslib.Complexity.CSP.computableInPolyTime_validArity encRel arity).ite
      (CSP.computableInPolyTime_instantiateCNF encRel template)
      (ComputableInPolyTime.const [[]])
  refine ⟨guardedCNF arity template, hp, fun F => ?_⟩
  by_cases hF : F.WellFormed arity
  · have hsyntax : (F.instantiateCNF 0 template).IsDualHorn := by
      apply (CNF.isDualHorn_iff _).mpr
      intro c hc
      obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hc
      exact (CNF.isDualHorn_iff _).mp
        ((CNF.isDualHorn_relabel _ _).mpr (hh d.1)) c hd
    have heq : guardedCNF arity template F = F.instantiateCNF 0 template := by
      simp [guardedCNF, (CSP.validArity_eq_true_iff arity F).mpr hF]
    change (F.WellFormed arity ∧ F.Satisfiable sem) ↔
      (guardedCNF arity template F).IsDualHorn ∧ (guardedCNF arity template F).Satisfiable
    rw [heq, CSP.satisfiable_instantiateCNF ht 0 hF]
    exact ⟨fun h => ⟨hsyntax, h.2⟩, fun h => ⟨hF, h.2⟩⟩
  · have hguard : F.validArity arity = false := by
      cases hg : F.validArity arity
      · rfl
      · exact (hF ((CSP.validArity_eq_true_iff arity F).mp hg)).elim
    simp [guardedCNF, hguard, mem_iff, hF, DualHornSAT, CNF.Satisfiable, CNF.eval, Clause.eval]

/-- **Native polynomial-time tractability of a fixed finite AND-preserved Boolean language.** -/
theorem mem_P_of_and [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 && a 1)) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) := by
  obtain ⟨template, ht, hh⟩ := exists_hornCNF_templates arity sem h
  exact (polyTimeReducible_HornSAT_of_templates encRel arity sem template ht hh).mem_P HornSAT.mem_P

/-- **Native polynomial-time tractability of a fixed finite OR-preserved Boolean language.** -/
theorem mem_P_of_or [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 || a 1)) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) := by
  obtain ⟨template, ht, hh⟩ := exists_dualHornCNF_templates arity sem h
  exact (polyTimeReducible_DualHornSAT_of_templates encRel arity sem template ht hh).mem_P
    DualHornSAT.mem_P

end Cslib.Complexity.CSPSAT
