/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.Basic
public import Complexity.Computability.PolyTime.CSP.CNFTemplate
public import Complexity.Computability.Complexity.Problems.TwoSAT
public import Complexity.Logics.Propositional.CNF.Majority
import Complexity.Computability.Complexity.Problems.TwoSAT.Completeness
import Complexity.Computability.Complexity.Classes.LogSpace.PolyTime

/-!
# Native tractability from a common majority polymorphism

Each majority-preserved Boolean relation has a defining width-two CNF. For a fixed finite
language these formulas are fixed templates, so their instantiation is a native polynomial-time
reduction to 2SAT. Exact-arity guards reject malformed instances. Empty/nullary relations and
repeated variables are allowed. Native 2SAT membership in NL and `NL ⊆ P` give native P.

This proves the majority case of [Chen2006CSP], Theorem 3.20, under the library's explicit framed
CSP encoding and binary variable labels. The normal-form equivalence is [Bodirsky2026],
Lemma 6.32; no uniform complexity bound in a supplied language is asserted.

## Main results

* `Cslib.Complexity.CSPSAT.exists_twoCNF_templates`: fixed width-two templates from majority.
* `Cslib.Complexity.CSPSAT.polyTimeReducible_TwoSAT_of_templates`: certified instantiation.
* `Cslib.Complexity.CSPSAT.mem_P_of_majority`: native polynomial-time satisfiability.
-/

public section

namespace Cslib.Complexity.CSPSAT

open Cslib.Logic Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel : Type}

/-- A common majority polymorphism supplies correct fixed width-two CNF templates. -/
theorem exists_twoCNF_templates (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (Cslib.majority 3)) :
    ∃ template : Rel → CNF ℕ, CSP.CNFTemplates arity sem template ∧
      ∀ R c, c ∈ template R → c.length ≤ 2 := by
  classical
  have hex (R : Rel) := (isPolymorphism_majority_iff_exists_twoCNF
    (CSP.booleanRelation arity sem R)).mp (h R)
  choose φ hwidth hφ using hex
  let template : Rel → CNF ℕ := fun R => (φ R).relabel Fin.val
  refine ⟨template, ?_, ?_⟩
  · exact CSP.cnfTemplates_relabel_fin hφ
  · intro R c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    simpa [Clause.relabel] using hwidth R d hd

private def toTwoSAT (arity : Rel → ℕ) (template : Rel → CNF ℕ) (F : CSP Rel ℕ) : CNF ℕ :=
  if F.validArity arity then F.instantiateCNF 0 template else [[]]

/-- Fixed correct width-two templates induce a native polynomial-time reduction to 2SAT. -/
theorem polyTimeReducible_TwoSAT_of_templates [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (template : Rel → CNF ℕ)
    (ht : CSP.CNFTemplates arity sem template)
    (hw : ∀ R c, c ∈ template R → c.length ≤ 2) :
    PolyTimeReducible (encCSP encRel encNat) encCNF (CSPSAT arity sem) TwoSAT := by
  have hp : ComputableInPolyTime (toTwoSAT arity template) (encCSP encRel encNat) encCNF :=
    (CSP.computableInPolyTime_validArity encRel arity).ite
      (CSP.computableInPolyTime_instantiateCNF encRel template)
      (ComputableInPolyTime.const [[]])
  refine ⟨toTwoSAT arity template, hp, fun F => ?_⟩
  by_cases hF : F.WellFormed arity
  · have hwidth : ∀ c ∈ F.instantiateCNF 0 template, c.length ≤ 2 :=
      fun _ hc => CSP.length_clause_mem_instantiateCNF hw 0 hc
    have heq : toTwoSAT arity template F = F.instantiateCNF 0 template := by
      simp [toTwoSAT, (CSP.validArity_eq_true_iff arity F).mpr hF]
    rw [mem_iff, mem_TwoSAT, heq, CSP.satisfiable_instantiateCNF ht 0 hF]
    exact ⟨fun h => ⟨hwidth, h.2⟩, fun h => ⟨hF, h.2⟩⟩
  · have hguard : F.validArity arity = false := by
      cases hg : F.validArity arity
      · rfl
      · exact (hF ((CSP.validArity_eq_true_iff arity F).mp hg)).elim
    simp [toTwoSAT, hguard, mem_iff, hF, mem_TwoSAT, CNF.Satisfiable, CNF.eval, Clause.eval]

/-- **Native polynomial-time tractability of a fixed finite majority-preserved language.** -/
theorem mem_P_of_majority [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (Cslib.majority 3)) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) := by
  obtain ⟨template, ht, hw⟩ := exists_twoCNF_templates arity sem h
  exact (polyTimeReducible_TwoSAT_of_templates encRel arity sem template ht hw).mem_P
    (NL_subset_P TwoSAT.mem_NL)

end Cslib.Complexity.CSPSAT
