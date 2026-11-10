/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.Basic
public import CslibFrontier.Computability.PolyTime.CSP.CNFTemplate
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT
public import CslibFrontier.Logics.Propositional.CNF.Majority
import CslibFrontier.Computability.Complexity.Problems.TwoSAT.Completeness
import CslibFrontier.Computability.Complexity.Classes.LogSpace.PolyTime

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

/-- Fixed correct width-two templates induce a native polynomial-time reduction to 2SAT. -/
theorem polyTimeReducible_TwoSAT_of_templates [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (template : Rel → CNF ℕ)
    (ht : CSP.CNFTemplates arity sem template)
    (hw : ∀ R c, c ∈ template R → c.length ≤ 2) :
    PolyTimeReducible (encCSP encRel encNat) encCNF (CSPSAT arity sem) TwoSAT := by
  refine polyTimeReducible_of_guard encRel arity sem [[]]
    (CSP.computableInPolyTime_instantiateCNF encRel template) (fun F hF => ?_)
    (by simp [mem_TwoSAT, CNF.Satisfiable, CNF.eval, Clause.eval])
  rw [mem_TwoSAT, CSP.satisfiable_instantiateCNF ht 0 hF,
    and_iff_right fun _ hc => CSP.length_clause_mem_instantiateCNF hw 0 hc]

/-- **Native polynomial-time tractability of a fixed finite majority-preserved language.** -/
theorem mem_P_of_majority [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (Cslib.majority 3)) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) := by
  obtain ⟨template, ht, hw⟩ := exists_twoCNF_templates arity sem h
  exact (polyTimeReducible_TwoSAT_of_templates encRel arity sem template ht hw).mem_P
    (NL_subset_P TwoSAT.mem_NL)

end Cslib.Complexity.CSPSAT
