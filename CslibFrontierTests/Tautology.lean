/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Tautology

/-! Clients of TAUTOLOGY's coNP-completeness and of Arora–Barak 2007, Exercise 2 §7. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

open Cslib.Complexity Cslib.Logic.PL

/-- `x₀ ∨ ¬x₀` is a tautology. -/
example : (QBF.var 0).or (QBF.var 0).not ∈ TAUTOLOGY := by
  refine mem_TAUTOLOGY.2 ⟨by simp, fun σ => ?_⟩
  cases σ 0 <;> simp_all

/-- A variable is not a tautology: it is false under the all-false assignment. -/
example : QBF.var 0 ∉ TAUTOLOGY := fun h => by simpa using (mem_TAUTOLOGY.1 h).2 fun _ => false

/-- A true closed formula with a quantifier is not a member: TAUTOLOGY is a set of Boolean
formulas. -/
example : QBF.all 0 QBF.top ∉ TAUTOLOGY := fun h => by simpa using (mem_TAUTOLOGY.1 h).1

/-- The token scan evaluates a quantifier-free formula under the assignment of a list of true
variables. -/
example : ((QBF.var 0).and (QBF.var 1).not).tokens.reverse.foldl
    (QBF.evalStep fun v => [0].contains v) [] = [true] := by
  rw [QBF.foldl_evalStep (by simp)]
  simp

/-- A CNF is unsatisfiable exactly when its negation is a tautology; the reduction is native. -/
example (φ : CNF ℕ) : φ ∈ UNSAT ↔ (QBF.ofCNF φ).not ∈ TAUTOLOGY :=
  not_ofCNF_mem_TAUTOLOGY_iff.symm

/-- Every coNP problem, at any encoding, reduces to TAUTOLOGY. -/
example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hA : A ∈ coNP enc) :
    PolyTimeReducible enc encQBF A TAUTOLOGY :=
  TAUTOLOGY_coNPComplete.2 enc A hA

/-- Exercise 2 §7: a reduction from TAUTOLOGY to 3SAT puts every coNP problem in NP. -/
example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hA : A ∈ coNP enc)
    (h : PolyTimeReducible encQBF encCNF TAUTOLOGY ThreeSAT) : A ∈ NP enc :=
  ((TAUTOLOGY_coNPComplete.2 enc A hA).trans h).mem_NP ThreeSAT.mem_NP

/-- Exercise 2 §7, the converse: `NP = coNP` gives reductions in both directions. -/
example (h : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) :
    PolyTimeReducible encQBF encCNF TAUTOLOGY ThreeSAT ∧
      PolyTimeReducible encCNF encQBF ThreeSAT TAUTOLOGY :=
  (NP_eq_coNP_iff_ThreeSAT_reducible_TAUTOLOGY.1 h).symm
