/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CSP
import Complexity.Computability.Complexity.FineGrained.CountingCSP

/-!
# Tests for Boolean constraint satisfaction problems and counting CSP
-/

namespace ComplexityTests.CSP

open Cslib.Logic.PL Cslib.Complexity

/-! ### XOR constraint -/

/-- The XOR constraint on variables `x₀, x₁`: `x₀ ⊕ x₁ = 1`.
Forbidden assignments are `[false, false]` and `[true, true]`. -/
def cXor : Constraint ℕ := ⟨[0, 1], [[false, false], [true, true]]⟩

def φXor : CSP ℕ := [cXor]

theorem cXor_valid : cXor.Valid := by
  intro α hα
  simp only [cXor, List.mem_cons] at hα
  rcases hα with rfl | hα
  · rfl
  · rcases hα with rfl | hα
    · rfl
    · contradiction

example : cXor.HasWidth 2 := by
  dsimp [Constraint.HasWidth, cXor]
  decide

theorem φXor_valid : φXor.Valid := by
  intro c hc
  simp only [φXor, List.mem_singleton] at hc
  subst hc
  exact cXor_valid

theorem φXor_hasWidth2 : φXor.HasWidth 2 := by
  intro c hc
  simp only [φXor, List.mem_singleton] at hc
  subst hc
  dsimp [Constraint.HasWidth, cXor]
  decide

/-- Truth evaluations on the four local assignments. -/
example : cXor.eval (fun v => v == 0) = true := rfl
example : cXor.eval (fun v => v == 1) = true := rfl
example : cXor.eval (fun _ => false) = false := rfl
example : cXor.eval (fun _ => true) = false := rfl

/-- CNF compilation produces two clauses of width 2: `(x₀ ∨ x₁)` and `(¬x₀ ∨ ¬x₁)`. -/
example : cXor.toCNF = [[(0, true), (1, true)], [(0, false), (1, false)]] := rfl

example : φXor.toCNF = [[(0, true), (1, true)], [(0, false), (1, false)]] := rfl

/-- Preserves satisfiability. -/
example : φXor.Satisfiable := ⟨fun v => v == 1, rfl⟩

example : φXor.toCNF.Satisfiable := ⟨fun v => v == 1, rfl⟩

/-- Model count agreement on declared scopes. -/
example (declared : Finset ℕ) :
    φXor.toCNF.modelCountOn declared = φXor.modelCountOn declared :=
  CSP.modelCountOn_toCNF φXor φXor_valid declared

example : φXor.modelCount = 2 ^ (φXor.numVars - (φXor.toCNF).numVars) * (φXor.toCNF).modelCount :=
  CSP.modelCount_eq_mul_toCNF_modelCount φXor φXor_valid

/-! ### 1-in-3 SAT constraint -/

/-- The 1-in-3 SAT relation on 3 variables: exactly one is true. -/
def rOneInThree : Relation :=
  ⟨3, [[false, false, false], [false, true, true], [true, false, true],
       [true, true, false], [true, true, true]], by
    intro α hα
    simp only [List.mem_cons] at hα
    rcases hα with rfl | hα
    · rfl
    · rcases hα with rfl | hα
      · rfl
      · rcases hα with rfl | hα
        · rfl
        · rcases hα with rfl | hα
          · rfl
          · rcases hα with rfl | hα
            · rfl
            · contradiction⟩

def ΓOneInThree : Language := [rOneInThree]

theorem ΓOneInThree_hasWidth3 : ΓOneInThree.HasWidth 3 := by
  intro R hR
  simp only [ΓOneInThree, List.mem_singleton] at hR
  subst hR
  decide

def cOneInThree : Constraint ℕ := ⟨[0, 1, 2], rOneInThree.forbidden⟩

def φOneInThree : CSP ℕ := [cOneInThree]

theorem φOneInThree_inLanguage : φOneInThree.InLanguage ΓOneInThree := by
  intro c hc
  simp only [φOneInThree, List.mem_singleton] at hc
  subst hc
  refine ⟨rOneInThree, List.mem_singleton_self _, ⟨rfl, rfl⟩⟩

example : φOneInThree.Valid :=
  φOneInThree_inLanguage.valid

example : φOneInThree.HasWidth 3 :=
  φOneInThree_inLanguage.hasWidth ΓOneInThree_hasWidth3

example : cOneInThree.toCNF.length = 5 := rfl

example : (∀ cl ∈ cOneInThree.toCNF, cl.length = 3) := by
  intro cl hcl
  simp only [cOneInThree, Constraint.toCNF, rOneInThree, List.mem_map] at hcl
  obtain ⟨α, hα, rfl⟩ := hcl
  simp only [List.mem_cons] at hα
  rcases hα with rfl | hα
  · rfl
  · rcases hα with rfl | hα
    · rfl
    · rcases hα with rfl | hα
      · rfl
      · rcases hα with rfl | hα
        · rfl
        · rcases hα with rfl | hα
          · rfl
          · contradiction

/-! ### Variable containment and non-vacuity -/

example : (φXor.toCNF).vars.toFinset ⊆ φXor.vars.toFinset :=
  CSP.vars_toCNF_subset φXor

example : (φXor.toCNF).numVars ≤ φXor.numVars :=
  CSP.numVars_toCNF_le φXor

example : φXor ∈ ValidKCSP 2 := by
  rw [mem_ValidKCSP_iff φXor_hasWidth2 φXor_valid]
  exact ⟨fun v => v == 1, rfl⟩

example : φOneInThree ∈ LanguageCSP ΓOneInThree 3 := by
  rw [mem_LanguageCSP_iff ΓOneInThree_hasWidth3 φOneInThree_inLanguage]
  exact ⟨fun v => v == 0, rfl⟩

end ComplexityTests.CSP
