/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.ExactlyOne
import Complexity.Logics.Propositional.CNF.Parity
import Complexity.Logics.Propositional.ClauseSet.Basic
import Complexity.Logics.Propositional.DNF
import Complexity.Logics.Propositional.QBF
import Complexity.Computability.Complexity.Problems.SAT

/-!
# Tests for propositional normal forms, quantified Boolean formulas and SAT
-/

namespace ComplexityTests.CNF

open Cslib.Logic Cslib.Logic.PL Cslib.Complexity

/-- `(x₀ ∨ ¬x₁) ∧ x₁`. -/
def φ : CNF ℕ := [[(0, true), (1, false)], [(1, true)]]

/-- `(x₀ ∨ ¬x₁) ∧ x₁`, its verifier, and relabelling invariance. -/
example :
    φ.eval (fun _ => true) = true ∧
    φ.eval (fun v => v == 0) = false ∧
    φ.vars = [0, 1, 1] ∧
    SAT.verifier (φ, [true, true]) = true ∧
    SAT.verifier (φ, [false, false]) = false ∧
    φ ∈ SAT ∧
    ((φ.relabel (· + 7)).Satisfiable ↔ φ.Satisfiable) :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨fun _ => true, rfl⟩,
    CNF.satisfiable_relabel (add_left_injective 7) φ⟩

/-- Exactly one of three variables. -/
example :
    (CNF.exactlyOne [0, 1, 2]).eval (fun v => v == 1) = true ∧
    (CNF.exactlyOne [0, 1, 2]).eval (fun v => v != 0) = false ∧
    (CNF.exactlyOne [0, 1, 2]).eval (fun _ => false) = false := by
  decide

/-! ### Clause sets -/

/-- `φ`, its clause set, and `ClauseSet.toCNF` have the same solutions. -/
example :
    φ.toClauseSet.Sat (fun _ => true) ∧
    ¬ φ.toClauseSet.Sat (fun v => v == 0) ∧
    φ.toClauseSet.toCNF.eval (fun _ => true) = true :=
  ⟨(CNF.sat_toClauseSet_iff φ _).2 rfl,
    by rw [CNF.sat_toClauseSet_iff]; decide,
    (ClauseSet.eval_toCNF_eq_true_iff _ _).2 ((CNF.sat_toClauseSet_iff φ _).2 rfl)⟩

/-! ### Parity constraints -/

/-- The parity of `x₀, x₁` is odd under `x₀ ↦ true, x₁ ↦ false`, so the constraint for odd parity
holds and the one for even parity fails. -/
example :
    (CNF.parityOnEq ({0, 1} : Finset ℕ) true).eval (fun v => v == 0) = true ∧
    (CNF.parityOnEq ({0, 1} : Finset ℕ) false).eval (fun v => v == 0) = false :=
  ⟨(CNF.eval_parityOnEq_eq_true_iff _ _ _).2 (by decide), by
    rw [Bool.eq_false_iff, ne_eq, CNF.eval_parityOnEq_eq_true_iff]
    decide⟩

/-! ### Disjunctive normal form -/

/-- `(x₀ ∧ ¬x₁) ∨ x₁`. -/
def δ : DNF ℕ := [[(0, true), (1, false)], [(1, true)]]

/-- Evaluation of `δ` and negation of every literal into a CNF formula for `¬δ`. -/
example :
    δ.eval (fun v => v == 0) = true ∧
    δ.eval (fun _ => false) = false ∧
    CNF.eval (fun _ => false) δ.negate = true :=
  ⟨rfl, rfl, by rw [DNF.eval_negate]; rfl⟩

/-! ### Quantified Boolean formulas -/

/-- `∀ x₀, ∃ x₁, x₀ ↔ x₁` is closed and true; `∃ x₀, x₀ ∧ ¬x₀` is closed and false. -/
def θ : QBF ℕ :=
  .all 0 (.ex 1 (.or (.and (.var 0) (.var 1)) (.and (.not (.var 0)) (.not (.var 1)))))

example :
    θ.Closed ∧
    θ.eval (fun _ => false) = true ∧
    (QBF.ex 0 (.and (.var 0) (.not (.var 0)))).eval (fun _ => true) = false ∧
    θ.eval (fun v => v == 0) = true :=
  ⟨by decide, by decide, by decide,
    (QBF.eval_eq_of_closed (by decide) (fun v => v == 0) (fun _ => false)).trans (by decide)⟩

/-- CSLib logical operator typeclasses (`⊤`, `⊥`, `¬`, `∧`, `∨`, `→`, `↔`, `⋀`) on `QBF`. -/
example :
    (⊤ : QBF ℕ) = .top ∧
    (⊥ : QBF ℕ) = .bot ∧
    (¬θ) = θ.not ∧
    (θ ∧ ⊤) = θ.and .top ∧
    (θ ∨ ⊤) = θ.or .top ∧
    (θ → ⊤) = θ.imp .top ∧
    (θ ↔ ⊤) = θ.iff .top ∧
    QBF.conj [θ, ⊤] = ⋀[θ, ⊤] ∧
    θ = .all 0 (.ex 1 (.var 0 ↔ .var 1)) ∧
    (⋀([⊤, ¬⊥, ⊥ → ⊤] : List (QBF ℕ))).eval (fun _ => false) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, QBF.conj_eq_finiteAnd [θ, ⊤], rfl, rfl⟩

end ComplexityTests.CNF
