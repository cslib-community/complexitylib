/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

import Complexity.Logics.Propositional.ClauseSet.Satisfiable

/-! Tests for satisfiability of clause sets: a satisfiable and an unsatisfiable clause set over two
variables, decided by evaluation; a clause that makes a satisfiable set unsatisfiable; relabelling
along an injective map, which preserves satisfiability, and along a map identifying two variables,
which does not; agreement with `CNF.Satisfiable`; and the width bound under relabelling. -/

namespace ComplexityTests.ClauseSetSatisfiable

open Cslib.Logic.PL

/-- `(x₀ ∨ x₁) ∧ ¬x₀`, satisfied only by `x₀ = false`, `x₁ = true`. -/
private def ψ : ClauseSet (Fin 2) := {{(0, true), (1, true)}, {(0, false)}}

/-- `x₀ ∧ ¬x₀`. -/
private def φ : ClauseSet (Fin 2) := {{(0, true)}, {(0, false)}}

example : ψ.Satisfiable := by decide

example : ¬φ.Satisfiable := by decide

-- The satisfying assignment, and a non-satisfying one.
example : ψ.Sat (fun i => i == 1) ∧ ¬ψ.Sat fun _ => true := by decide

-- Adding the clause `¬x₁` leaves no satisfying assignment.
example : ¬(ψ ∪ {{(1, false)}}).Satisfiable := by decide

-- `sat_insert_iff` splits off the inserted clause: the only satisfying assignment of `ψ` falsifies
-- `¬x₁`.
example : ¬(insert {(1, false)} ψ).Sat fun i => i == 1 := by
  simp only [ClauseSet.sat_insert_iff, not_and]
  decide

-- An injective relabelling preserves satisfiability, by the lemma and by evaluation.
example : (ψ.relabel (Fin.succ : Fin 2 → Fin 3)).Satisfiable :=
  (ClauseSet.satisfiable_relabel (Fin.succ_injective 2) ψ).mpr (by decide)

example : (ψ.relabel (Fin.succ : Fin 2 → Fin 3)).Satisfiable := by decide

-- Identifying `x₀` and `x₁` turns `ψ` into `y ∧ ¬y`: injectivity is needed.
example : ¬(ψ.relabel fun _ : Fin 2 => (0 : Fin 1)).Satisfiable := by decide

-- The assignment `σ` satisfies the relabelled set exactly when `σ ∘ f` satisfies `ψ`.
example : (ψ.relabel (Fin.succ : Fin 2 → Fin 3)).Sat fun i => i != 1 :=
  (ClauseSet.sat_relabel_iff _ ψ _).mpr (by decide)

example : ψ.toCNF.Satisfiable := (ClauseSet.satisfiable_toCNF_iff ψ).mpr (by decide)

example : ¬φ.toCNF.Satisfiable := by
  rw [ClauseSet.satisfiable_toCNF_iff]
  decide

-- A formula listing the clauses of `φ` is unsatisfiable, and so is its clause set again.
example : ¬φ.toCNF.toClauseSet.Satisfiable := by
  rw [CNF.satisfiable_toClauseSet_iff, ClauseSet.satisfiable_toCNF_iff]
  decide

-- Relabelling keeps clauses of width at most `2`.
example : ∀ C ∈ ψ.relabel (Fin.succ : Fin 2 → Fin 3), C.card ≤ 2 :=
  fun _ hC => ClauseSet.card_le_of_mem_relabel (by decide) hC

end ComplexityTests.ClauseSetSatisfiable
