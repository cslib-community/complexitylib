/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
import Complexity.Computability.Complexity.Problems.SAT.Planar.Completeness

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Complexity.SAT.PlanarCompile

-- Concrete nonempty actual compiler outputs have satisfying assignments for both polarities.
example : (rawFormula [[(0, true)]]).eval (fun _ => true) = true := by decide +kernel
example : (rawFormula [[(0, false)]]).eval (fun _ => false) = true := by decide +kernel

-- The actual compact output cannot manufacture a model of contradictory unit clauses.
example : ¬ (formula [[(0, true)], [(0, false)]]).Satisfiable := by
  intro hs
  obtain ⟨τ, hτ⟩ := satisfiable_source_of_formula
    (by decide : ∀ c ∈ ([[(0, true)], [(0, false)]] : CNF ℕ), c.length ≤ 3)
    (fun v => (List.count_le_length :
      (CNF.vars ([[(0, true)], [(0, false)]] : CNF ℕ)).count v ≤
        (CNF.vars ([[(0, true)], [(0, false)]] : CNF ℕ)).length).trans (by decide)) hs
  cases hv : τ 0 <;> simp [CNF.eval, Clause.eval, Literal.eval, hv] at hτ

private def crossedSource : CNF ℕ :=
  [[(0, true), (1, true)], [(1, false), (0, true)]]

-- This instance exercises selected crossings, with different values on the two source wires.
example : crossingSites crossedSource ≠ [] := by decide +kernel

private theorem crossed_width : ∀ c ∈ crossedSource, c.length ≤ 3 := by decide

private theorem crossed_count : ∀ v, crossedSource.vars.count v ≤ 3 := by
  intro v
  by_cases h0 : v = 0
  · subst v
    decide
  by_cases h1 : v = 1
  · subst v
    decide
  simp [crossedSource, CNF.vars, Ne.symm h0, Ne.symm h1]

example : (formula crossedSource).Satisfiable := by
  apply (satisfiable_formula_iff crossed_width crossed_count).2
  exact ⟨fun v => v == 0, by decide⟩

example : (formula []).Satisfiable := by
  apply (satisfiable_formula_iff (by simp) (by simp [CNF.vars])).2
  exact ⟨fun _ => false, rfl⟩

example : ¬ (formula [[]]).Satisfiable := by
  rw [satisfiable_formula_iff (by simp) (by simp [CNF.vars])]
  rintro ⟨τ, hτ⟩
  simp [CNF.eval, Clause.eval] at hτ

-- At this actual selected crossing, horizontal true and vertical false coexist in one model.
example : ∃ σ : Variable → Bool, (rawFormula crossedSource).eval σ = true ∧
    σ ((10, 34), some Crossover.SplitVariable.aLeft) = true ∧
    σ ((10, 34), some Crossover.SplitVariable.bTop) = false := by
  let τ : ℕ → Bool := fun v => v == 0
  obtain ⟨σ, hcompat, hcross⟩ := exists_compatible_assignment crossed_width crossed_count τ
  have hh := hcompat (0, 0, (0, true)) (by decide)
    (((10, 34), some Crossover.SplitVariable.aLeft),
      ((10, 34), some Crossover.SplitVariable.aRight)) (by decide +kernel)
  have hv := hcompat (0, 1, (1, true)) (by decide)
    (((10, 34), some Crossover.SplitVariable.bTop),
      ((10, 34), some Crossover.SplitVariable.bBottom)) (by decide +kernel)
  exact ⟨σ, eval_rawFormula_complete_of_compatible crossedSource τ σ
    (fun _ ho => occurrencePath_length_ge_two ho) hcompat hcross (by decide), hh.1, hv.1⟩
