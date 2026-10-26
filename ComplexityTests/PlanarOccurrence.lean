/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedOccurrence

/-! Literal-position regressions for the paired compiler and its shared canonical paths. -/

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Complexity.SAT.ParsimoniousPlanar
open Cslib.Complexity.SAT.PlanarCompile (occurrencePaths_eq_paths)

private def repeated : CNF ℕ := [[(0, true), (0, false), (0, true)]]

example : (Cslib.Logic.PL.occurrences repeated).map (occurrencePath repeated) = paths repeated :=
  occurrencePaths_eq_paths _

private theorem repeated_width : ∀ c ∈ repeated, c.length ≤ 3 := by
  intro c hc
  simp only [repeated, List.mem_singleton] at hc
  subst c
  decide

private theorem repeated_count : ∀ v, repeated.vars.count v ≤ 3 := by
  intro v
  by_cases hv : v = 0
  · subst v
    decide
  · simp [repeated, CNF.vars, Ne.symm hv]

-- All three source literal positions are preserved in the degree accounting, including repeats.
example : repeated.vars.count 0 = 3 := by decide

example : ∀ v, (formula repeated).vars.count v ≤ 3 :=
  count_vars_formula_le_three repeated_width repeated_count

private def crossed : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(1, true), (0, true), (2, false)]]

private theorem crossed_width : ∀ c ∈ crossed, c.length ≤ 3 := by
  intro c hc
  simp only [crossed, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

private theorem crossed_count : ∀ v, crossed.vars.count v ≤ 3 := by
  intro v
  by_cases hv : v ∈ crossed.vars
  · have hv' : v = 0 ∨ v = 1 ∨ v = 2 := by
      simpa [crossed, CNF.vars, or_assoc, or_left_comm, or_comm] using hv
    rcases hv' with rfl | rfl | rfl <;> decide
  · rw [List.count_eq_zero.mpr hv]
    decide

example : ∀ v, (rawFormula crossed).vars.count v ≤ 3 :=
  count_vars_rawFormula_le_three crossed_width crossed_count

example : ∀ v, (formula crossed).vars.count v ≤ 3 :=
  count_vars_formula_le_three crossed_width crossed_count

-- Empty formulas and unsatisfiable empty clauses introduce no unbounded wire-variable case.
example : ∀ v, (formula []).vars.count v ≤ 3 :=
  count_vars_formula_le_three (by simp) (by simp [CNF.vars])

example : ∀ v, (formula [[]]).vars.count v ≤ 3 :=
  count_vars_formula_le_three (by simp) (by simp [CNF.vars])
