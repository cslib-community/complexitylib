/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.Occurrence

/-! Literal-position counting regressions for actual planarization paths. -/

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Complexity.SAT.PlanarCompile Cslib.Orthogonal

private def repeated : CNF ℕ := [[(0, true), (0, false), (0, true)]]

example : (Cslib.Logic.PL.occurrences repeated).Nodup := Cslib.Logic.PL.occurrences_nodup _

example : (Cslib.Logic.PL.occurrences repeated).map (occurrencePath repeated) = paths repeated :=
  occurrencePaths_eq_paths _

example : (pathSignals [] [(0, 0), (1, 0), (2, 0)]).count ((1, 0), none) = 2 := by decide

example : (pathSignals [] [(0, 0), (1, 0), (2, 0)]).count ((0, 0), none) = 1 := by decide

example : (pathSignals [(1, 0)] [(0, 0), (1, 0), (2, 0)]).count
    ((1, 0), some (Crossover.splitTerminal 0)) = 1 := by decide

example : (pathSignals [(1, 0)] [(0, 0), (1, 0), (2, 0)]).count
    ((1, 0), some (Crossover.splitTerminal 1)) = 1 := by decide

example : (pathSignals [(1, 0)] [(0, 0), (1, 0), (2, 0)]).count ((1, 0), none) = 0 := by decide

example (positive : Bool) :
    (CNF.vars ((links [] positive [(0, 0), (1, 0), (2, 0)]).map Prod.fst)).count ((1, 0), none) +
      [(lastLiteral [] [(0, 0), (1, 0), (2, 0)] positive).1.1].count ((1, 0), none) ≤ 2 := by
  simpa only [show (pathSignals [] [(0, 0), (1, 0), (2, 0)]).count ((1, 0), none) = 2 by decide]
    using count_links_lastLiteral_le [] positive [(0, 0), (1, 0), (2, 0)] (by decide) ((1, 0), none)

example (i : Fin 4) : Crossover.splitFormula.vars.count (Crossover.splitTerminal i) = 2 :=
  count_vars_splitTerminal i

example (v : Crossover.SplitVariable) : Crossover.splitFormula.vars.count v ≤ 3 :=
  count_vars_splitFormula v

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

-- This actual compiler input selects a strict bridge/stem crossing at (10,42).
private theorem crossing_selected : (10, 42) ∈ crossingSites crossed := by decide +kernel

example (i : Fin 4) : (allPathSignals crossed).count
    ((10, 42), some (Crossover.splitTerminal i)) ≤ 1 :=
  count_allPathSignals_terminal_le_one crossed_width crossed_count _ i crossing_selected

example (i : Fin 4) : (crossingSignals crossed).count
    ((10, 42), some (Crossover.splitTerminal i)) = 2 := by
  rw [count_crossingSignals_some, count_vars_splitTerminal]
  have hpos := List.count_pos_iff.mpr crossing_selected
  have hle := List.nodup_iff_count_le_one.mp (crossingSites_nodup crossed) (10, 42)
  omega

example : ∀ v, (rawFormula crossed).vars.count v ≤ 3 :=
  count_vars_rawFormula_le_three crossed_width crossed_count

example : ∀ v, (formula crossed).vars.count v ≤ 3 :=
  count_vars_formula_le_three crossed_width crossed_count

-- Empty formulas and unsatisfiable empty clauses introduce no unbounded wire-variable case.
example : ∀ v, (formula []).vars.count v ≤ 3 :=
  count_vars_formula_le_three (by simp) (by simp [CNF.vars])

example : ∀ v, (formula [[]]).vars.count v ≤ 3 :=
  count_vars_formula_le_three (by simp) (by simp [CNF.vars])
