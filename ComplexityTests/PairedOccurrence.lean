/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedOccurrence

/-! Repeated literals consume separate occurrence capacity in the actual paired compiler. -/

open Cslib.Logic.PL Cslib.Complexity.SAT.ParsimoniousPlanar

private def repeated : CNF ℕ := [[(0, true), (0, true), (0, true)]]

private theorem repeated_counts : ∀ v, repeated.vars.count v ≤ 3 := by
  intro v
  by_cases h : 0 = v
  · subst v
    decide
  · simp [repeated, CNF.vars, h]

example : repeated.vars.count 0 = 3 := by decide

example (v : Variable) : (rawFormula repeated).vars.count v ≤ 3 :=
  count_vars_rawFormula_le_three (by decide) repeated_counts v

example (v : ℕ) : (formula repeated).vars.count v ≤ 3 :=
  count_vars_formula_le_three (by decide) repeated_counts v
