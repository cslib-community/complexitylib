/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCounting

/-! # Exact counts and assignment correspondence of the actual paired compiler -/

open Cslib.Logic.PL Cslib.Complexity.SAT.ParsimoniousPlanar

/-- The empty source has one assignment on its empty variable set. -/
example : (formula []).modelCount = 1 := by
  rw [modelCount_formula _ (by simp) (by simp [CNF.vars])]
  decide

/-- An empty clause remains unsatisfiable. -/
example : (formula [[]]).modelCount = 0 := by
  rw [modelCount_formula _ (by simp) (by simp [CNF.vars])]
  decide

/-- A singleton source variable acquires no auxiliary choices. -/
example : (formula [[(7, true)]]).modelCount = 1 := by
  rw [modelCount_formula _ (by simp) (fun _ => List.count_le_length.trans (by decide))]
  decide

/-- Repeated literal occurrences remain one forced source variable. -/
example : (formula [[(7, true), (7, true), (7, true)]]).modelCount = 1 := by
  rw [modelCount_formula _ (by simp) (fun _ => List.count_le_length.trans (by decide))]
  decide

/-- A tautological source variable retains both choices. -/
example : (formula [[(7, true), (7, false)]]).modelCount = 2 := by
  rw [modelCount_formula _ (by simp) (fun _ => List.count_le_length.trans (by decide))]
  decide

/-- Contradictory source unit clauses have no output models. -/
example : (formula [[(0, true)], [(0, false)]]).modelCount = 0 := by
  rw [modelCount_formula _ (by simp) (fun _ => List.count_le_length.trans (by decide))]
  decide

/-- Both source variables occur twice, on paths with actual selected crossings. -/
private def crossedSource : CNF ℕ :=
  [[(0, true), (1, true)], [(1, false), (0, true)]]

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

example : crossingSites crossedSource ≠ [] := by decide +kernel

example : (formula crossedSource).modelCount = 2 := by
  rw [modelCount_formula _ crossed_width crossed_count]
  decide

example : (rawFormula crossedSource).modelCount = 2 := by
  rw [modelCount_rawFormula _ crossed_width crossed_count]
  decide

/-- Source values determine the actual raw models, including crossover internals. -/
example (σ τ : Variable → Bool) (hσ : (rawFormula crossedSource).eval σ = true)
    (hτ : (rawFormula crossedSource).eval τ = true)
    (he : ∀ v ∈ crossedSource.vars, sourceValue crossedSource σ v = sourceValue crossedSource τ v) :
    ∀ v ∈ (rawFormula crossedSource).vars, σ v = τ v :=
  raw_assignments_agree crossed_width crossed_count hσ hτ he

/-- First-occurrence compaction works for an infinite variable type and sparse source names. -/
example : (CNF.compact [[(7, true), (7, false)], [(1000000, true)]]).modelCount = 2 := by
  rw [CNF.modelCount_compact]
  decide

/-- Compaction also works when the variable type is empty. -/
example : (CNF.compact ([] : CNF Empty)).modelCount = 1 := by
  rw [CNF.modelCount_compact]
  decide
