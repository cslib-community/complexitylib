/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCounting

/-! # Exact counts and assignment correspondence of the actual paired compiler -/

open Cslib.Logic.PL Cslib.Complexity.SAT.ParsimoniousPlanar

/-- Model counts of small compiled formulas: empty source, empty clause, singleton variable,
repeated literal occurrences, tautological clause, and contradictory unit clauses. -/
example :
    (formula []).modelCount = 1 ∧
    (formula [[]]).modelCount = 0 ∧
    (formula [[(7, true)]]).modelCount = 1 ∧
    (formula [[(7, true), (7, true), (7, true)]]).modelCount = 1 ∧
    (formula [[(7, true), (7, false)]]).modelCount = 2 ∧
    (formula [[(0, true)], [(0, false)]]).modelCount = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [modelCount_formula _ (by simp) (by simp [CNF.vars])]; decide
  · rw [modelCount_formula _ (by simp) (by simp [CNF.vars])]; decide
  · rw [modelCount_formula _ (by simp) (fun _ => List.count_le_length.trans (by decide))]; decide
  · rw [modelCount_formula _ (by simp) (fun _ => List.count_le_length.trans (by decide))]; decide
  · rw [modelCount_formula _ (by simp) (fun _ => List.count_le_length.trans (by decide))]; decide
  · rw [modelCount_formula _ (by simp) (fun _ => List.count_le_length.trans (by decide))]; decide

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

/-- Crossed-source crossing sites, model counts, assignment agreement, and compaction on
sparse infinite and empty variable types. -/
example :
    crossingSites crossedSource ≠ [] ∧
    (formula crossedSource).modelCount = 2 ∧
    (rawFormula crossedSource).modelCount = 2 ∧
    (∀ (σ τ : Variable → Bool),
      (rawFormula crossedSource).eval σ = true →
      (rawFormula crossedSource).eval τ = true →
      (∀ v ∈ crossedSource.vars, sourceValue crossedSource σ v = sourceValue crossedSource τ v) →
      ∀ v ∈ (rawFormula crossedSource).vars, σ v = τ v) ∧
    (CNF.compact [[(7, true), (7, false)], [(1000000, true)]]).modelCount = 2 ∧
    (CNF.compact ([] : CNF Empty)).modelCount = 1 := by
  refine ⟨by decide +kernel, ?_, ?_,
    fun _ _ hσ hτ he => raw_assignments_agree crossed_width crossed_count hσ hτ he, ?_, ?_⟩
  · rw [modelCount_formula _ crossed_width crossed_count]; decide
  · rw [modelCount_rawFormula _ crossed_width crossed_count]; decide
  · rw [CNF.modelCount_compact]; decide
  · rw [CNF.modelCount_compact]; decide
