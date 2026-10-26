/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.ThreeSATThree

/-! # 3SAT-3: repetitions, empty inputs, and binary labels -/

open Cslib.Logic.PL Cslib.Complexity

/-- Repeated literals must be split even when they occur within a single clause. -/
private def repeated : CNF ℕ := [[(0, true), (0, true), (0, true)], [(0, true)]]

example : repeated.vars.count 0 = 4 := by decide

example : repeated.toThreeOccurrence.length = 6 := by decide

example : repeated.toThreeOccurrence.vars.length = 12 := by decide

example : repeated.toThreeOccurrence.numVars = 4 := by decide

example : repeated ∉ ThreeSATThree := by
  intro h
  have := h.2.1 0
  change 4 ≤ 3 at this
  omega

example : toThreeSATThree repeated ∈ ThreeSATThree := by
  rw [mem_ThreeSATThree_toThreeSATThree_iff]
  refine ⟨?_, ⟨fun _ => true, ?_⟩⟩
  · intro c hc
    simp only [repeated, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  · decide

example : (toThreeSATThree []).Satisfiable := ⟨fun _ => false, rfl⟩

example : ¬ (toThreeSATThree [[]]).Satisfiable := by
  intro h
  have := (CNF.satisfiable_relabel ThreeSATThree.numberCopy_injective _).1 h
  have := (CNF.satisfiable_toThreeOccurrence ([[]] : CNF ℕ)).1 this
  simp [CNF.Satisfiable] at this

/-- A non-width-three input maps to the fixed no-instance even if it is satisfiable. -/
example : toThreeSATThree [[(7, true), (7, true), (7, true), (7, true)]] = [[]] := by decide

/-- Contradictory unit clauses remain a no-instance. -/
example : toThreeSATThree [[(0, true)], [(0, false)]] ∉ ThreeSATThree := by
  rw [mem_ThreeSATThree_toThreeSATThree_iff]
  rintro ⟨_, σ, hσ⟩
  cases hv : σ 0 <;> simp [CNF.eval, Clause.eval, Literal.eval, hv] at hσ

/-- The original label is large in value but short in its binary encoding. -/
example : toThreeSATThree [[(2 ^ 100, true)]] ∈ ThreeSATThree := by
  rw [mem_ThreeSATThree_toThreeSATThree_iff]
  exact ⟨by simp, ⟨fun _ => true, by simp [Literal.eval]⟩⟩

example : (CNF.implicationCycle [0, 1, 2]).eval (fun v => v == 1) = false := by decide

example : (CNF.implicationCycle [0, 1, 2]).eval (fun _ => false) = true := by decide

/-- A singleton cycle contains both occurrences of its variable. -/
example : (CNF.implicationCycle [0]).vars.count 0 = 2 := by decide

example : (CNF.implicationCycle ([] : List ℕ)).eval (fun _ => true) = true := rfl
