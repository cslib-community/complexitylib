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

example :
    repeated.vars.count 0 = 4 ∧
    repeated.toThreeOccurrence.length = 6 ∧
    repeated.toThreeOccurrence.vars.length = 12 ∧
    repeated.toThreeOccurrence.numVars = 4 ∧
    repeated ∉ ThreeSATThree ∧
    toThreeSATThree repeated ∈ ThreeSATThree ∧
    (toThreeSATThree []).Satisfiable ∧
    ¬ (toThreeSATThree [[]]).Satisfiable ∧
    toThreeSATThree [[(7, true), (7, true), (7, true), (7, true)]] = [[]] ∧
    toThreeSATThree [[(0, true)], [(0, false)]] ∉ ThreeSATThree ∧
    toThreeSATThree [[(2 ^ 100, true)]] ∈ ThreeSATThree ∧
    (CNF.implicationCycle [0, 1, 2]).eval (fun v => v == 1) = false ∧
    (CNF.implicationCycle [0, 1, 2]).eval (fun _ => false) = true ∧
    (CNF.implicationCycle [0]).vars.count 0 = 2 ∧
    (CNF.implicationCycle ([] : List ℕ)).eval (fun _ => true) = true := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_,
    ⟨fun _ => false, rfl⟩, ?_, by decide, ?_, ?_, by decide, by decide, by decide, rfl⟩
  · intro h
    have := h.2.1 0
    change 4 ≤ 3 at this
    omega
  · rw [mem_ThreeSATThree_toThreeSATThree_iff]
    refine ⟨?_, ⟨fun _ => true, by decide⟩⟩
    intro c hc
    simp only [repeated, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  · intro h
    have := (CNF.satisfiable_relabel ThreeSATThree.numberCopy_injective _).1 h
    have := (CNF.satisfiable_toThreeOccurrence ([[]] : CNF ℕ)).1 this
    simp [CNF.Satisfiable] at this
  · rw [mem_ThreeSATThree_toThreeSATThree_iff]
    rintro ⟨_, σ, hσ⟩
    cases hv : σ 0 <;> simp [CNF.eval, Clause.eval, Literal.eval, hv] at hσ
  · rw [mem_ThreeSATThree_toThreeSATThree_iff]
    exact ⟨by simp, ⟨fun _ => true, by simp [Literal.eval]⟩⟩
