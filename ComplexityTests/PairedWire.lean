/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Logics.Propositional.CNF.Planar.PairedWire

/-! # Paired-wire directions, propagation, and exact sizes -/

open Cslib.Logic.PL Cslib.Logic.PL.CNF.PairedWire

/-- Four distinct variables per cell, with two consecutive variables per lane. -/
private def cell (index : ℕ) : Cell ℕ :=
  fun lane => (4 * index + 2 * lane.val, 4 * index + 2 * lane.val + 1)

/-- The opposite clauses use separate lanes, with the prescribed entry/exit directions. -/
example : gapClauses (cell 0) (cell 1) =
    [[(1, false), (4, true)], [(6, false), (3, true)]] := rfl

example : (links ([] : List (Cell ℕ))).length = 0 ∧
    (links ([] : List (Cell ℕ))).vars.length = 0 := by decide

example : (links [cell 0]).length = 0 ∧ (links [cell 0]).vars.length = 0 := by decide

example : (links [cell 0, cell 1, cell 2]).length = 4 ∧
    (links [cell 0, cell 1, cell 2]).vars.length = 8 := by decide

/-- Counts retain multiplicity even when all port variables coincide. -/
example : (links [fun _ => (0, 0), fun _ => (0, 0)]).length = 2 ∧
    (links [fun _ => (0, 0), fun _ => (0, 0)]).vars.length = 4 := by decide

example (value : Bool) : (links [cell 0, cell 1, cell 2]).eval (fun _ => value) = true :=
  eval_links_of_constant _ value _ (fun _ _ _ => ⟨rfl, rfl⟩)

/-- Local agreement is satisfiable when the two cells have different representative values. -/
example : ∀ c ∈ [cell 0, cell 1], c.Agree (fun v => decide (v < 4)) := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> unfold Cell.Agree <;> decide

/-- The forward implication excludes a drop from true to false between cells. -/
example : (links [cell 0, cell 1]).eval (fun v => decide (v < 4)) = false := by decide

/-- The backward implication excludes a rise from false to true between cells. -/
example : (links [cell 0, cell 1]).eval (fun v => decide (4 ≤ v)) = false := by decide

/-- Links alone allow different representatives when local agreement is absent. -/
example : (links [cell 0, cell 1]).eval (fun v => v == 4) = true ∧
    ((cell 0 0).1 == 4) ≠ ((cell 1 0).1 == 4) := by decide

/-- A compiler can recover any terminal port from local cell guarantees and satisfied links. -/
example (σ : ℕ → Bool) (hcells : ∀ c ∈ [cell 0, cell 1, cell 2], c.Agree σ)
    (hlinks : (links [cell 0, cell 1, cell 2]).eval σ = true) :
    σ (cell 2 1).2 = σ (cell 0 0).1 :=
  (agree_head σ (cell 0) [cell 1, cell 2] hcells hlinks (cell 2) (by simp) 1).2
