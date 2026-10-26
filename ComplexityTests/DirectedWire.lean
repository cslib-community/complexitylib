/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
import Complexity.Logics.Propositional.CNF.Planar.DirectedWire

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.CNF.DirectedWire

-- A positive wire rejects a true clause-side value with a false source-side value.
example : (links true [(0, 0), (1, 1)]).eval (fun n : ℕ => n == 1) = false := by decide

-- A negative wire rejects a false clause-side value with a true source-side value.
example : (links false [(0, 0), (1, 1)]).eval (fun n : ℕ => n == 0) = false := by decide

-- Aliased endpoints still contribute two literal occurrences to a binary gap clause.
example : (links true [((), ()), ((), ())]).vars.count () = 2 := by decide

private def unitSource : CNF Unit := [[((), true)]]
private def contradiction : CNF Unit := [[((), true)], [((), false)]]
private def testWire (o : Occurrence Unit) : List (ℕ × ℕ) := [(0, 0), (o.1 + 1, o.1 + 1)]

-- A nonempty compatible wire assembly genuinely has a satisfying assignment.
example : (assemble unitSource testWire 0).Satisfiable := by
  refine ⟨fun _ => true, ?_⟩
  apply eval_assemble_complete unitSource testWire 0 (fun _ => true) (fun _ => true)
  · intro o _
    exact List.cons_ne_nil _ _
  · intro o _
    simp [testWire]
  · decide

-- Sharing the actual source variable across opposite unit clauses preserves unsatisfiability.
example : ¬ (assemble contradiction testWire 0).Satisfiable := by
  rintro ⟨σ, hs⟩
  have hsource := eval_assemble_sound contradiction testWire 0 (fun _ => σ 0) σ
    (fun _ _ => List.cons_ne_nil _ _)
    (by intro o _; simp [testWire]) (by intro o _; rfl) hs
  cases hσ : σ 0 <;> simp [contradiction, CNF.eval, Clause.eval, Literal.eval, hσ] at hsource

-- Empty formulas and empty clauses retain their usual meanings.
example : (assemble ([] : CNF Unit) testWire 0).eval (fun _ => false) = true := by decide
example : (assemble ([[]] : CNF Unit) testWire 0).eval (fun _ => false) = false := by decide
