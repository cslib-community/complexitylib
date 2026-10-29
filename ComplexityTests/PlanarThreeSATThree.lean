/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.PlanarThreeSATThree

namespace ComplexityTests.PlanarThreeSATThree

open Cslib.Complexity Cslib.Logic.PL

private theorem emptyDrawing : Graph.IsPlanarOrthogonalDrawing
    (SAT.incidenceGraph ([] : CNF ℕ)) ([], []) := by
  refine ⟨rfl, rfl, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [SAT.incidenceGraph, Cslib.Logic.PL.occurrences]

example : ([] : CNF ℕ) ∈ PlanarThreeSATThree := by
  refine ⟨⟨?_, ?_, ⟨fun _ => false, rfl⟩⟩, ⟨([], []), emptyDrawing⟩⟩
  · simp
  · simp [CNF.vars]

example : ([[]] : CNF ℕ) ∉ PlanarThreeSATThree := by
  simp [PlanarThreeSATThree, ThreeSATThree, CNF.Satisfiable]

example : ThreeSATThree.syntaxCheck [[(0, true), (0, true), (0, false)]] = true := by decide
example : ThreeSATThree.syntaxCheck [[(0, true)], [(0, true)], [(0, true)], [(0, true)]] =
    false := by decide

-- Width and literal-count violations independently trigger the total rejection branch.
example : toDrawnPlanarThreeSATThree [[(0, true), (1, true), (2, true), (3, true)]] =
    ([[]], [(0, 0)], []) := by decide +kernel
example : toDrawnPlanarThreeSATThree [[(0, true)], [(0, false)], [(0, true)], [(0, false)]] =
    ([[]], [(0, 0)], []) := by decide +kernel

-- A succinct binary label takes the actual paired compilation branch.
example : (toPlanarThreeSATThree [[(2 ^ 100, true)]]).length = 319 := by
  change (SAT.ParsimoniousPlanar.formula [[(2 ^ 100, true)]]).length = 319
  rw [SAT.ParsimoniousPlanar.length_formula]
  decide +kernel

-- Original 3SAT inputs use the occurrence splitter before the geometric compiler.
example : (toPlanarThreeSAT [[(7, true)]]).Satisfiable := by
  apply (satisfiable_toPlanarThreeSAT_iff _).2
  exact ⟨by decide, ⟨fun _ => true, rfl⟩⟩

example : (toPlanarThreeSAT [[(7, false)]]).Satisfiable := by
  apply (satisfiable_toPlanarThreeSAT_iff _).2
  exact ⟨by decide, ⟨fun _ => false, rfl⟩⟩

example : ¬(toPlanarThreeSAT [[(7, true)], [(7, false)]]).Satisfiable := by
  intro h
  obtain ⟨_, σ, hs⟩ := (satisfiable_toPlanarThreeSAT_iff _).1 h
  cases hv : σ 7 <;> simp [CNF.eval, Clause.eval, Literal.eval, hv] at hs

-- The quantitative statement measures the composed output against original clause/literal size.
example : Graph.drawingFits (toDrawnPlanarThreeSAT [[(2 ^ 100, true)]]).2 40320 40320 :=
  toDrawnPlanarThreeSAT_fits _

-- The final language theorem includes the generated continuous drawing certificate.
example : toDrawnPlanarThreeSAT [[(2 ^ 100, true)]] ∈ DrawnPlanarThreeSATThree := by
  apply (mem_DrawnPlanarThreeSATThree_toDrawnPlanarThreeSAT_iff _).2
  exact ⟨by decide, ⟨fun _ => true, rfl⟩⟩

-- Rejection still emits a valid isolated-vertex drawing, but cannot enter the SAT language.
example : Graph.IsPlanarOrthogonalDrawing
    (SAT.incidenceGraph (toPlanarThreeSATThree
      [[(0, true), (1, true), (2, true), (3, true)]]))
    (toDrawnPlanarThreeSATThree [[(0, true), (1, true), (2, true), (3, true)]]).2 :=
  isPlanarOrthogonalDrawing_toDrawnPlanarThreeSATThree _

example : ([[]], [(0, 0)], []) ∉ DrawnPlanarThreeSATThree := by
  simp [DrawnPlanarThreeSATThree, ThreeSATThree, CNF.Satisfiable]

-- The paired-port variable and placed-clause encodings are computable via `FinEnum`.
example : SAT.ParsimoniousPlanar.encVariable ((0, 0), .inl (0, 0)) ≠
    SAT.ParsimoniousPlanar.encVariable ((0, 0), .inr .center) := by decide +kernel

example : (SAT.ParsimoniousPlanar.encPlacedClause
    ([(((0, 0), .inl (0, 0)), true)], (0, 0), [[(0, 0)]])).isEmpty = false := by decide +kernel

end ComplexityTests.PlanarThreeSATThree
