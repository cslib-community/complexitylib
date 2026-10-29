/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedGeometry
import Mathlib.Tactic.NormNum

/-! Actual continuous cell geometry and complete compiled drawing regressions. -/

namespace ComplexityTests.PlanarGeometry

open Cslib.Logic.PL Cslib.Orthogonal Cslib.Complexity
open SAT.ParsimoniousPlanar
open SAT.PlanarCompile (occurrencePath_nodup pathPorts_nodup pathMidpoints_nodup shared_cellPort)

-- Access and last-literal regularity, wire lengths, route counts, occurrence-path nodup,
-- shared cell ports, and disjoint access supports.
example :
    IsOrthogonal (access [] (-1, -2) (0, -2) 0) ∧
    IsSimple (access [(-1, -2)] (-1, -2) (-1, -3) 1) ∧
    IsSimple (lastLiteral [(-1, -2)] [(-1, -2), (-1, -3)] true).2 ∧
    wireLength (access [(-1, -2)] (-1, -2) (-1, -3) 0) = 20 ∧
    wireLength (lastLiteral [] [(-1, -2), (-1, -3)] true).2 = 150 ∧
    (∀ r ∈ routes [[(7, true)]], IsOrthogonal r ∧ IsSimple r) ∧
    (routes [[(7, true)]]).length =
      (SAT.incidenceGraph (formula [[(7, true)]])).2.length ∧
    (occurrencePath [[(7, true)]] (0, 0, (7, true))).Nodup ∧
    cellPort 120 (-1, -2) (side (-1, -2) (0, -2)) =
      cellPort 120 (0, -2) (side (0, -2) (-1, -2)) ∧
    Disjoint (support (access [(0, 0)] (0, 0) (-1, 0) 0))
      (support (access [(0, 0)] (0, 0) (0, 1) 0)) :=
  ⟨access_orthogonal _ _ _ _,
   access_simple _ _ _ _,
   (lastLiteral_route_regular _ _ _ (by decide)).2,
   (access_cost _ _ _ _).1,
   by decide,
   routes_regular _,
   routes_length _,
   occurrencePath_nodup (by decide),
   shared_cellPort (by decide),
   access_disjoint_same_cell _ _ _ _ _ _ (by decide)⟩

private def crossed : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(1, true), (0, true), (2, false)]]

-- Even three repeated incidences between the same original vertices use distinct cell ports,
-- positions, routes, and midpoints; empty clauses, parallel incidences, and `crossed` all yield
-- planar orthogonal drawings.
example :
    ((paths [[(7, true), (7, false), (7, true)]]).flatMap fun r =>
      r.consecutivePairs.flatMap fun e =>
        [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]).Nodup ∧
    (positions [[(7, true), (7, false), (7, true)]]).Nodup ∧
    (routes [[(7, true), (7, false), (7, true)]]).Nodup ∧
    (positions [[], []]).Nodup ∧
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula []))
      (positions [], routes []) ∧
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula [[], []]))
      (positions [[], []], routes [[], []]) ∧
    Graph.IsPlanarOrthogonalDrawing
      (SAT.incidenceGraph (formula [[(7, true), (7, false), (7, true)]]))
      (positions [[(7, true), (7, false), (7, true)]],
        routes [[(7, true), (7, false), (7, true)]]) ∧
    (10, 42) ∈ crossingSites crossed ∧
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula crossed))
      (positions crossed, routes crossed) ∧
    ((paths [[(7, true), (7, false), (7, true)]]).flatMap fun r =>
      r.consecutivePairs.map fun e => cellPort 120 e.1 (side e.1 e.2)).Nodup := by
  have hc3 : ∀ c ∈ ([[(7, true), (7, false), (7, true)]] : CNF ℕ), c.length ≤ 3 := by
    intro c hc; obtain rfl := List.mem_singleton.mp hc; decide
  have hv3 : ∀ v, (CNF.vars [[(7, true), (7, false), (7, true)]]).count v ≤ 3 :=
    fun _ => List.count_le_length.trans (by decide)
  have hc0 : ∀ c ∈ ([[], []] : CNF ℕ), c.length ≤ 3 := by
    intro c hc; have : c = [] := by simpa using hc
    subst c; decide
  have hv0 : ∀ v, (CNF.vars ([[], []] : CNF ℕ)).count v ≤ 3 := by simp [CNF.vars]
  refine ⟨pathPorts_nodup hc3 hv3, positions_nodup hc3 hv3, routes_nodup hc3 hv3,
    positions_nodup hc0 hv0, isPlanarOrthogonalDrawing (by simp) (by simp [CNF.vars]),
    isPlanarOrthogonalDrawing hc0 hv0, isPlanarOrthogonalDrawing hc3 hv3,
    (by decide +kernel), ?_, pathMidpoints_nodup hc3 hv3⟩
  apply isPlanarOrthogonalDrawing
  · intro c hc
    simp only [crossed, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  · intro v
    by_cases hv : v ∈ crossed.vars
    · have hv' : v = 0 ∨ v = 1 ∨ v = 2 := by
        simpa [crossed, CNF.vars, or_assoc, or_left_comm, or_comm] using hv
      rcases hv' with rfl | rfl | rfl <;> decide
    · rw [List.count_eq_zero.mpr hv]
      decide

-- Continuous support includes nonintegral points of the actual paired access.
example : ((230.5 : ℝ), (110 : ℝ)) ∈ support (access [] (0, 0) (1, 0) 0) := by
  rw [access, support_cons_cons]
  apply Or.inl
  norm_num [boundary, cellOrigin, side, SAT.PlanarCompile.side, variablePosition, signal, port,
    PairedPorts.variablePosition, PairedPorts.boundaryPort, PairedPorts.offset,
    Cslib.Orthogonal.segment, realPoint, mem_horizontal, Set.mem_uIcc]

end ComplexityTests.PlanarGeometry
