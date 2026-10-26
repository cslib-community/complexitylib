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

example : IsOrthogonal (access [] (-1, -2) (0, -2) 0) := access_orthogonal _ _ _ _
example : IsSimple (access [(-1, -2)] (-1, -2) (-1, -3) 1) := access_simple _ _ _ _

example : IsSimple (lastLiteral [(-1, -2)] [(-1, -2), (-1, -3)] true).2 :=
  (lastLiteral_route_regular _ _ _ (by decide)).2

example : wireLength (access [(-1, -2)] (-1, -2) (-1, -3) 0) = 20 :=
  (access_cost _ _ _ _).1

example : wireLength (lastLiteral [] [(-1, -2), (-1, -3)] true).2 = 150 := by decide

example : ∀ r ∈ routes [[(7, true)]], IsOrthogonal r ∧ IsSimple r := routes_regular _

example : (routes [[(7, true)]]).length =
    (SAT.incidenceGraph (formula [[(7, true)]])).2.length := routes_length _

example : (occurrencePath [[(7, true)]] (0, 0, (7, true))).Nodup :=
  occurrencePath_nodup (by decide)

-- Even three repeated incidences between the same original vertices use distinct cell ports.
example :
    ((paths [[(7, true), (7, false), (7, true)]]).flatMap fun r =>
      r.consecutivePairs.flatMap fun e =>
        [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]).Nodup := by
  apply pathPorts_nodup
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    decide
  · intro v
    exact List.count_le_length.trans (by decide)

example : (positions [[(7, true), (7, false), (7, true)]]).Nodup := by
  apply positions_nodup
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    decide
  · intro v
    exact List.count_le_length.trans (by decide)

-- Repeated literal occurrences have different routes as well as different midpoint clauses.
example : (routes [[(7, true), (7, false), (7, true)]]).Nodup := by
  apply routes_nodup
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    decide
  · intro v
    exact List.count_le_length.trans (by decide)

-- Repeated empty clauses still produce different geometric clause vertices.
example : (positions [[], []]).Nodup := by
  apply positions_nodup
  · intro c hc
    have : c = [] := by simpa using hc
    subst c
    decide
  · intro v
    simp [CNF.vars]

example : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula []))
    (positions [], routes []) :=
  isPlanarOrthogonalDrawing (by simp) (by simp [CNF.vars])

-- Empty clauses are isolated vertices at distinct source centers.
example : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula [[], []]))
    (positions [[], []], routes [[], []]) := by
  apply isPlanarOrthogonalDrawing
  · intro c hc
    have : c = [] := by simpa using hc
    subst c
    decide
  · intro v
    simp [CNF.vars]

-- Three parallel source incidences retain their individual ordered routes.
example : Graph.IsPlanarOrthogonalDrawing
    (SAT.incidenceGraph (formula [[(7, true), (7, false), (7, true)]]))
    (positions [[(7, true), (7, false), (7, true)]],
      routes [[(7, true), (7, false), (7, true)]]) := by
  apply isPlanarOrthogonalDrawing
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    decide
  · intro v
    exact List.count_le_length.trans (by decide)

private def crossed : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(1, true), (0, true), (2, false)]]

-- This is a selected crossing of the actual generator, rather than an assumed local site list.
example : (10, 42) ∈ crossingSites crossed := by decide +kernel

example : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula crossed))
    (positions crossed, routes crossed) := by
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

example :
    ((paths [[(7, true), (7, false), (7, true)]]).flatMap fun r =>
      r.consecutivePairs.map fun e => cellPort 120 e.1 (side e.1 e.2)).Nodup := by
  apply pathMidpoints_nodup
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    decide
  · intro v
    exact List.count_le_length.trans (by decide)

example : cellPort 120 (-1, -2) (side (-1, -2) (0, -2)) =
    cellPort 120 (0, -2) (side (0, -2) (-1, -2)) := shared_cellPort (by decide)

example : Disjoint (support (access [(0, 0)] (0, 0) (-1, 0) 0))
    (support (access [(0, 0)] (0, 0) (0, 1) 0)) :=
  access_disjoint_same_cell _ _ _ _ _ _ (by decide)

-- Continuous support includes nonintegral points of the actual paired access.
example : ((230.5 : ℝ), (110 : ℝ)) ∈ support (access [] (0, 0) (1, 0) 0) := by
  rw [access, support_cons_cons]
  apply Or.inl
  norm_num [boundary, cellOrigin, side, SAT.PlanarCompile.side, variablePosition, signal, port,
    PairedPorts.variablePosition, PairedPorts.boundaryPort, PairedPorts.offset,
    Cslib.Orthogonal.segment, realPoint, mem_horizontal, Set.mem_uIcc]

end ComplexityTests.PlanarGeometry
