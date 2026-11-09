/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Incidence
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalLayout
public import Complexity.Foundations.Geometry.Orthogonal.Subdivision
public import Complexity.Foundations.Geometry.Orthogonal.Macrocell

/-!
# Canonical incidence-path data

The retained shared data consist of bounded unit paths, selected crossing cells, and the
common macrocell coordinates. No clauses, formula, or drawing are assembled here.

## Main definitions

* `Cslib.Complexity.SAT.PlanarCompile.budget`, `.paths`, `.occurrencePath`.
* `Cslib.Complexity.SAT.PlanarCompile.crossingSites`, `.side`, `.center`.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.mem_crossingSites`.
* `Cslib.Complexity.SAT.PlanarCompile.crossingSites_nodup`.

## References

These are the shared canonical incidence-path constructions and certificates.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- The explicit linear per-route expansion budget. -/
def budget (φ : CNF ℕ) : ℕ :=
  80 * (SAT.incidenceGraph φ).1.length + 10 * (SAT.incidenceGraph φ).2.length

/-- Unit paths in the order of the original literal occurrences. -/
def paths (φ : CNF ℕ) : List Route :=
  let G := SAT.incidenceGraph φ
  (G.orthogonalRoutes G.canonicalPorts).map (subdivideWithin (budget φ))

/-- The path of a particular original literal occurrence. -/
def occurrencePath (φ : CNF ℕ) (o : Occurrence ℕ) : Route :=
  (paths φ).getD ((Cslib.Logic.PL.occurrences φ).idxOf o) []

/-- Actual occupied crossing candidates, excluding every declared graph vertex center.
First-occurrence selection ensures exactly one local gadget per selected square. -/
def crossingSites (φ : CNF ℕ) : List Point :=
  let G := SAT.incidenceGraph φ
  let occupied := (G.crossingCandidates G.canonicalPorts).filter fun p =>
    !(G.orthogonalPositions.contains p) &&
      decide (2 ≤ ((paths φ).filter fun r => r.contains p).length)
  Cslib.Complexity.selectDistinct occupied (List.replicate occupied.length true)

/-- The selected cells are exactly occupied nonvertex candidates. -/
theorem mem_crossingSites (φ : CNF ℕ) (p : Point) :
    p ∈ crossingSites φ ↔
      p ∈ (SAT.incidenceGraph φ).crossingCandidates (SAT.incidenceGraph φ).canonicalPorts ∧
        p ∉ (SAT.incidenceGraph φ).orthogonalPositions ∧
          2 ≤ ((paths φ).filter fun r => r.contains p).length := by
  simp [crossingSites, mem_selectDistinct_replicate, Bool.and_eq_true]

/-- Every selected square receives exactly one template. -/
theorem crossingSites_nodup (φ : CNF ℕ) : (crossingSites φ).Nodup := nodup_selectDistinct _ _

/-- Side facing a neighboring square, in left/right/bottom/top order.
Only unit neighbors are used by the correctness theorem. -/
def side (p q : Point) : Fin 4 :=
  if q.1 < p.1 then 0 else if p.1 < q.1 then 1 else if q.2 < p.2 then 2 else 3

/-- The center of a square of side 240 indexed by an integer grid point. -/
def center (p : Point) : Point := cellOrigin 120 p + (120, 120)

/-- Unit-adjacent integer cells differ by exactly one of the four cardinal displacements. -/
theorem unit_neighbor_cases {p q : Point} (h : Orthogonal.length p q = 1) :
    q = p + (-1, 0) ∨ q = p + (1, 0) ∨ q = p + (0, -1) ∨ q = p + (0, 1) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [Orthogonal.length] at h
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  omega

/-- Neighboring unit cells use exactly the same geometric midpoint for their shared port. -/
theorem shared_cellPort {p q : Point} (h : Orthogonal.length p q = 1) :
    cellPort 120 p (side p q) = cellPort 120 q (side q p) := by
  rcases p with ⟨px, py⟩
  rcases unit_neighbor_cases h with rfl | rfl | rfl | rfl <;>
    simp [side, cellPort, cellOrigin, Prod.ext_iff] <;> omega

end Cslib.Complexity.SAT.PlanarCompile
