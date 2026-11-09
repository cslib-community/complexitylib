/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathData
public import Complexity.Computability.Complexity.Problems.SAT.Planar.OrdinaryRing
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCrossoverLayout
public import Complexity.Foundations.Geometry.Orthogonal.PairedSpokes
public import Complexity.Logics.Propositional.CNF.Compact

/-!
# A finite compiler with paired wire ports

Canonical incidence paths and their crossing sites are reused. Each ordinary retained cell
contains a fixed implication ring whose eight ports carry the same value. A crossing cell
contains a crossover with two equal ports on each side. Each gap receives opposite implications
on its two separate ports. Consequently the adjacent signal values must agree.

Original clause cells contain no auxiliary variables. Their final incidences use one of the two
ports facing the clause, with four disjoint offset spokes inside the clause cell. Unused ports
belong to their cell's implication ring and introduce no independent choices.

## Main definitions

* `Cslib.Complexity.SAT.ParsimoniousPlanar.placedClauses`: actual clauses and geometric data.
* `Cslib.Complexity.SAT.ParsimoniousPlanar.formula`: compact natural-number output labels.
* `Cslib.Complexity.SAT.ParsimoniousPlanar.positions`, `.routes`: finite drawing data.

## References

The paired assembly is original. The crossover's source credit is documented in `PairedCrossover`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- An ordinary ring port or a local crossover variable, together with its unit-cell index. -/
abbrev Variable := Point × ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)

/-- A clause, its position, and one incidence route per literal, in literal order. -/
abbrev PlacedClause := Clause Variable × Point × List Route

/-- Reuse the already-certified canonical unit paths. -/
abbrev paths := PlanarCompile.paths

/-- Reuse the selected crossing cells. -/
abbrev crossingSites := PlanarCompile.crossingSites

/-- Reuse the occurrence-indexed canonical unit path. -/
abbrev occurrencePath := PlanarCompile.occurrencePath

/-- Side facing a unit neighbor, in left/right/bottom/top order. -/
abbrev side := PlanarCompile.side

/-- The center of a macrocell of side 240. -/
abbrev center := PlanarCompile.center

/-- All occupied retained ordinary cells, listed without repetitions. -/
def ordinaryCells (φ : CNF ℕ) : List Point :=
  let occupied := ((paths φ).flatMap List.dropLast).filter fun p => decide (p ∉ crossingSites φ)
  selectDistinct occupied (List.replicate occupied.length true)

/-- The signal variable on a particular side and lane of a cell. -/
def port (sites : List Point) (p : Point) (s : Fin 4) (lane : Fin 2) : Variable :=
  (p, if p ∈ sites then .inr (PairedCrossover.terminal s lane) else .inl (s, lane))

/-- Signal presented toward the neighboring cell on one lane. -/
def signal (sites : List Point) (p q : Point) (lane : Fin 2) : Variable :=
  port sites p (side p q) lane

/-- The actual displayed position of a structured variable. -/
def variablePosition (v : Variable) : Point :=
  cellOrigin 120 v.1 + v.2.elim
    (fun p => PairedPorts.variablePosition p.1 p.2) PairedCrossover.variablePosition

/-- The shared side point for a specified lane. -/
def boundary (p : Point) (s : Fin 4) (lane : Fin 2) : Point :=
  cellOrigin 120 p + PairedPorts.boundaryPort s lane

/-- A straight route from a cell boundary to its presented signal. -/
def access (sites : List Point) (p q : Point) (lane : Fin 2) : Route :=
  [boundary p (side p q) lane, variablePosition (signal sites p q lane)]

/-- The clause on lane zero goes forward; the clause on lane one goes backward. -/
def link (sites : List Point) (p q : Point) (lane : Fin 2) : PlacedClause :=
  let a := signal sites p q lane
  let b := signal sites q p lane
  let ra := access sites p q lane
  let rb := access sites q p lane
  (if lane = 0 then [(a, false), (b, true)] else [(b, false), (a, true)],
    boundary p (side p q) lane, if lane = 0 then [ra, rb] else [rb, ra])

/-- Two implication clauses per gap, excluding the final step into the original clause. -/
def links (sites : List Point) (r : Route) : List PlacedClause :=
  r.dropLast.consecutivePairs.flatMap fun e => [link sites e.1 e.2 0, link sites e.1 e.2 1]

/-- Final literal and its incidence route from the original clause center. -/
def lastLiteral (sites : List Point) (r : Route) (positive : Bool) : Literal Variable × Route :=
  let p := r.getD (r.length - 2) (0, 0)
  let q := r.getLastD (0, 0)
  let s := side q p
  let lane := PairedPorts.spokeLane s
  ((signal sites p q lane, positive),
    [center q, cellOrigin 120 q + PairedPorts.spokeElbow s, boundary q s lane,
      variablePosition (signal sites p q lane)])

/-- Original clauses keep their order, arity and literal signs. -/
def originalClauses (φ : CNF ℕ) (sites : List Point) : List PlacedClause :=
  φ.zipIdx.map fun (c, i) =>
    let ls := c.zipIdx.map fun (l, j) =>
      lastLiteral sites (occurrencePath φ (i, j, l)) l.2
    (ls.map Prod.fst, center (Layout.center (φ.distinctVars.length + i)), ls.map Prod.snd)

/-- The ordinary fixed implication ring in an occupied cell. -/
def ordinaryClauses (p : Point) : List PlacedClause :=
  OrdinaryRing.formula.zipIdx.map fun (c, i) =>
    (c.relabel (fun v => (p, .inl v)),
      cellOrigin 120 p + OrdinaryRing.clausePositions.getD i (0, 0),
      (OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i).map fun e =>
        translate (cellOrigin 120 p) e.2.2)

/-- The paired-port crossover in a selected crossing cell. -/
def crossingClauses (p : Point) : List PlacedClause :=
  PairedCrossover.formula.zipIdx.map fun (c, i) =>
    (c.relabel (fun v => (p, .inr v)),
      cellOrigin 120 p + PairedCrossover.clausePositions.getD i (0, 0),
      (PairedCrossover.incidenceRoutes.filter fun e => e.1 == i).map fun e =>
        translate (cellOrigin 120 p) e.2.2)

/-- The actual finite output, with no clauses for unoccupied ordinary cells. -/
def placedClauses (φ : CNF ℕ) : List PlacedClause :=
  let sites := crossingSites φ
  originalClauses φ sites ++ (ordinaryCells φ).flatMap ordinaryClauses ++
    sites.flatMap crossingClauses ++
      (Cslib.Logic.PL.occurrences φ).flatMap fun o => links sites (occurrencePath φ o)

/-- Output formula with structured variable names. -/
def rawFormula (φ : CNF ℕ) : CNF Variable := (placedClauses φ).map Prod.fst

/-- Compact natural-number labels for the actual formula. -/
def formula (φ : CNF ℕ) : CNF ℕ := (rawFormula φ).compact

/-- Positions ordered by the final formula's distinct variables, then its clauses. -/
def positions (φ : CNF ℕ) : List Point :=
  (rawFormula φ).distinctVars.map variablePosition ++ (placedClauses φ).map fun c => c.2.1

/-- Incidence routes ordered by clauses and by literal positions. -/
def routes (φ : CNF ℕ) : List Route := (placedClauses φ).flatMap fun c => c.2.2

/-- A point receives an ordinary ring exactly when a retained path uses it outside a crossing. -/
theorem mem_ordinaryCells (φ : CNF ℕ) (p : Point) :
    p ∈ ordinaryCells φ ↔
      (∃ r ∈ paths φ, p ∈ r.dropLast) ∧ p ∉ crossingSites φ := by
  simp [ordinaryCells, mem_selectDistinct_replicate, List.mem_flatMap]

/-- No ordinary ring is emitted twice. -/
theorem ordinaryCells_nodup (φ : CNF ℕ) : (ordinaryCells φ).Nodup :=
  nodup_selectDistinct _ _

/-- The compiler's presented signal always has the shared inner access position. -/
theorem signal_position (sites : List Point) (p q : Point) (l : Fin 2) :
    variablePosition (signal sites p q l) =
      cellOrigin 120 p + PairedPorts.variablePosition (side p q) l := by
  simp only [signal, port, variablePosition]
  split_ifs <;> rfl

/-- Actual accesses are translations of the fixed paired-port accesses. -/
theorem access_eq_translate (sites : List Point) (p q : Point) (l : Fin 2) :
    access sites p q l = translate (cellOrigin 120 p) (PairedPorts.accessRoute (side p q) l) := by
  rw [access, signal_position]
  simp only [boundary, PairedPorts.accessRoute, translate, List.map_cons, List.map_nil]
  simp only [add_comm]

/-- Local template of the final incidence route inside a clause cell. -/
def finalLocalRoute (s : Fin 4) : Route :=
  [(120, 120), PairedPorts.spokeElbow s, PairedPorts.boundaryPort s (PairedPorts.spokeLane s),
    cellOrigin 120 (PairedPorts.neighbor s) +
      PairedPorts.variablePosition (PairedPorts.oppositeSide s) (PairedPorts.spokeLane s)]

/-- Actual final literal routes are translations of `finalLocalRoute`. -/
theorem finalRoute_eq_translate (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) :
    [center q, cellOrigin 120 q + PairedPorts.spokeElbow (side q p),
      boundary q (side q p) (PairedPorts.spokeLane (side q p)),
      variablePosition (signal sites p q (PairedPorts.spokeLane (side q p)))] =
      translate (cellOrigin 120 q) (finalLocalRoute (side q p)) := by
  rw [signal_position]
  have hrev : Orthogonal.length q p = 1 := by
    simp only [Orthogonal.length] at h ⊢
    omega
  rcases q with ⟨x, y⟩
  rcases PlanarCompile.unit_neighbor_cases hrev with rfl | rfl | rfl | rfl <;>
    simp [translate, finalLocalRoute, side, PlanarCompile.side, center, PlanarCompile.center,
      boundary, cellOrigin, PairedPorts.neighbor, PairedPorts.oppositeSide,
      PairedPorts.variablePosition, PairedPorts.boundaryPort, PairedPorts.spokeLane,
      PairedPorts.spokeElbow, PairedPorts.offset, Prod.ext_iff] <;> omega

end Cslib.Complexity.SAT.ParsimoniousPlanar
