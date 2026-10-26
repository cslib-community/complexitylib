/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathData
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathAssignments
public import Complexity.Computability.Complexity.Problems.SAT.Incidence
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalLayout
public import Complexity.Foundations.Geometry.Orthogonal.Subdivision
public import Complexity.Foundations.Geometry.Orthogonal.Macrocell
public import Complexity.Computability.Complexity.Problems.SAT.Planar.CrossoverLayout
public import Complexity.Logics.Propositional.CNF.Compact

/-!
# Finite orthogonal planarization data

The compiler replaces each integer unit of an incidence route by a square of side 240.
An ordinary occupied square contains one signal variable. A crossing square contains the
fixed degree-three crossover. Each step between squares contributes one binary implication,
except the last step into an original clause, which supplies its original literal incidence.
The implication direction depends on that literal's polarity.

This module defines the actual finite output, including clause positions and incidence routes.
Correctness and resource certificates are separate from these executable definitions.

## Main definitions

* `Cslib.Complexity.SAT.PlanarCompile.paths`: bounded unit expansions of canonical routes.
* `Cslib.Complexity.SAT.PlanarCompile.crossingSites`: occupied nonvertex crossing candidates.
* `Cslib.Complexity.SAT.PlanarCompile.placedClauses`: clauses with their geometric data.
* `Cslib.Complexity.SAT.PlanarCompile.rawFormula`, `formula`: structured and compact outputs.

## References

The global assembly is original. The fixed crossover is credited in `Crossover`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- A clause, its position, and one route per literal in literal order. -/
abbrev PlacedClause := Clause Variable × Point × List Route

/-- Geometric position of a structured output variable. -/
def variablePosition (v : Variable) : Point :=
  cellOrigin 120 v.1 + v.2.elim (120, 120) Crossover.variablePosition

/-- A route from a cell's side midpoint to its presented signal. -/
def access (sites : List Point) (p q : Point) : Route :=
  if p ∈ sites then translate (cellOrigin 120 p) (Crossover.accessRoute (side p q))
  else [cellPort 120 p (side p q), center p]

/-- One implication at the common side midpoint of adjacent occupied cells.
Positive literals propagate toward the source, negative literals toward the clause. -/
def link (sites : List Point) (positive : Bool) (p q : Point) : PlacedClause :=
  let a := signal sites p q
  let b := signal sites q p
  let ra := access sites p q
  let rb := access sites q p
  (if positive then [(b, false), (a, true)] else [(a, false), (b, true)],
    cellPort 120 p (side p q), if positive then [rb, ra] else [ra, rb])

/-- Link clauses along an occurrence path, omitting its final step into the original clause. -/
def links (sites : List Point) (positive : Bool) (r : Route) : List PlacedClause :=
  r.dropLast.consecutivePairs.map fun e => link sites positive e.1 e.2

/-- The final signal and incidence route replacing one original literal. -/
def lastLiteral (sites : List Point) (r : Route) (positive : Bool) : Literal Variable × Route :=
  let p := r.getD (r.length - 2) (0, 0)
  let q := r.getLastD (0, 0)
  ((signal sites p q, positive), center q :: access sites p q)

/-- Original clauses retain their order and literal polarities. -/
def originalClauses (φ : CNF ℕ) (sites : List Point) : List PlacedClause :=
  φ.zipIdx.map fun (c, i) =>
    let ls := c.zipIdx.map fun (l, j) =>
      lastLiteral sites (occurrencePath φ (i, j, l)) l.2
    (ls.map Prod.fst, center (Layout.center (φ.distinctVars.length + i)), ls.map Prod.snd)

/-- The translated fixed gadget in a crossing square. -/
def crossingClauses (p : Point) : List PlacedClause :=
  Crossover.splitFormula.zipIdx.map fun (c, i) =>
    (c.relabel (fun v => (p, some v)),
      cellOrigin 120 p + Crossover.clausePositions.getD i (0, 0),
      (Crossover.incidenceRoutes.filter fun e => e.1 == i).map fun e =>
        translate (cellOrigin 120 p) e.2.2)

/-- The complete finite output, with all original, crossover and link clauses. -/
def placedClauses (φ : CNF ℕ) : List PlacedClause :=
  let sites := crossingSites φ
  originalClauses φ sites ++ sites.flatMap crossingClauses ++
    (Cslib.Logic.PL.occurrences φ).flatMap fun o => links sites o.2.2.2 (occurrencePath φ o)

/-- The planarization formula before compacting its structured variable names. -/
def rawFormula (φ : CNF ℕ) : CNF Variable := (placedClauses φ).map Prod.fst

/-- Compact natural-number labels, using the existing CNF compaction operation. -/
def formula (φ : CNF ℕ) : CNF ℕ := (rawFormula φ).compact

/-- Positions in the order of the output's distinct variables, then of its clauses. -/
def positions (φ : CNF ℕ) : List Point :=
  ((rawFormula φ).distinctVars.map variablePosition) ++
    ((placedClauses φ).map fun c => c.2.1)

/-- Incidence routes in output clause order and literal order. -/
def routes (φ : CNF ℕ) : List Route := (placedClauses φ).flatMap fun c => c.2.2

end Cslib.Complexity.SAT.PlanarCompile
