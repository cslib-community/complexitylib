/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.Planar.PairedCrossover
public import CslibFrontier.Foundations.Geometry.Orthogonal.PairedPorts
public import CslibFrontier.Computability.Complexity.Problems.SAT.Planar.CrossoverLayoutData

/-!
# Orthogonal drawing data for the paired-port crossover

The old internal drawing is retained. Each old terminal is replaced by ports at offsets 110
and 130, with the new implication clause at the old terminal position. Only the eight old
terminal incidence routes are rerouted. The shared paired accesses end at these eight ports.

## Main definitions

* `variablePosition`, `clausePositions`, `incidenceRoutes`: the 57-variable, 78-clause drawing.
  `incidenceRoutes` is the old route table lifted by `liftIncidence`, plus the bridge routes.
* `accessRoute`: the eight accesses from `Orthogonal.PairedPorts`.

## References

The unchanged core comes from [Lichtenstein1982, Figs. 4–5] and [Tromino2025, Fig. 8(b)].
The paired terminal modification is original.
Source credit for the core is in `CrossoverLayoutData`.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.PairedCrossover

open Orthogonal

/-- The eight new ports use the shared paired interface; other vertices keep their positions. -/
def variablePosition : Variable → Point
  | .port s l => PairedPorts.variablePosition s l
  | .center => Crossover.variablePosition .center
  | .copy v i => Crossover.variablePosition (.copy v i)

/-- The old clause positions followed by the four old terminal positions. -/
def clausePositions : List Point :=
  Crossover.clausePositions ++ [(20, 120), (220, 120), (120, 20), (120, 220)]

/-- An incidence route of the old drawing in the paired drawing. The eight old terminal
incidences are rerouted to the lane of the port that replaces their terminal, as chosen by
`mapLiteral`; every other route is kept. -/
def liftIncidence : ℕ × Crossover.SplitVariable × Route → ℕ × Variable × Route
  | (0, .aLeft, _) => (0, .port 0 0, [(40, 120), (40, 119), (21, 119), (21, 110), (20, 110)])
  | (1, .aLeft, _) => (1, .port 0 1, [(40, 140), (37, 140), (37, 135), (33, 135), (33, 131),
      (29, 131), (29, 130), (20, 130)])
  | (7, .bTop, _) => (7, .port 2 0, [(100, 40), (100, 37), (105, 37), (105, 33), (109, 33),
      (109, 20), (110, 20)])
  | (11, .bTop, _) => (11, .port 2 1, [(120, 40), (121, 40), (121, 21), (130, 21), (130, 20)])
  | (14, .bBottom, _) => (14, .port 3 0, [(120, 200), (120, 201), (110, 201), (110, 220)])
  | (18, .bBottom, _) => (18, .port 3 1, [(140, 200), (137, 200), (137, 205), (133, 205),
      (133, 209), (133, 213), (130, 213), (130, 220)])
  | (24, .aRight, _) => (24, .port 1 0, [(200, 100), (200, 103), (205, 103), (205, 107),
      (209, 107), (209, 110), (220, 110)])
  | (25, .aRight, _) => (25, .port 1 1, [(200, 120), (200, 121), (219, 121), (219, 130),
      (220, 130)])
  | (i, v, r) => (i, representative v, r)

/-- Exact clause-to-variable incidence routes in clause and literal order: the old routes,
lifted by `liftIncidence`, followed by the routes of the four bridge clauses. -/
def incidenceRoutes : List (ℕ × Variable × Route) :=
  Crossover.incidenceRoutes.map liftIncidence ++
    [(74, .port 0 0, [(20, 120), (20, 110)]),
     (74, .port 0 1, [(20, 120), (20, 130)]),
     (75, .port 1 1, [(220, 120), (220, 130)]),
     (75, .port 1 0, [(220, 120), (220, 110)]),
     (76, .port 2 1, [(120, 20), (130, 20)]),
     (76, .port 2 0, [(120, 20), (110, 20)]),
     (77, .port 3 0, [(120, 220), (110, 220)]),
     (77, .port 3 1, [(120, 220), (130, 220)])]

/-- Boundary access points agree definitionally with the shared paired interface. -/
def boundaryPort : Fin 4 → Fin 2 → Point := PairedPorts.boundaryPort

/-- Straight shared accesses to the eight degree-two terminals. -/
def accessRoute : Fin 4 → Fin 2 → Route := PairedPorts.accessRoute

/-- The terminal coordinates are exactly the shared paired-port positions. -/
theorem terminal_position (s : Fin 4) (l : Fin 2) :
    variablePosition (terminal s l) = PairedPorts.variablePosition s l := rfl

end Cslib.Logic.PL.CNF.PairedCrossover
