/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal

/-!
# Local orthogonal drawings for parsimonious exact-one gadgets

The three fixed drawings fit in `[0,180]²`. Their core vertices and routes lie in
`[20,160]²`; access routes run from designated side midpoints to their terminals.
The unsigned incidence signatures deliberately leave clause semantics to the logical gadgets.

## Main definitions

* `LocalGeometry`: finite vertex, incidence, and access data for a local replacement.
* `disjunctionGeometry`: the four-clause parsimonious disjunction replacement.
* `falseGeometry`: the three-clause positive gadget with a forced-false exterior terminal.
* `complementGeometry`: a positive two-terminal gadget forcing opposite values.

## References

The incidence graphs are from [HuntMaratheRadhakrishnanStearns1998, Theorem 3.8,
Figures 3.4–3.5 and Lemma 3.6]. The orthogonal coordinates and routes are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

/-- An incidence records its clause index, variable index, and clause-to-variable route. -/
abbrev LocalIncidence := ℕ × ℕ × Route

/-- Finite local replacement data. Variables and clauses have separate zero-based indices.
`terminalVariables`, `boundaryPorts`, and `accessRoutes` have corresponding orders. -/
structure LocalGeometry where
  /-- Common square side length; the elementary templates use 180. -/
  size : ℕ := 180
  /-- Positions in variable-index order. -/
  variablePositions : List Point
  /-- Positions in clause-index order. -/
  clausePositions : List Point
  /-- Routes with their incident clause and variable indices. -/
  incidenceRoutes : List LocalIncidence
  /-- Variables exposed to the exterior. -/
  terminalVariables : List ℕ
  /-- Exterior endpoints of the access routes. -/
  boundaryPorts : List Point
  /-- Boundary-to-terminal routes. -/
  accessRoutes : List Route

namespace LocalGeometry

/-- Indexed variable position; valid incidence indices are certified separately. -/
def variablePosition (g : LocalGeometry) (v : ℕ) : Point :=
  g.variablePositions.getD v (0, 0)

/-- Indexed clause position; valid incidence indices are certified separately. -/
def clausePosition (g : LocalGeometry) (i : ℕ) : Point :=
  g.clausePositions.getD i (0, 0)

/-- Permitted contacts of two incidence routes: their shared graph endpoints. -/
def commonEndpoints (g : LocalGeometry) (e f : LocalIncidence) : List Point :=
  (if e.1 = f.1 then [g.clausePosition e.1] else []) ++
    (if e.2.1 = f.2.1 then [g.variablePosition e.2.1] else [])

end LocalGeometry

/-- The four-clause disjunction gadget. Variables are `p,q,r,u,v,w,t,x` in that order;
the incidence signature is `[[p,u,v],[q,u,w],[v,w,t],[r,v,x]]`.
The boundary terminals are `p,q,r`, with north, west, and east accesses. -/
def disjunctionGeometry : LocalGeometry where
  variablePositions :=
    [(20, 20), (20, 100), (140, 20), (40, 60),
      (100, 40), (70, 100), (100, 120), (160, 40)]
  clausePositions := [(40, 40), (40, 100), (100, 100), (140, 40)]
  incidenceRoutes :=
    [(0, 0, [(40, 40), (20, 40), (20, 20)]),
      (0, 3, [(40, 40), (40, 60)]),
      (0, 4, [(40, 40), (100, 40)]),
      (1, 1, [(40, 100), (20, 100)]),
      (1, 3, [(40, 100), (40, 60)]),
      (1, 5, [(40, 100), (70, 100)]),
      (2, 4, [(100, 100), (100, 40)]),
      (2, 5, [(100, 100), (70, 100)]),
      (2, 6, [(100, 100), (100, 120)]),
      (3, 2, [(140, 40), (140, 20)]),
      (3, 4, [(140, 40), (100, 40)]),
      (3, 7, [(140, 40), (160, 40)])]
  terminalVariables := [0, 1, 2]
  boundaryPorts := [(90, 0), (0, 90), (180, 90)]
  accessRoutes :=
    [[(90, 0), (90, 10), (20, 10), (20, 20)],
      [(0, 90), (10, 90), (10, 100), (20, 100)],
      [(180, 90), (170, 90), (170, 20), (140, 20)]]

/-- The positive forced-false gadget. Variables are `c,d,e,f`; the three clauses have
signature `[[c,d,e],[c,e,f],[d,e,f]]`. The terminal `c` has a north access. -/
def falseGeometry : LocalGeometry where
  variablePositions := [(80, 20), (20, 100), (80, 60), (140, 100)]
  clausePositions := [(40, 40), (120, 40), (80, 120)]
  incidenceRoutes :=
    [(0, 0, [(40, 40), (40, 20), (80, 20)]),
      (0, 1, [(40, 40), (20, 40), (20, 100)]),
      (0, 2, [(40, 40), (40, 60), (80, 60)]),
      (1, 0, [(120, 40), (120, 20), (80, 20)]),
      (1, 2, [(120, 40), (120, 60), (80, 60)]),
      (1, 3, [(120, 40), (140, 40), (140, 100)]),
      (2, 1, [(80, 120), (20, 120), (20, 100)]),
      (2, 2, [(80, 120), (80, 60)]),
      (2, 3, [(80, 120), (140, 120), (140, 100)])]
  terminalVariables := [0]
  boundaryPorts := [(80, 0)]
  accessRoutes := [[(80, 0), (80, 20)]]

/-- A positive complement gadget: one clause on `p,q,c` followed by the forced-false
gadget on `c,d,e,f`. The terminals `p,q` have west and east accesses. -/
def complementGeometry : LocalGeometry where
  variablePositions :=
    [(20, 20), (140, 20), (80, 60), (20, 140), (80, 100), (140, 140)]
  clausePositions := [(80, 20), (40, 80), (120, 80), (80, 160)]
  incidenceRoutes :=
    [(0, 0, [(80, 20), (20, 20)]),
      (0, 1, [(80, 20), (140, 20)]),
      (0, 2, [(80, 20), (80, 60)]),
      (1, 2, [(40, 80), (40, 60), (80, 60)]),
      (1, 3, [(40, 80), (20, 80), (20, 140)]),
      (1, 4, [(40, 80), (40, 100), (80, 100)]),
      (2, 2, [(120, 80), (120, 60), (80, 60)]),
      (2, 4, [(120, 80), (120, 100), (80, 100)]),
      (2, 5, [(120, 80), (140, 80), (140, 140)]),
      (3, 3, [(80, 160), (20, 160), (20, 140)]),
      (3, 4, [(80, 160), (80, 100)]),
      (3, 5, [(80, 160), (140, 160), (140, 140)])]
  terminalVariables := [0, 1]
  boundaryPorts := [(0, 90), (180, 90)]
  accessRoutes :=
    [[(0, 90), (10, 90), (10, 20), (20, 20)],
      [(180, 90), (170, 90), (170, 20), (140, 20)]]

end Cslib.Complexity.SAT.ExactOne
