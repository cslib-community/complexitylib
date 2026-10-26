/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Planar.CrossoverSplit
public import Complexity.Foundations.Geometry.Orthogonal

/-!
# Explicit orthogonal crossover data

The original straight-ray crossover is scaled by twenty. Each degree-six variable is replaced
inside its radius-four square by six occurrence variables and a cyclic implication ring. The
original incidence rays are replaced by explicit orthogonal paths in disjoint narrow corridors.
The core lies in `[20,220]²`. Four access routes connect its signal terminals to the boundary
of `[0,240]²`, using the free third incidence direction at each terminal.

## Main definitions

* `Cslib.Logic.PL.CNF.Crossover.variablePosition`: the 53 distinct variable positions.
* `Cslib.Logic.PL.CNF.Crossover.clausePositions`: the 74 clause positions.
* `Cslib.Logic.PL.CNF.Crossover.incidenceRoutes`: the 154 clause-to-variable incidence routes.

## Main results

The finite certificates for these data are in `CrossoverLayoutChecks`; their continuous
consequences are in `CrossoverLayout`.

## References

* David Lichtenstein, *Planar Formulae and Their Uses*, Figs. 4–5 [Lichtenstein1982].
* MIT–ULB CompGeom Group, *Undecidability of Tiling with a Tromino*, Fig. 8(b) [Tromino2025].

The fixed orthogonal routes and local splitting are original modifications of that grid drawing.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.Crossover

open Orthogonal

/-- Distinct positions for the five unsplit variables and the 48 local occurrence copies. -/
def variablePosition : SplitVariable → Point
  | .copy .aInnerLeft 0 => (60, 116)
  | .copy .aInnerLeft 1 => (64, 116)
  | .copy .aInnerLeft 2 => (64, 124)
  | .copy .aInnerLeft 3 => (60, 124)
  | .copy .aInnerLeft 4 => (56, 124)
  | .copy .aInnerLeft 5 => (56, 120)
  | .copy .aInnerRight 0 => (176, 116)
  | .copy .aInnerRight 1 => (180, 116)
  | .copy .aInnerRight 2 => (184, 116)
  | .copy .aInnerRight 3 => (184, 120)
  | .copy .aInnerRight 4 => (180, 124)
  | .copy .aInnerRight 5 => (176, 124)
  | .aLeft => (20, 120)
  | .aRight => (220, 120)
  | .bBottom => (120, 220)
  | .copy .bInnerBottom 0 => (116, 176)
  | .copy .bInnerBottom 1 => (124, 176)
  | .copy .bInnerBottom 2 => (124, 180)
  | .copy .bInnerBottom 3 => (124, 184)
  | .copy .bInnerBottom 4 => (120, 184)
  | .copy .bInnerBottom 5 => (116, 180)
  | .copy .bInnerTop 0 => (116, 56)
  | .copy .bInnerTop 1 => (120, 56)
  | .copy .bInnerTop 2 => (124, 60)
  | .copy .bInnerTop 3 => (124, 64)
  | .copy .bInnerTop 4 => (116, 64)
  | .copy .bInnerTop 5 => (116, 60)
  | .bTop => (120, 20)
  | .center => (120, 120)
  | .copy .lowerLeft 0 => (96, 136)
  | .copy .lowerLeft 1 => (100, 136)
  | .copy .lowerLeft 2 => (104, 140)
  | .copy .lowerLeft 3 => (100, 144)
  | .copy .lowerLeft 4 => (96, 144)
  | .copy .lowerLeft 5 => (96, 140)
  | .copy .lowerRight 0 => (140, 136)
  | .copy .lowerRight 1 => (144, 136)
  | .copy .lowerRight 2 => (144, 140)
  | .copy .lowerRight 3 => (144, 144)
  | .copy .lowerRight 4 => (140, 144)
  | .copy .lowerRight 5 => (136, 140)
  | .copy .upperLeft 0 => (96, 96)
  | .copy .upperLeft 1 => (100, 96)
  | .copy .upperLeft 2 => (104, 100)
  | .copy .upperLeft 3 => (100, 104)
  | .copy .upperLeft 4 => (96, 104)
  | .copy .upperLeft 5 => (96, 100)
  | .copy .upperRight 0 => (140, 96)
  | .copy .upperRight 1 => (144, 96)
  | .copy .upperRight 2 => (144, 100)
  | .copy .upperRight 3 => (144, 104)
  | .copy .upperRight 4 => (140, 104)
  | .copy .upperRight 5 => (136, 100)

/-- Clause positions, in precisely the order of `splitFormula`. -/
def clausePositions : List Point :=
  [
    (40, 120), (40, 140), (60, 60), (60, 180), (80, 100), (80, 120), (80, 140),
    (100, 40), (100, 80), (100, 120), (100, 160), (120, 40), (120, 100), (120, 140),
    (120, 200), (140, 80), (140, 120), (140, 160), (140, 200), (160, 100), (160, 120),
    (160, 140), (180, 60), (180, 180), (200, 100), (200, 120), (62, 116), (64, 120),
    (62, 124), (58, 124), (56, 122), (56, 116), (98, 96), (104, 96), (104, 104),
    (98, 104), (96, 102), (96, 98), (98, 136), (104, 136), (104, 144), (98, 144),
    (96, 142), (96, 138), (118, 56), (124, 56), (124, 62), (120, 64), (116, 62),
    (116, 58), (120, 176), (124, 178), (124, 182), (122, 184), (116, 184), (116, 178),
    (142, 96), (144, 98), (144, 102), (142, 104), (136, 104), (136, 96), (142, 136),
    (144, 138), (144, 142), (142, 144), (136, 144), (136, 136), (178, 116), (182, 116),
    (184, 118), (184, 124), (178, 124), (176, 120)
  ]

/-- All clause-to-variable incidence routes, in clause and literal order.
The first component is a clause index; the second is its incident variable. -/
def incidenceRoutes : List (ℕ × SplitVariable × Route) :=
  [
    (0, .aLeft, [(40, 120), (40, 119), (20, 119), (20, 120)]),
    (0, .copy .aInnerLeft 5, [(40, 120), (56, 120)]),
    (1, .aLeft,
      [(40, 140), (37, 140), (37, 135), (33, 135), (33, 131), (29, 131), (29, 127), (25, 127),
       (25, 123), (21, 123), (21, 120), (20, 120)]),
    (1, .copy .aInnerLeft 4,
      [(40, 140), (40, 137), (45, 137), (45, 133), (49, 133), (49, 129), (53, 129), (53, 125),
       (56, 125), (56, 124)]),
    (2, .copy .aInnerLeft 0, [(60, 60), (59, 60), (59, 115), (60, 115), (60, 116)]),
    (2, .copy .upperLeft 0,
      [(60, 60), (60, 63), (65, 63), (65, 67), (69, 67), (69, 71), (73, 71), (73, 75),
       (77, 75), (77, 79), (81, 79), (81, 83), (85, 83), (85, 87), (89, 87), (89, 91),
       (93, 91), (93, 95), (96, 95), (96, 96)]),
    (2, .copy .bInnerTop 5, [(60, 60), (116, 60)]),
    (3, .copy .aInnerLeft 3, [(60, 180), (59, 180), (59, 125), (60, 125), (60, 124)]),
    (3, .copy .lowerLeft 4,
      [(60, 180), (60, 177), (65, 177), (65, 173), (69, 173), (69, 169), (73, 169), (73, 165),
       (77, 165), (77, 161), (81, 161), (81, 157), (85, 157), (85, 153), (89, 153), (89, 149),
       (93, 149), (93, 145), (96, 145), (96, 144)]),
    (3, .copy .bInnerBottom 5, [(60, 180), (116, 180)]),
    (4, .copy .aInnerLeft 1,
      [(80, 100), (77, 100), (77, 105), (73, 105), (73, 109), (69, 109), (69, 113), (65, 113),
       (65, 116), (64, 116)]),
    (4, .copy .upperLeft 5, [(80, 100), (96, 100)]),
    (5, .copy .upperLeft 4,
      [(80, 120), (80, 117), (85, 117), (85, 113), (89, 113), (89, 109), (93, 109), (93, 105),
       (96, 105), (96, 104)]),
    (5, .copy .lowerLeft 0,
      [(80, 120), (80, 123), (85, 123), (85, 127), (89, 127), (89, 131), (93, 131), (93, 135),
       (96, 135), (96, 136)]),
    (6, .copy .aInnerLeft 2,
      [(80, 140), (77, 140), (77, 135), (73, 135), (73, 131), (69, 131), (69, 127), (65, 127),
       (65, 124), (64, 124)]),
    (6, .copy .lowerLeft 5, [(80, 140), (96, 140)]),
    (7, .bTop,
      [(100, 40), (100, 37), (105, 37), (105, 33), (109, 33), (109, 29), (113, 29), (113, 25),
       (117, 25), (117, 21), (120, 21), (120, 20)]),
    (7, .copy .bInnerTop 0,
      [(100, 40), (100, 43), (105, 43), (105, 47), (109, 47), (109, 51), (113, 51), (113, 55),
       (116, 55), (116, 56)]),
    (8, .copy .upperLeft 1, [(100, 80), (100, 96)]),
    (8, .copy .bInnerTop 4,
      [(100, 80), (100, 77), (105, 77), (105, 73), (109, 73), (109, 69), (113, 69), (113, 65),
       (116, 65), (116, 64)]),
    (9, .copy .upperLeft 3, [(100, 120), (100, 104)]),
    (9, .copy .lowerLeft 1, [(100, 120), (100, 136)]),
    (9, .center, [(100, 120), (120, 120)]),
    (10, .copy .lowerLeft 3, [(100, 160), (100, 144)]),
    (10, .copy .bInnerBottom 0,
      [(100, 160), (100, 163), (105, 163), (105, 167), (109, 167), (109, 171), (113, 171),
       (113, 175), (116, 175), (116, 176)]),
    (11, .bTop, [(120, 40), (121, 40), (121, 20), (120, 20)]),
    (11, .copy .bInnerTop 1, [(120, 40), (120, 56)]),
    (12, .copy .upperLeft 2, [(120, 100), (104, 100)]),
    (12, .copy .upperRight 5, [(120, 100), (136, 100)]),
    (13, .copy .lowerLeft 2, [(120, 140), (104, 140)]),
    (13, .copy .lowerRight 5, [(120, 140), (136, 140)]),
    (14, .copy .bInnerBottom 4, [(120, 200), (120, 184)]),
    (14, .bBottom, [(120, 200), (120, 220)]),
    (15, .copy .bInnerTop 3,
      [(140, 80), (137, 80), (137, 75), (133, 75), (133, 71), (129, 71), (129, 67), (125, 67),
       (125, 64), (124, 64)]),
    (15, .copy .upperRight 0, [(140, 80), (140, 96)]),
    (16, .center, [(140, 120), (120, 120)]),
    (16, .copy .upperRight 4, [(140, 120), (140, 104)]),
    (16, .copy .lowerRight 0, [(140, 120), (140, 136)]),
    (17, .copy .bInnerBottom 1,
      [(140, 160), (137, 160), (137, 165), (133, 165), (133, 169), (129, 169), (129, 173),
       (125, 173), (125, 176), (124, 176)]),
    (17, .copy .lowerRight 4, [(140, 160), (140, 144)]),
    (18, .copy .bInnerBottom 3,
      [(140, 200), (140, 197), (135, 197), (135, 193), (131, 193), (131, 189), (127, 189),
       (127, 185), (124, 185), (124, 184)]),
    (18, .bBottom,
      [(140, 200), (137, 200), (137, 205), (133, 205), (133, 209), (129, 209), (129, 213),
       (125, 213), (125, 217), (121, 217), (121, 220), (120, 220)]),
    (19, .copy .upperRight 2, [(160, 100), (144, 100)]),
    (19, .copy .aInnerRight 0,
      [(160, 100), (160, 103), (165, 103), (165, 107), (169, 107), (169, 111), (173, 111),
       (173, 115), (176, 115), (176, 116)]),
    (20, .copy .upperRight 3,
      [(160, 120), (157, 120), (157, 115), (153, 115), (153, 111), (149, 111), (149, 107),
       (145, 107), (145, 104), (144, 104)]),
    (20, .copy .lowerRight 1,
      [(160, 120), (160, 123), (155, 123), (155, 127), (151, 127), (151, 131), (147, 131),
       (147, 135), (144, 135), (144, 136)]),
    (21, .copy .lowerRight 2, [(160, 140), (144, 140)]),
    (21, .copy .aInnerRight 5,
      [(160, 140), (160, 137), (165, 137), (165, 133), (169, 133), (169, 129), (173, 129),
       (173, 125), (176, 125), (176, 124)]),
    (22, .copy .bInnerTop 2, [(180, 60), (180, 59), (125, 59), (125, 60), (124, 60)]),
    (22, .copy .upperRight 1,
      [(180, 60), (177, 60), (177, 65), (173, 65), (173, 69), (169, 69), (169, 73), (165, 73),
       (165, 77), (161, 77), (161, 81), (157, 81), (157, 85), (153, 85), (153, 89), (149, 89),
       (149, 93), (145, 93), (145, 96), (144, 96)]),
    (22, .copy .aInnerRight 1, [(180, 60), (180, 116)]),
    (23, .copy .bInnerBottom 2, [(180, 180), (180, 181), (125, 181), (125, 180), (124, 180)]),
    (23, .copy .lowerRight 3,
      [(180, 180), (177, 180), (177, 175), (173, 175), (173, 171), (169, 171), (169, 167),
       (165, 167), (165, 163), (161, 163), (161, 159), (157, 159), (157, 155), (153, 155),
       (153, 151), (149, 151), (149, 147), (145, 147), (145, 144), (144, 144)]),
    (23, .copy .aInnerRight 4, [(180, 180), (180, 124)]),
    (24, .copy .aInnerRight 2,
      [(200, 100), (197, 100), (197, 105), (193, 105), (193, 109), (189, 109), (189, 113),
       (185, 113), (185, 116), (184, 116)]),
    (24, .aRight,
      [(200, 100), (200, 103), (205, 103), (205, 107), (209, 107), (209, 111), (213, 111),
       (213, 115), (217, 115), (217, 119), (220, 119), (220, 120)]),
    (25, .copy .aInnerRight 3, [(200, 120), (184, 120)]),
    (25, .aRight, [(200, 120), (220, 120)]),
    (26, .copy .aInnerLeft 0, [(62, 116), (60, 116)]),
    (26, .copy .aInnerLeft 1, [(62, 116), (64, 116)]),
    (27, .copy .aInnerLeft 1, [(64, 120), (64, 116)]),
    (27, .copy .aInnerLeft 2, [(64, 120), (64, 124)]),
    (28, .copy .aInnerLeft 2, [(62, 124), (64, 124)]),
    (28, .copy .aInnerLeft 3, [(62, 124), (60, 124)]),
    (29, .copy .aInnerLeft 3, [(58, 124), (60, 124)]),
    (29, .copy .aInnerLeft 4, [(58, 124), (56, 124)]),
    (30, .copy .aInnerLeft 4, [(56, 122), (56, 124)]),
    (30, .copy .aInnerLeft 5, [(56, 122), (56, 120)]),
    (31, .copy .aInnerLeft 5, [(56, 116), (56, 120)]),
    (31, .copy .aInnerLeft 0, [(56, 116), (60, 116)]),
    (32, .copy .upperLeft 0, [(98, 96), (96, 96)]),
    (32, .copy .upperLeft 1, [(98, 96), (100, 96)]),
    (33, .copy .upperLeft 1, [(104, 96), (100, 96)]),
    (33, .copy .upperLeft 2, [(104, 96), (104, 100)]),
    (34, .copy .upperLeft 2, [(104, 104), (104, 100)]),
    (34, .copy .upperLeft 3, [(104, 104), (100, 104)]),
    (35, .copy .upperLeft 3, [(98, 104), (100, 104)]),
    (35, .copy .upperLeft 4, [(98, 104), (96, 104)]),
    (36, .copy .upperLeft 4, [(96, 102), (96, 104)]),
    (36, .copy .upperLeft 5, [(96, 102), (96, 100)]),
    (37, .copy .upperLeft 5, [(96, 98), (96, 100)]),
    (37, .copy .upperLeft 0, [(96, 98), (96, 96)]),
    (38, .copy .lowerLeft 0, [(98, 136), (96, 136)]),
    (38, .copy .lowerLeft 1, [(98, 136), (100, 136)]),
    (39, .copy .lowerLeft 1, [(104, 136), (100, 136)]),
    (39, .copy .lowerLeft 2, [(104, 136), (104, 140)]),
    (40, .copy .lowerLeft 2, [(104, 144), (104, 140)]),
    (40, .copy .lowerLeft 3, [(104, 144), (100, 144)]),
    (41, .copy .lowerLeft 3, [(98, 144), (100, 144)]),
    (41, .copy .lowerLeft 4, [(98, 144), (96, 144)]),
    (42, .copy .lowerLeft 4, [(96, 142), (96, 144)]),
    (42, .copy .lowerLeft 5, [(96, 142), (96, 140)]),
    (43, .copy .lowerLeft 5, [(96, 138), (96, 140)]),
    (43, .copy .lowerLeft 0, [(96, 138), (96, 136)]),
    (44, .copy .bInnerTop 0, [(118, 56), (116, 56)]),
    (44, .copy .bInnerTop 1, [(118, 56), (120, 56)]),
    (45, .copy .bInnerTop 1, [(124, 56), (120, 56)]),
    (45, .copy .bInnerTop 2, [(124, 56), (124, 60)]),
    (46, .copy .bInnerTop 2, [(124, 62), (124, 60)]),
    (46, .copy .bInnerTop 3, [(124, 62), (124, 64)]),
    (47, .copy .bInnerTop 3, [(120, 64), (124, 64)]),
    (47, .copy .bInnerTop 4, [(120, 64), (116, 64)]),
    (48, .copy .bInnerTop 4, [(116, 62), (116, 64)]),
    (48, .copy .bInnerTop 5, [(116, 62), (116, 60)]),
    (49, .copy .bInnerTop 5, [(116, 58), (116, 60)]),
    (49, .copy .bInnerTop 0, [(116, 58), (116, 56)]),
    (50, .copy .bInnerBottom 0, [(120, 176), (116, 176)]),
    (50, .copy .bInnerBottom 1, [(120, 176), (124, 176)]),
    (51, .copy .bInnerBottom 1, [(124, 178), (124, 176)]),
    (51, .copy .bInnerBottom 2, [(124, 178), (124, 180)]),
    (52, .copy .bInnerBottom 2, [(124, 182), (124, 180)]),
    (52, .copy .bInnerBottom 3, [(124, 182), (124, 184)]),
    (53, .copy .bInnerBottom 3, [(122, 184), (124, 184)]),
    (53, .copy .bInnerBottom 4, [(122, 184), (120, 184)]),
    (54, .copy .bInnerBottom 4, [(116, 184), (120, 184)]),
    (54, .copy .bInnerBottom 5, [(116, 184), (116, 180)]),
    (55, .copy .bInnerBottom 5, [(116, 178), (116, 180)]),
    (55, .copy .bInnerBottom 0, [(116, 178), (116, 176)]),
    (56, .copy .upperRight 0, [(142, 96), (140, 96)]),
    (56, .copy .upperRight 1, [(142, 96), (144, 96)]),
    (57, .copy .upperRight 1, [(144, 98), (144, 96)]),
    (57, .copy .upperRight 2, [(144, 98), (144, 100)]),
    (58, .copy .upperRight 2, [(144, 102), (144, 100)]),
    (58, .copy .upperRight 3, [(144, 102), (144, 104)]),
    (59, .copy .upperRight 3, [(142, 104), (144, 104)]),
    (59, .copy .upperRight 4, [(142, 104), (140, 104)]),
    (60, .copy .upperRight 4, [(136, 104), (140, 104)]),
    (60, .copy .upperRight 5, [(136, 104), (136, 100)]),
    (61, .copy .upperRight 5, [(136, 96), (136, 100)]),
    (61, .copy .upperRight 0, [(136, 96), (140, 96)]),
    (62, .copy .lowerRight 0, [(142, 136), (140, 136)]),
    (62, .copy .lowerRight 1, [(142, 136), (144, 136)]),
    (63, .copy .lowerRight 1, [(144, 138), (144, 136)]),
    (63, .copy .lowerRight 2, [(144, 138), (144, 140)]),
    (64, .copy .lowerRight 2, [(144, 142), (144, 140)]),
    (64, .copy .lowerRight 3, [(144, 142), (144, 144)]),
    (65, .copy .lowerRight 3, [(142, 144), (144, 144)]),
    (65, .copy .lowerRight 4, [(142, 144), (140, 144)]),
    (66, .copy .lowerRight 4, [(136, 144), (140, 144)]),
    (66, .copy .lowerRight 5, [(136, 144), (136, 140)]),
    (67, .copy .lowerRight 5, [(136, 136), (136, 140)]),
    (67, .copy .lowerRight 0, [(136, 136), (140, 136)]),
    (68, .copy .aInnerRight 0, [(178, 116), (176, 116)]),
    (68, .copy .aInnerRight 1, [(178, 116), (180, 116)]),
    (69, .copy .aInnerRight 1, [(182, 116), (180, 116)]),
    (69, .copy .aInnerRight 2, [(182, 116), (184, 116)]),
    (70, .copy .aInnerRight 2, [(184, 118), (184, 116)]),
    (70, .copy .aInnerRight 3, [(184, 118), (184, 120)]),
    (71, .copy .aInnerRight 3, [(184, 124), (184, 120)]),
    (71, .copy .aInnerRight 4, [(184, 124), (180, 124)]),
    (72, .copy .aInnerRight 4, [(178, 124), (180, 124)]),
    (72, .copy .aInnerRight 5, [(178, 124), (176, 124)]),
    (73, .copy .aInnerRight 5, [(176, 120), (176, 124)]),
    (73, .copy .aInnerRight 0, [(176, 120), (176, 116)])
  ]

/-- Boundary access points in left/right/top/bottom order. They are geometric ports, not
additional SAT variables. An external implication route continues from this point to the
terminal. -/
def boundaryPort : Fin 4 → Point
  | 0 => (0, 120)
  | 1 => (240, 120)
  | 2 => (120, 0)
  | 3 => (120, 240)

/-- Straight access from the outer box boundary to the degree-two terminal. -/
def accessRoute (i : Fin 4) : Route :=
  [boundaryPort i, variablePosition (splitTerminal i)]

end Cslib.Logic.PL.CNF.Crossover
