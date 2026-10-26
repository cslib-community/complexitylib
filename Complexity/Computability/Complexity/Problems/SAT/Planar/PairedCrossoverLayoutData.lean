/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Planar.PairedCrossover
public import Complexity.Foundations.Geometry.Orthogonal.PairedPorts
public import Complexity.Computability.Complexity.Problems.SAT.Planar.CrossoverLayoutData

/-!
# Orthogonal drawing data for the paired-port crossover

The old internal drawing is retained. Each old terminal is replaced by ports at offsets 110
and 130, with the new implication clause at the old terminal position. Only the eight old
terminal incidence routes are rerouted. The shared paired accesses end at these eight ports.

## Main definitions

* `variablePosition`, `clausePositions`, `incidenceRoutes`: the 57-variable, 78-clause drawing.
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

/-- Exact clause-to-variable incidence routes in clause and literal order. -/
def incidenceRoutes : List (ℕ × Variable × Route) :=
  [
    (0, .port 0 0, [(40, 120), (40, 119), (21, 119), (21, 110), (20, 110)]),
    (0, .copy .aInnerLeft 5, [(40, 120), (56, 120)]),
    (1, .port 0 1, [(40, 140), (37, 140), (37, 135), (33, 135), (33, 131), (29, 131), (29, 130),
      (20, 130)]),
    (1, .copy .aInnerLeft 4, [(40, 140), (40, 137), (45, 137), (45, 133), (49, 133), (49, 129),
      (53, 129), (53, 125), (56, 125), (56, 124)]),
    (2, .copy .aInnerLeft 0, [(60, 60), (59, 60), (59, 115), (60, 115), (60, 116)]),
    (2, .copy .upperLeft 0, [(60, 60), (60, 63), (65, 63), (65, 67), (69, 67), (69, 71), (73, 71),
      (73, 75), (77, 75), (77, 79), (81, 79), (81, 83), (85, 83), (85, 87), (89, 87), (89, 91),
      (93, 91), (93, 95), (96, 95), (96, 96)]),
    (2, .copy .bInnerTop 5, [(60, 60), (116, 60)]),
    (3, .copy .aInnerLeft 3, [(60, 180), (59, 180), (59, 125), (60, 125), (60, 124)]),
    (3, .copy .lowerLeft 4, [(60, 180), (60, 177), (65, 177), (65, 173), (69, 173), (69, 169), (73,
      169), (73, 165), (77, 165), (77, 161), (81, 161), (81, 157), (85, 157), (85, 153), (89, 153),
      (89, 149), (93, 149), (93, 145), (96, 145), (96, 144)]),
    (3, .copy .bInnerBottom 5, [(60, 180), (116, 180)]),
    (4, .copy .aInnerLeft 1, [(80, 100), (77, 100), (77, 105), (73, 105), (73, 109), (69, 109),
      (69, 113), (65, 113), (65, 116), (64, 116)]),
    (4, .copy .upperLeft 5, [(80, 100), (96, 100)]),
    (5, .copy .upperLeft 4, [(80, 120), (80, 117), (85, 117), (85, 113), (89, 113), (89, 109), (93,
      109), (93, 105), (96, 105), (96, 104)]),
    (5, .copy .lowerLeft 0, [(80, 120), (80, 123), (85, 123), (85, 127), (89, 127), (89, 131), (93,
      131), (93, 135), (96, 135), (96, 136)]),
    (6, .copy .aInnerLeft 2, [(80, 140), (77, 140), (77, 135), (73, 135), (73, 131), (69, 131),
      (69, 127), (65, 127), (65, 124), (64, 124)]),
    (6, .copy .lowerLeft 5, [(80, 140), (96, 140)]),
    (7, .port 2 0, [(100, 40), (100, 37), (105, 37), (105, 33), (109, 33), (109, 20), (110, 20)]),
    (7, .copy .bInnerTop 0, [(100, 40), (100, 43), (105, 43), (105, 47), (109, 47), (109, 51),
      (113, 51), (113, 55), (116, 55), (116, 56)]),
    (8, .copy .upperLeft 1, [(100, 80), (100, 96)]),
    (8, .copy .bInnerTop 4, [(100, 80), (100, 77), (105, 77), (105, 73), (109, 73), (109, 69),
      (113, 69), (113, 65), (116, 65), (116, 64)]),
    (9, .copy .upperLeft 3, [(100, 120), (100, 104)]),
    (9, .copy .lowerLeft 1, [(100, 120), (100, 136)]),
    (9, .center, [(100, 120), (120, 120)]),
    (10, .copy .lowerLeft 3, [(100, 160), (100, 144)]),
    (10, .copy .bInnerBottom 0, [(100, 160), (100, 163), (105, 163), (105, 167), (109, 167), (109,
      171), (113, 171), (113, 175), (116, 175), (116, 176)]),
    (11, .port 2 1, [(120, 40), (121, 40), (121, 21), (130, 21), (130, 20)]),
    (11, .copy .bInnerTop 1, [(120, 40), (120, 56)]),
    (12, .copy .upperLeft 2, [(120, 100), (104, 100)]),
    (12, .copy .upperRight 5, [(120, 100), (136, 100)]),
    (13, .copy .lowerLeft 2, [(120, 140), (104, 140)]),
    (13, .copy .lowerRight 5, [(120, 140), (136, 140)]),
    (14, .copy .bInnerBottom 4, [(120, 200), (120, 184)]),
    (14, .port 3 0, [(120, 200), (120, 201), (110, 201), (110, 220)]),
    (15, .copy .bInnerTop 3, [(140, 80), (137, 80), (137, 75), (133, 75), (133, 71), (129, 71),
      (129, 67), (125, 67), (125, 64), (124, 64)]),
    (15, .copy .upperRight 0, [(140, 80), (140, 96)]),
    (16, .center, [(140, 120), (120, 120)]),
    (16, .copy .upperRight 4, [(140, 120), (140, 104)]),
    (16, .copy .lowerRight 0, [(140, 120), (140, 136)]),
    (17, .copy .bInnerBottom 1, [(140, 160), (137, 160), (137, 165), (133, 165), (133, 169), (129,
      169), (129, 173), (125, 173), (125, 176), (124, 176)]),
    (17, .copy .lowerRight 4, [(140, 160), (140, 144)]),
    (18, .copy .bInnerBottom 3, [(140, 200), (140, 197), (135, 197), (135, 193), (131, 193), (131,
      189), (127, 189), (127, 185), (124, 185), (124, 184)]),
    (18, .port 3 1, [(140, 200), (137, 200), (137, 205), (133, 205), (133, 209), (133, 213), (130,
      213), (130, 220)]),
    (19, .copy .upperRight 2, [(160, 100), (144, 100)]),
    (19, .copy .aInnerRight 0, [(160, 100), (160, 103), (165, 103), (165, 107), (169, 107), (169,
      111), (173, 111), (173, 115), (176, 115), (176, 116)]),
    (20, .copy .upperRight 3, [(160, 120), (157, 120), (157, 115), (153, 115), (153, 111), (149,
      111), (149, 107), (145, 107), (145, 104), (144, 104)]),
    (20, .copy .lowerRight 1, [(160, 120), (160, 123), (155, 123), (155, 127), (151, 127), (151,
      131), (147, 131), (147, 135), (144, 135), (144, 136)]),
    (21, .copy .lowerRight 2, [(160, 140), (144, 140)]),
    (21, .copy .aInnerRight 5, [(160, 140), (160, 137), (165, 137), (165, 133), (169, 133), (169,
      129), (173, 129), (173, 125), (176, 125), (176, 124)]),
    (22, .copy .bInnerTop 2, [(180, 60), (180, 59), (125, 59), (125, 60), (124, 60)]),
    (22, .copy .upperRight 1, [(180, 60), (177, 60), (177, 65), (173, 65), (173, 69), (169, 69),
      (169, 73), (165, 73), (165, 77), (161, 77), (161, 81), (157, 81), (157, 85), (153, 85), (153,
      89), (149, 89), (149, 93), (145, 93), (145, 96), (144, 96)]),
    (22, .copy .aInnerRight 1, [(180, 60), (180, 116)]),
    (23, .copy .bInnerBottom 2, [(180, 180), (180, 181), (125, 181), (125, 180), (124, 180)]),
    (23, .copy .lowerRight 3, [(180, 180), (177, 180), (177, 175), (173, 175), (173, 171), (169,
      171), (169, 167), (165, 167), (165, 163), (161, 163), (161, 159), (157, 159), (157, 155),
      (153, 155), (153, 151), (149, 151), (149, 147), (145, 147), (145, 144), (144, 144)]),
    (23, .copy .aInnerRight 4, [(180, 180), (180, 124)]),
    (24, .copy .aInnerRight 2, [(200, 100), (197, 100), (197, 105), (193, 105), (193, 109), (189,
      109), (189, 113), (185, 113), (185, 116), (184, 116)]),
    (24, .port 1 0, [(200, 100), (200, 103), (205, 103), (205, 107), (209, 107), (209, 110), (220,
      110)]),
    (25, .copy .aInnerRight 3, [(200, 120), (184, 120)]),
    (25, .port 1 1, [(200, 120), (200, 121), (219, 121), (219, 130), (220, 130)]),
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
    (73, .copy .aInnerRight 0, [(176, 120), (176, 116)]),
    (74, .port 0 0, [(20, 120), (20, 110)]),
    (74, .port 0 1, [(20, 120), (20, 130)]),
    (75, .port 1 1, [(220, 120), (220, 130)]),
    (75, .port 1 0, [(220, 120), (220, 110)]),
    (76, .port 2 1, [(120, 20), (130, 20)]),
    (76, .port 2 0, [(120, 20), (110, 20)]),
    (77, .port 3 0, [(120, 220), (110, 220)]),
    (77, .port 3 1, [(120, 220), (130, 220)])
  ]

/-- Boundary access points agree definitionally with the shared paired interface. -/
def boundaryPort : Fin 4 → Fin 2 → Point := PairedPorts.boundaryPort

/-- Straight shared accesses to the eight degree-two terminals. -/
def accessRoute : Fin 4 → Fin 2 → Route := PairedPorts.accessRoute

/-- The terminal coordinates are exactly the shared paired-port positions. -/
theorem terminal_position (s : Fin 4) (l : Fin 2) :
    variablePosition (terminal s l) = PairedPorts.variablePosition s l := rfl

end Cslib.Logic.PL.CNF.PairedCrossover
