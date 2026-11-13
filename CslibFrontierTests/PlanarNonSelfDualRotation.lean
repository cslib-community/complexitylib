/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem
import Mathlib.GroupTheory.Perm.List

/-! Fixed rotation checks for the original NAND triangle reconstruction. These use the
existing listed multigraph and rotation system; no geometric realization is asserted.
The library's face successor is inverse rotation after reversal, so the stored vertex
rotation is the inverse of the clockwise `rho` in the reconstruction note. -/

namespace CslibFrontierTests.PlanarNonSelfDualRotation

open Cslib.Complexity

-- Inner edges I0,I1,I2 followed by the parallel outer edges O0,O1,O2.
private abbrev triangleGraph : Graph :=
  ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0), (0, 1), (1, 2), (2, 0)]⟩

private def triangleRho : Equiv.Perm (Graph.Dart triangleGraph) :=
  [(0, false), (3, false), (5, true), (2, true)].formPerm *
  [(1, false), (4, false), (3, true), (0, true)].formPerm *
  [(2, false), (5, false), (4, true), (1, true)].formPerm

private def triangleRotation : Graph.RotationSystem triangleGraph where
  rotate := triangleRho.symm
  sameCycle_iff := by decide +kernel

private def triangleFaces : List (List (Graph.Dart triangleGraph)) :=
  [[(0, false), (1, false), (2, false)],
   [(3, false), (0, true)],
   [(4, false), (1, true)],
   [(5, false), (2, true)],
   [(5, true), (4, true), (3, true)]]

-- These are exactly the face cycles, not just five selected walks: they partition all darts.
example : triangleFaces.flatten.Nodup ∧
    ∀ d : Graph.Dart triangleGraph, d ∈ triangleFaces.flatten := by decide +kernel

example : ∀ f ∈ triangleFaces,
    f.map triangleRotation.faceNext = f.rotate 1 := by decide +kernel

-- The bounded ternary face has its original order, without assuming its relation symmetric.
example : (triangleFaces[0]).map Graph.Dart.vertex = [0, 1, 2] := by decide

-- The clockwise outer walk is 0,2,1,0, exposing the reverse order 0,1,2.
example : (triangleFaces[4]).map Graph.Dart.vertex = [0, 2, 1] := by decide

-- The three bounded binary faces have exactly the cyclic scopes 01,12,20.
example : ((triangleFaces.drop 1).take 3).map (List.map Graph.Dart.vertex) =
    [[0, 1], [1, 2], [2, 0]] := by decide

-- The only binary intersection used for the constant lemma is three parallel edges.
private abbrev binaryGraph : Graph := ⟨[0, 1], [(0, 1), (0, 1), (0, 1)]⟩

private def binaryRho : Equiv.Perm (Graph.Dart binaryGraph) :=
  [(0, false), (2, false), (1, false)].formPerm *
  [(0, true), (1, true), (2, true)].formPerm

private def binaryRotation : Graph.RotationSystem binaryGraph where
  rotate := binaryRho.symm
  sameCycle_iff := by decide +kernel

private def binaryFaces : List (List (Graph.Dart binaryGraph)) :=
  [[(0, false), (1, true)], [(1, false), (2, true)], [(2, false), (0, true)]]

example : binaryFaces.flatten.Nodup ∧
    (∀ d : Graph.Dart binaryGraph, d ∈ binaryFaces.flatten) ∧
    (∀ f ∈ binaryFaces, f.map binaryRotation.faceNext = f.rotate 1) ∧
    binaryFaces.map (List.map Graph.Dart.vertex) = [[0, 1], [0, 1], [0, 1]] := by decide +kernel

end CslibFrontierTests.PlanarNonSelfDualRotation
