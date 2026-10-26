/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Geometry.Orthogonal.Subdivision
import Complexity.Foundations.Geometry.Orthogonal.Layout

/-! Regression instances for signed unit subdivision and continuous support preservation. -/

open Cslib.Orthogonal

private def signedRoute : Route := [(-2, 1), (1, 1), (1, -1)]

private theorem signedRoute_orthogonal : IsOrthogonal signedRoute := by
  norm_num [signedRoute, IsOrthogonal, AxisAligned, List.consecutivePairs, Prod.mk.injEq]

example : subdivide [] = [] := rfl

example : subdivide [(3, -4)] = [(3, -4)] := rfl

example : subdivide signedRoute =
    [(-2, 1), (-1, 1), (0, 1), (1, 1), (1, 0), (1, -1)] := by decide

example : segmentWalk (1, -1) (1, 2) = [(1, -1), (1, 0), (1, 1), (1, 2)] := by decide

example : segmentWalk (2, 0) (-1, 0) = [(2, 0), (1, 0), (0, 0), (-1, 0)] := by decide

example : (subdivide signedRoute).length = 6 := by decide

example : wireLength (subdivide signedRoute) = 5 := by decide

example : (subdivide signedRoute).head? = some (-2, 1) := by decide

example : (subdivide signedRoute).getLast? = some (1, -1) := by decide

example : support (subdivide signedRoute) = support signedRoute :=
  support_subdivide signedRoute_orthogonal

example : ∀ e ∈ (subdivide signedRoute).consecutivePairs, length e.1 e.2 = 1 :=
  fun _ he => subdivide_unit signedRoute_orthogonal he

example : IsOrthogonal (subdivide signedRoute) := subdivide_orthogonal signedRoute_orthogonal

example : subdivideWithin 5 signedRoute = subdivide signedRoute :=
  subdivideWithin_eq_of_wireLength_le signedRoute_orthogonal (by decide)

example : subdivideWithin 2 signedRoute ≠ subdivide signedRoute := by decide

example : subdivideWithin 0 signedRoute = [(1, -1)] := by decide

example : Turing.MultiTapeTM.ComputableInPolyTime
    (fun p : ℕ × Route => subdivideWithin p.1 p.2)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary encRoute) encRoute :=
  computableInPolyTime_subdivideWithin

example : (subdivide (Layout.route 2 0 0 1 1 2)).Nodup :=
  subdivide_nodup (Layout.route_orthogonal (by decide) (by decide) (by decide) 1 2)
    (Layout.route_simple (by decide) (by decide) (by decide) 1 2)

private def selfCrossing : Route := [(0, 1), (2, 1), (2, 0), (1, 0), (1, 2)]

-- Distinct listed vertices alone do not prevent a repeated point after unit subdivision.
example : selfCrossing.Nodup := by decide

example : ¬ (subdivide selfCrossing).Nodup := by decide
