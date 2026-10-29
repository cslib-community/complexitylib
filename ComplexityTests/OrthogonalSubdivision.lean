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

private def selfCrossing : Route := [(0, 1), (2, 1), (2, 0), (1, 0), (1, 2)]

example :
    subdivide [] = [] ∧
    subdivide [(3, -4)] = [(3, -4)] ∧
    subdivide signedRoute =
      [(-2, 1), (-1, 1), (0, 1), (1, 1), (1, 0), (1, -1)] ∧
    segmentWalk (1, -1) (1, 2) = [(1, -1), (1, 0), (1, 1), (1, 2)] ∧
    segmentWalk (2, 0) (-1, 0) = [(2, 0), (1, 0), (0, 0), (-1, 0)] ∧
    (subdivide signedRoute).length = 6 ∧
    wireLength (subdivide signedRoute) = 5 ∧
    (subdivide signedRoute).head? = some (-2, 1) ∧
    (subdivide signedRoute).getLast? = some (1, -1) ∧
    subdivideWithin 2 signedRoute ≠ subdivide signedRoute ∧
    subdivideWithin 0 signedRoute = [(1, -1)] ∧
    selfCrossing.Nodup ∧
    ¬ (subdivide selfCrossing).Nodup := by
  decide

example :
    support (subdivide signedRoute) = support signedRoute ∧
    (∀ e ∈ (subdivide signedRoute).consecutivePairs, length e.1 e.2 = 1) ∧
    IsOrthogonal (subdivide signedRoute) ∧
    subdivideWithin 5 signedRoute = subdivide signedRoute ∧
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : ℕ × Route => subdivideWithin p.1 p.2)
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary encRoute) encRoute ∧
    (subdivide (Layout.route 2 0 0 1 1 2)).Nodup :=
  ⟨support_subdivide signedRoute_orthogonal,
    fun _ he => subdivide_unit signedRoute_orthogonal he,
    subdivide_orthogonal signedRoute_orthogonal,
    subdivideWithin_eq_of_wireLength_le signedRoute_orthogonal (by decide),
    computableInPolyTime_subdivideWithin,
    subdivide_nodup (Layout.route_orthogonal (by decide) (by decide) (by decide) 1 2)
      (Layout.route_simple (by decide) (by decide) (by decide) 1 2)⟩
