/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Foundations.Geometry.Orthogonal.Separation
import Complexity.Foundations.Geometry.Orthogonal.Simple

/-! Finite checks and continuous geometric consequences, including forbidden overlaps. -/

namespace ComplexityTests.OrthogonalContacts

open Cslib.Orthogonal

private def horizontal : Route := [(0, 0), (4, 0)]
private def vertical : Route := [(2, -2), (2, 2)]

-- Proper crossings are forbidden unless their exact contact point is allowed.
example : routeContactCheck [] horizontal vertical = false := by decide
example : routeContactCheck [(2, 0)] horizontal vertical = true := by decide

-- The finite certificate controls all real points of the crossing.
example {p : ℝ × ℝ} (hh : p ∈ support horizontal) (hv : p ∈ support vertical) :
    p = ((2 : ℝ), (0 : ℝ)) := by
  obtain ⟨q, hq, hp⟩ := routeContactCheck_sound
    (show routeContactCheck [(2, 0)] horizontal vertical = true by decide) hh hv
  obtain rfl := List.mem_singleton.mp hq
  simpa only [realPoint, Int.cast_ofNat, Int.cast_zero] using hp

-- Listing endpoints does not permit a positive-length collinear overlap.
example : routeContactCheck [(0, 0), (2, 0), (4, 0), (6, 0)]
    horizontal [(2, 0), (6, 0)] = false := by decide

-- Adjacent segments can share their endpoint.
example : routeContactCheck [(4, 0)] horizontal [(4, 0), (4, 3)] = true := by decide

-- A singleton on the interior of an edge is detected; an off-edge vertex is excluded.
example : routeContactCheck [] horizontal [(2, 0)] = false := by decide
example : realPoint (2, 1) ∉ support horizontal :=
  not_mem_support_of_routeContactCheck (by decide)

-- Empty and singleton supports are included in the certificate's semantics.
example : Disjoint (support ([] : Route)) (support horizontal) :=
  disjoint_support_of_routeContactCheck (by decide)
example : routeContactCheck [(1, 1)] [(1, 1)] [(1, 1)] = true := by decide
example : routeContactCheck [] [(1, 1)] [(1, 1)] = false := by decide

-- These diagonal segments intersect at (1/2, 1/2), with no common integer point.
-- A certificate checking just lattice-point intersections would miss this contact.
example : segmentContactCheck [] (0, 0) (1, 1) (0, 1) (1, 0) = false := by decide

-- Tail certificates expose the actual suffix without reconstructing segment membership.
example (a : Point) (r : Route) (h : IsOrthogonal (a :: r)) : IsOrthogonal r := h.of_cons
example (a : Point) (r : Route) (h : IsSimple (a :: r)) : IsSimple r := h.of_cons
example : AxisAligned (0, 0) (-1, 0) := axisAligned_of_length_eq_one (by decide)

end ComplexityTests.OrthogonalContacts
