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

-- Proper crossings are forbidden unless their exact contact point is allowed; disjoint route
-- bounding boxes short-circuit and certify disjoint real supports; and touching or overlapping
-- route boxes fall back to segment-piece checks.
example :
    routeContactCheck [] horizontal vertical = false ∧
      routeContactCheck [(2, 0)] horizontal vertical = true ∧
      routeBoxDisjoint horizontal [(5, -2), (5, 2)] = true ∧
      routeBoxDisjoint horizontal [(0, 2), (4, 2)] = true ∧
      Disjoint (support horizontal) (support [(5, -2), (5, 2)]) ∧
      routeContactCheck [] horizontal [(5, -2), (5, 2)] = true ∧
      routeBoxDisjoint [(0, 0), (2, 0), (2, 2)] [(0, 2), (0, 4)] = false ∧
      routeContactCheck [] [(0, 0), (2, 0), (2, 2)] [(0, 2), (0, 4)] = true ∧
      routeBoxDisjoint horizontal [(4, 0), (4, 3)] = false ∧
      routeContactCheck [] horizontal [(4, 0), (4, 3)] = false ∧
      routeBoxDisjoint horizontal [(2, 0), (6, 0)] = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    disjoint_support_of_routeBoxDisjoint (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

-- The finite certificate controls all real points of the crossing.
example {p : ℝ × ℝ} (hh : p ∈ support horizontal) (hv : p ∈ support vertical) :
    p = ((2 : ℝ), (0 : ℝ)) := by
  obtain ⟨q, hq, hp⟩ := routeContactCheck_sound
    (show routeContactCheck [(2, 0)] horizontal vertical = true by decide) hh hv
  obtain rfl := List.mem_singleton.mp hq
  simpa only [realPoint, Int.cast_ofNat, Int.cast_zero] using hp

-- Collinear overlaps, shared endpoints, singleton interior/off-edge points, empty/singleton
-- supports and diagonal half-integer intersections.
example :
    routeContactCheck [(0, 0), (2, 0), (4, 0), (6, 0)] horizontal [(2, 0), (6, 0)] = false ∧
      routeContactCheck [(4, 0)] horizontal [(4, 0), (4, 3)] = true ∧
      routeContactCheck [] horizontal [(2, 0)] = false ∧
      realPoint (2, 1) ∉ support horizontal ∧
      Disjoint (support ([] : Route)) (support horizontal) ∧
      routeContactCheck [(1, 1)] [(1, 1)] [(1, 1)] = true ∧
      routeContactCheck [] [(1, 1)] [(1, 1)] = false ∧
      segmentContactCheck [] (0, 0) (1, 1) (0, 1) (1, 0) = false ∧
      AxisAligned (0, 0) (-1, 0) :=
  ⟨by decide, by decide, by decide,
    not_mem_support_of_routeContactCheck (by decide),
    disjoint_support_of_routeContactCheck (by decide),
    by decide, by decide, by decide,
    axisAligned_of_length_eq_one (by decide)⟩

-- Removing the start of a one-segment route preserves both certificates.
example : IsOrthogonal [(4, 0)] :=
  (show IsOrthogonal horizontal by decide).of_cons

example : IsSimple [(4, 0)] :=
  (show IsSimple horizontal by simp [IsSimple, horizontal, List.consecutivePairs]).of_cons

end ComplexityTests.OrthogonalContacts
