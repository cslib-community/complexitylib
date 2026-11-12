/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity

/-!
# Literal clockwise realization by polygonal drawings

The circular order on `Real.Angle` increases counterclockwise. The three germ arguments
below are deliberately reversed: `c,b,a` expresses the clockwise order `a,b,c` in the fixed
complex plane. Thus the existing forward `rotate` is clockwise and its
`faceNext = rotate⁻¹ ∘ reversal` retains the right-side face convention.

The predicate compares all distinct incident triples and requires distinct outgoing rays.
It includes the degree-zero, one and two cases without choosing a cyclic starting point or
allowing reflection. This is an original definition on actual segment germs. No numerical
or geometric equivalence theorem is claimed by this module.

## Main definitions

* `Cslib.Complexity.Graph.PolygonalDrawing.Realizes`: literal clockwise germ realization.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

variable {G : Graph} (D : PolygonalDrawing G)

/-- A drawing realizes a rotation if its nonzero, distinct incident germs have exactly
the literal clockwise circular order of the rotation. Distinct triples exclude interval
endpoints, so the existing half-open rotation interval gives strict betweenness here. -/
structure Realizes (r : RotationSystem G) : Prop where
  /-- Directions come from nondegenerate actual end segments. -/
  nonzero : ∀ d, D.germ d ≠ 0
  /-- Two different darts at one vertex have different outgoing geometric rays. -/
  directions_injective : ∀ a b, a.vertex = b.vertex → D.direction a = D.direction b → a = b
  /-- In the fixed complex orientation, the forward rotation follows clockwise order. -/
  clockwise : ∀ a b c, a.vertex = b.vertex → b.vertex = c.vertex →
    a ≠ b → b ≠ c → a ≠ c →
      (sbtw (D.direction c) (D.direction b) (D.direction a) ↔ b ∈ r.rotationInterval a c)

/-- Clockwise and counterclockwise order of the same three distinct germs cannot both
hold. This pins the geometric convention independently of any face-count calculation. -/
theorem Realizes.not_counterclockwise {D : PolygonalDrawing G} {r : RotationSystem G}
    (h : D.Realizes r) (a b c : Dart G) (hab : a.vertex = b.vertex)
    (hbc : b.vertex = c.vertex) (hneab : a ≠ b) (hnebc : b ≠ c) (hneac : a ≠ c)
    (hmem : b ∈ r.rotationInterval a c) :
    ¬sbtw (D.direction a) (D.direction b) (D.direction c) :=
  ((h.clockwise a b c hab hbc hneab hnebc hneac).mpr hmem).not_sbtw

end Cslib.Complexity.Graph.PolygonalDrawing
