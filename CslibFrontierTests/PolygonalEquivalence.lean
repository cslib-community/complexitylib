/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Equivalence
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Star

/-! Ordinary-import clients of both directions on nonloop stars of arbitrary degree. -/

namespace CslibFrontierTests.PolygonalEquivalence

open Cslib.Complexity Cslib.Complexity.Graph RotationSystem

-- The forward implication chooses the entire actual drawing, including at degree > 4.
example (n : ℕ) : ∃ D : PolygonalDrawing (starGraph n),
    D.IsEmbedding ∧ D.Realizes (starRotation n) :=
  ((starRotation n).numericalGenusZero_iff_exists_polygonalDrawing
    (starGraph_endpoints_declared n)).mp (numericalGenusZero_starRotation n)

-- Any supplied actual realization gives genus zero through the reverse implication.
example (n : ℕ) (D : PolygonalDrawing (starGraph n))
    (hD : D.IsEmbedding) (hR : D.Realizes (starRotation n)) :
    (starRotation n).NumericalGenusZero :=
  ((starRotation n).numericalGenusZero_iff_exists_polygonalDrawing
    (starGraph_endpoints_declared n)).mpr ⟨D, hD, hR⟩

-- No connectedness, nonempty incidence or unique-declaration premise is introduced.
example (r : RotationSystem ([7, 7, 1000], [])) :
    r.NumericalGenusZero ↔
      ∃ D : PolygonalDrawing ([7, 7, 1000], []), D.IsEmbedding ∧ D.Realizes r :=
  r.numericalGenusZero_iff_exists_polygonalDrawing (by decide)

end CslibFrontierTests.PolygonalEquivalence
