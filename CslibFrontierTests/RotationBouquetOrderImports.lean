/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.BouquetOrder

/-!
The old ordinary BouquetOrder import still exposes the moved generic ranks and its
original numerical loop-laminarity conclusion, with unchanged qualified names.
-/

namespace CslibFrontierTests.RotationBouquetOrderImports

open Cslib.Complexity Cslib.Complexity.Graph

example {G : Graph} (r : RotationSystem G) (a b : Dart G) (hab : a.vertex = b.vertex)
    (heq : r.portRank a = r.portRank b) : a = b := r.portRank_injective a b hab heq

example {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hr : r.NumericalGenusZero)
    (e f : Fin G.2.length) (hef : e ≠ f)
    (he : Dart.vertex (G := G) (e, false) = Dart.vertex (e, true))
    (hf : Dart.vertex (G := G) (f, false) = Dart.vertex (f, true))
    (hv : Dart.vertex (G := G) (e, false) = Dart.vertex (f, false)) :
    max (r.portRank (e, false)) (r.portRank (e, true)) <
        min (r.portRank (f, false)) (r.portRank (f, true)) ∨
      max (r.portRank (f, false)) (r.portRank (f, true)) <
        min (r.portRank (e, false)) (r.portRank (e, true)) ∨
      (min (r.portRank (e, false)) (r.portRank (e, true)) <
          min (r.portRank (f, false)) (r.portRank (f, true)) ∧
        max (r.portRank (f, false)) (r.portRank (f, true)) <
          max (r.portRank (e, false)) (r.portRank (e, true))) ∨
      (min (r.portRank (f, false)) (r.portRank (f, true)) <
          min (r.portRank (e, false)) (r.portRank (e, true)) ∧
        max (r.portRank (e, false)) (r.portRank (e, true)) <
          max (r.portRank (f, false)) (r.portRank (f, true))) :=
  r.portRank_loops_laminar hG hr e f hef he hf hv

end CslibFrontierTests.RotationBouquetOrderImports
