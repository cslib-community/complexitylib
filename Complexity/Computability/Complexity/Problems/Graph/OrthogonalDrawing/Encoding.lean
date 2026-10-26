/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import Complexity.Computability.Geometry.Orthogonal.Encoding

/-!
# Binary encoding of supplied orthogonal drawings

## Main definitions

* `Cslib.Complexity.Graph.encOrthogonalDrawing`: framed vertex and route lists using the
  existing binary-coordinate point encoding. Geometric certificates remain propositions.

## References

Uses the finite drawing data and binary signed-integer encodings already defined in the library.
-/

@[expose] public section

namespace Cslib.Complexity.Graph

open Turing.MultiTapeTM Orthogonal

/-- Framed vertex positions and incidence routes, with binary signed coordinates. -/
def encOrthogonalDrawing : OrthogonalDrawing ↪ List Bool := encPair encRoute (encList encRoute)

end Cslib.Complexity.Graph
