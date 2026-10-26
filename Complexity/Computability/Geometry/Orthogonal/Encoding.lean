/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary

/-!
# Binary encodings of orthogonal drawing data

## Main definitions

* `Cslib.Orthogonal.encPoint`: a pair of binary signed coordinates.
* `Cslib.Orthogonal.encRoute`: a framed list of such points.

## References

These encodings combine the existing signed-integer, pair and list encodings.
-/

@[expose] public section

namespace Cslib.Orthogonal

open Turing.MultiTapeTM

/-- A point is encoded by its two binary signed integer coordinates. -/
def encPoint : Point ↪ List Bool := encPair encIntBin encIntBin

/-- A route is encoded by a framed finite list of binary-coordinate points. -/
def encRoute : Route ↪ List Bool := encList encPoint

end Cslib.Orthogonal
