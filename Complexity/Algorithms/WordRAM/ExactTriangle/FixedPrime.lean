/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.NumericBounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.TimeBound

/-!
# Numerical support for fixed-prime Exact Triangle

`FixedPrime.timeBound` retains the conservative complete charge envelope and
`FixedPrime.timeBound_le` its aggregate product saving. `admissionWidth` and `wordBound`
provide the logarithmic admission and polynomial word envelopes from original scalar bounds.

The canonical solver is `StreamingFixedPrime`: it computes the catalogue, constructs and
consumes one physical slot at a time, and verifies original signed weights before success.
The independent `Instances` all-record producer and standalone record product/witness APIs are
separate modules.
-/
