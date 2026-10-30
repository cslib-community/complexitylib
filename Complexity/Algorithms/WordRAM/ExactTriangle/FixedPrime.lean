/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.SourceBounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.TimeBound

/-!
# Complete native ExactTriangle decision at a fixed admitted prime

`FixedPrime.runs_input` executes one concrete 416-register standard-native program from the
original signed input, with actual preparation once, all computed catalogue records and
original-weight witness verification. Its same-state prefix/halt verdict is equivalent to
original `HasZeroTriangle`; a successful state retains the original coordinates.

`FixedPrime.timeBound_le` derives all-instance queried-product charges and one global
false-positive scan budget. Preparation costs at most `690n²Dg`, product charges at most
`138412032(19m+1)n³g/D^(1/18)`, with explicit additional root/query/controller and original
scan terms. The total actual scans satisfy `S ≤ F(p)+returnedFlag`: empty/failed records do
not each receive a successful-scan allowance. The runtime order is the producer's actual
chunk-major order, without a precomputed record list or a clean-workspace premise.

All initialized results require `D=4^m≥16`, `n≥D^18`, `g≥1`, the stated prime window and the
original signed magnitude bound. The original-input threshold is positive, logarithmic for
polynomial weights and bounded scalar headers, and works at every wider physical width.
`FixedPrime.bounded_reachable_original` derives polynomial words and zero support above an
original-input envelope independent of that larger width. The code never reads word width,
has at most 133152 flat slots including halt, and performs no whole-window clear or snapshot.

Global parameter/prime selection, unrestricted small geometry and the complete aggregate
source exponent remain separate. This component does not complete ordinary 3SUM 1.9992.
The stage execution lemmas in the submodules are internal implementation interfaces.
-/
