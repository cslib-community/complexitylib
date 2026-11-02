/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxFixedPrime.SourceBounds
public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxFixedPrime.TimeBound

/-!
# Complete box-backed native Exact Triangle decision at a fixed prime

`BoxFixedPrime.runs_input` executes the actual producer once and traverses its occupied
records with `RecordBoxProduct`, followed by the existing original-weight verifier. The
same-state prefix and halt return one exactly for `HasZeroTriangle`, and retain original
witness coordinates. Calls reuse dirty workspace and preserve the producer catalogue.

For `m = 9k`, `BoxFixedPrime.timeBound_le` bounds aggregate product charges by
`125829120 (189k+1)^2 (9k+1) D^(-8/125) n^3 g`, with the actual producer, roots, queries,
controller and one global `F(p)+1` original-weight scan reserve stated separately. Correctness
also holds for general `m`, using the executable threshold `m/9`.

The concrete program uses 416 registers, at most 133152 flat slots including halt, and never
reads physical width. It shares `FixedPrime.admissionWidth` and `FixedPrime.wordBound`:
logarithmic admission and polynomial prefix words/support follow from original scalar bounds
and polynomial original weight magnitude. No solver, intermediate execution, clean workspace
or sparse occurrence certificate is supplied as an input hypothesis.

Parameters and the prime are still explicit admitted inputs (`D >= 16`, `n >= D^18`, `g >= 1`
and the stated prime window). Connecting this program to global parameter/prime selection,
absorbing polynomial factors and proving ordinary 3SUM exponent 1.9992 remain open.
-/
