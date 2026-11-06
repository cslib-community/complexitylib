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
# Complete box-backed native Exact Triangle decision at a fixed prime

`FixedPrime.runs_input` executes the actual producer once and traverses its occupied
records with `RecordBoxProduct`, followed by the existing original-weight verifier. The
same-state prefix and halt return one exactly for `HasZeroTriangle`, and retain original
witness coordinates. Calls reuse dirty workspace and preserve the producer catalogue.

For `m = 9k`, `FixedPrime.timeBound_le` bounds aggregate product charges by
`125829120 (189k+1)^2 (9k+1) D^(-8/125) n^3 g`, with the actual producer, roots, queries,
controller and one global `F(p)+1` original-weight scan reserve stated separately. Correctness
also holds for general `m`, using the executable threshold `m/9`.

The concrete program uses 416 registers, at most 133152 flat slots including halt, and never
reads physical width. It shares `FixedPrime.admissionWidth` and `FixedPrime.wordBound`:
logarithmic admission and polynomial prefix words/support follow from original scalar bounds
and polynomial original weight magnitude. No solver, intermediate execution, clean workspace
or sparse occurrence certificate is supplied as an input hypothesis.

Parameters and the prime remain explicit admitted inputs of this component (`D >= 16`,
`n >= D^18`, `g >= 1` and the stated prime window). `ParameterSelecting.callee` computes those
values and calls this actual controller; `ThreeSum.Decision.exists_one9992_runs` composes the
complete native ordinary 3SUM endpoint. This component does not require a supplied fast solver.
-/
