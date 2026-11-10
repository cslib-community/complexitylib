/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.SourceBounds
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.FixedPrime.TimeBound

/-!
# Initialized one-slot streaming ExactTriangle

`StreamingFixedPrime.runs_input` computes the immutable catalogue, then constructs each logical
chunk/piece in one physical slot. The complete box product and original-weight verifier consume
that slot at physical ordinal zero before a charged heap reset. The native loop preserves
chunk-major/piece-major order and early success, returning an original-coordinate integer-zero
witness or exhausting every logical record. A modular hit alone never suffices.

The actual program retains the existing logarithmic admission, polynomial all-prefix word and
support bounds, fixed code envelope and conservative `FixedPrime.timeBound`.
`streamingCharge_le_timeBound` proves that its construction, consumption, reset, loop and halt
charges fit this envelope. `CallableFixedPrime` uses this program through the real memory-window
compiler, so the ordinary 3SUM and ExactTriangle quantitative endpoints retain their existing
bounds.

The independent `Instances` all-record producer remains available. Its genuine `Output` supplies
a derived mathematical reference, but is never asserted for a reused slot. The slot's raw matrix
pair may be overwritten by solver work; queries, catalogue and original signed arrays remain
protected for subsequent records and calls. No dirty scratch is cleared.
-/
