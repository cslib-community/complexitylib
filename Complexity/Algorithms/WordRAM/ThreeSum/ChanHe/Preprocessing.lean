/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingTime
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingIntermediates

/-!
# Complete native Chan–He preprocessing

One finite 128-register program per fixed exponent computes every parameter, sorts and counts
the initialized signed input, constructs the exact distinct-position frontend, builds its prime
bitmap, executes both modulus searches and every heavy/light recursion, and returns a table of
exact packed convolution instances. Counts, pointers and the common length are unsigned; packed
payloads use the existing signed encoding. Runtime code does not read physical width.

## Main definitions

This umbrella re-exports these definitions and results from its imported modules.

* `program`, `flatProgram`: structured and flat native code from `PreprocessingProgram`.
* `width`: the positive threshold `(1300κ+7865) clog₂(n+2)` from `PreprocessingWidth` derives fits.
* `cost`: all native instructions, including the final halt, from `PreprocessingInput`.

## Main results

* `runs_input`: complete `State.init` execution and exact existing `ChanHe.instances` readback.
* `cost_bound`: at most `Kκ (n+2)(sqrt(n+2)+1)(log₂(n+2)+1)^13` charged instructions.
* `intermediates_polynomial`, `space_polynomial`: every prefix at every admitted width uses only
  polynomial words and a polynomial initial address range.

The initialized-input controller, layout, native execution and resource composition are original.
The reused finite Chan–He mathematics credits Anthropic, PBC and [ChanHe2020]. No solver or source
machine simulation is assumed. This preprocessing endpoint leaves the Exact Triangle solver and
complete subquadratic 3SUM composition, including the final 1.9992 exponent, separate.
-/
