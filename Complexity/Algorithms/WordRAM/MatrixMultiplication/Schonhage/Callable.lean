/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Width

/-!
# Caller-safe native queried thin products

## Main definitions

* `CallableProduct.program`: fixed standard unsigned code on 163 registers, with a runtime
  source-memory base in register 160 and an absolute answer pointer returned in register zero.
* `CallableProduct.entryProgram`, `CallableProduct.input`: actual initialized client, with a
  protected caller prefix and original raw matrices/interleaved request coordinates.
* `CallableProduct.windowSize`: explicit polynomial virtual address-space reservation;
  this interval is not initialized or copied in bulk.

## Main results

* `CallableProduct.exec`: actual caller-safe product execution from original zero/one matrices,
  arbitrary query occurrences and dirty scratch, with exact local-input restoration and full
  outside-window frame. A bounded caller state supplies physical word validity throughout.
* `CallableProduct.runs_wide`: actual `State.init` input fit, same-data prefix `Runs` and charged
  halt at every physical width at least `256*clog₂(base+N+Q+P+5)`, for caller-word bound `P`.
* `CallableProduct.runs_caller`, `CallableProduct.caller_prefix_bounded`: the corresponding
  callable flat run and every-prefix physical fit with `P` bounding all initial caller words,
  including dirty memory words loaded before the real remainder. In initialized clients,
  scratch is zero and `P` only needs to bound the protected caller prefix.
* `CallableProduct.timeBound_le`: at most three times the original charged product plus
  `2048*(N*D+Q+1)` standalone adaptation work, including halt.
* `CallableProduct.runs_thin`: at `L=19m`, `D=4^m`, `D^18≤N` and `Q*2^m≤N²`, the actual charge
  is at most `17301504*(19m+1)*N²/D^(1/18)`. Distinct-set sparsity instead retains an explicit
  additive charge for duplicate occurrences through `CallableProduct.thin_timeBound`.

The original product program is unchanged. `MemoryWindow.compile` translates each load into
actual base addition, load and remainder, each store into addition and store, and preserves
native branching/loop decisions. Computed logarithm/power setup and two linear normalization
loops are charged. Raw zero/one input is doubled by the original actual matrix-input loop.
No source-Light semantics, new ALU operation, assumed execution or fast solver is used.

The finite tensor, band and query mathematics and their source mapping remain those of
`QueriedProduct`; the compiler and callable controller are original native work. Stage APIs
are internal implementation interfaces. The concrete ET-record adapter, backend/witness
composition, whole ordinary-3SUM solver and improved 1.9992 endpoint remain open under #1394.
-/
