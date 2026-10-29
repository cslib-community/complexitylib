/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.SourceBounds

/-!
# Native ExactTriangle record-to-product adapter

## Main definitions

* `RecordProduct.program`: fixed 320-register consumer of any occupied producer record ordinal.
* `RecordProduct.entryProgram`: actual original-input producer followed by ordinal-zero selection
  and that consumer; original geometry proves the first record exists.
* `RecordProduct.leftMatrix`, `RecordProduct.rightMatrix`: the unchanged native writer's actual
  raw zero/one matrices, read in their respective row-major orders.
* `RecordProduct.admissionWidth`, `RecordProduct.wordBound`: original-header/weight bounds for
  every sufficiently wide physical execution and its complete prefix words/address support.

## Main results

* `RecordProduct.exec_of_output`: actual producer readback derives all six record words, every
  matrix/query pointer and separation, the coordinate occurrences and their sparsity; the actual
  callee returns all requested product values and preserves the producer catalogue and registers.
* `RecordProduct.runs_input`: complete native `State.init`, same-data prefix `Runs`, returned
  pointer, charged halt, exact product words, caller frame and occurrence sparsity. This fixed
  initialized client selects the first record, rather than solving all prepared instances.
* `RecordProduct.timeBound_le`: actual callee work plus `O(nD+Q)` descriptor/log/header/copy/
  invocation overhead. There is no whole-window/catalogue initialization or snapshot.
* `RecordProduct.thin_timeBound_sparse`: under `D=4^m`, `L=19m`, `D^18≤n` and `Q·2^m≤n²`, the
  per-record bound including halt is `34603008·(19m+1)·n²/D^(1/18)`. The actual chunk derives
  its occurrence bound; a mere distinct-set bound instead retains the additive occurrence term.
* `RecordProduct.admissionWidth_le_log`: original polynomial header/weight envelopes give the
  positive logarithmic threshold `(257κ+5906)·clog₂(n+2)` as a sufficient upper envelope.
* `RecordProduct.bounded_reachable_original`, `RecordProduct.wordBound_le_pow`: all wider native
  prefixes have polynomial words/support independent of the chosen physical width.

The native code computes the record stride/address, reads every descriptor word, recovers `m`
with the existing binary-logarithm program and division by two, writes original local headers,
and copies raw X/Y and all interleaved coordinate occurrences above the actual producer heap.
The entire 163-register callable bank is renamed together. Memory rebasing is performed by its
actual compiler; register renaming alone is not a memory relocation. Raw matrix entries remain
zero/one during adapter copying: the actual callee already charges their canonical-signed doubling.

`PreparationInput.exec_input` exposes the existing structured initialized producer execution,
and `PreparationInput.runs_input` reuses it without changing its statement or cost. Stage lemmas
in the submodules are internal implementation interfaces. No intermediate fits, layouts, routing
tables, run/time/solver or sparse-bound certificate is an original input hypothesis.

This is per-record composition, not an aggregate subcubic ExactTriangle solver. Global parameter
and prime selection, the outer instance loop, backend/witness reconstruction, the full ordinary
distinct-position 3SUM composition and the improved 1.9992 endpoint remain open under #1394.

## References

The existing matrix writer and queried-product mathematics retain their pinned
[AlmanWilliams2026] / Anthropic source mapping. This adapter, register framing, initialized
composition and charged native proofs are original work; they do not transfer source Light
semantics or instruction constants. The value-only matrix wrappers reuse `WriteMatrices.entry`.
-/
