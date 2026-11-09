/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Width

/-!
# Caller-safe native box products with the improved finite saving

One fixed 163-register standard WordRAM program computes exact zero/one matrix
products at a runtime base, preserves caller memory outside its virtual window and
restores the complete local input, including the ordinary threshold. The actual
memory-window compiler translates all source accesses. Computed setup and exact
physical input/answer normalization are charged, without bulk window clearing.

The shared setup functions are `CallableProduct.sourceWidth`,
`CallableProduct.windowSize`, `CallableProduct.inputBase` and
`CallableProduct.admissionWidth`. The reservation is polynomial in original row and
occurrence counts, and the physical threshold is logarithmic in original caller
parameters. No computed layout, table, bounded scratch, run or time oracle is input.

## Main definitions

* `CallableBoxProduct.program`: complete caller-safe native box product.
* `CallableBoxProduct.input`: ordinary base, caller prefix, matrices, coordinates and threshold.
* `CallableBoxProduct.timeBound`: complete charged instruction ledger.

## Main results

* `CallableBoxProduct.exec`: exact answers, restored input and caller frame from original words.
* `CallableBoxProduct.runs_caller`: actual flat call from arbitrary bounded dirty caller memory.
* `CallableBoxProduct.runs_wide`: initialized execution at every admitted physical width.
* `CallableBoxProduct.runs_thin`: the same initialized execution with finite `D^(-8/125)` saving.

Correctness requires `D=4^m`, `D^18≤N`, level `21*m`, threshold at most `m`, and original
zero/one entries. The finite saving specializes to `m=9k`, threshold `k`, and
`Q*2^m≤N²`, counting every query occurrence. Polynomial factors remain explicit.
Outer Exact Triangle aggregation and the ordinary-3SUM 1.9992 endpoint remain open.
-/
