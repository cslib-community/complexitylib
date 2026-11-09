/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Thin

/-!
# Routed native box products with one shared geometry

One fixed 160-register standard WordRAM program takes original matrices, raw coordinate
occurrences and an ordinary threshold. Actual routing computes wanted codes, tile spans
and a stable permutation. The actual band producer computes shared leaf encodings.
Box geometry is constructed once; each tile constructs its retained values and executes
its actual sparse query batch, then copies answers for original-order reconstruction.
The full original input and outside memory are restored. Signed input and raw nonnegative
input modes share the same mathematical matrix product; the latter executes conversion.

## Main definitions

* `BoxProduct.program`: complete native routing, shared preparation, all tiles and restoration.
* `BoxProduct.input`: original matrices/coordinates with an appended ordinary threshold word.
* `BoxProduct.timeBound`: actual instruction ledger with geometry charged once.
* `BoxProduct.admissionWidth`: sufficient width from original scalar and magnitude envelopes.

## Main results

* `BoxProduct.exec`: caller-safe actual execution with exact matrix products and complete frame.
* `BoxProduct.runs_wide`: initialized prefix and charged halt sharing the same answer memory.
* `BoxProduct.prefix_bounded`: original-input bounds at every wider execution prefix.
* `BoxProduct.timeBound_le`: complete charged time controlled by the finite work shape.
* `BoxProduct.runs_thin`: actual initialized thin-product execution with charged finite saving.
* `BoxProduct.thin_timeBound_rpow`: finite `D^(-8/125)` saving at block parameters,
  with all polynomial depth factors and original-occurrence sparsity explicit.

The improved finite estimate uses `L=189k`, `m=9k`, `t=k`, `D=4^m`, `D^18≤N`, and
`Q*2^m≤N²`, where `Q` counts original query occurrences, including duplicates. It adapts
the finite Section 4 estimates through `BoxTradeoff` and uses an original algebraic block
specialization. It imports no source machine, solver or runtime law. Polynomial-factor
absorption, Exact Triangle replacement and ordinary-3SUM exponent 1.9992 remain separate.
-/
