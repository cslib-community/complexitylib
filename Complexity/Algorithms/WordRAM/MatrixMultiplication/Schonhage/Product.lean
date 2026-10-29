/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.ThinWidth

/-!
# Native queried thin-matrix products

## Main definitions

* `QueriedProduct.program`: fixed standard unsigned WordRAM code with 160 registers.
* `QueriedProduct.input`: original scalar headers, both row-major matrices and raw query pairs.

## Main results

* `QueriedProduct.exec`: complete execution from original words, with arbitrary header zero
  and outside memory, exact `Matrix.mul` answers and input restoration.
* `QueriedProduct.runs_wide`: initialized flat runs, guaranteed input fit and a charged halt.
* `QueriedProduct.runs_thin`: the same native execution at `L=19m`, `D=4^m`, `D^18≤N`,
  with instruction bound `4325376*(19m+1)*N²/D^(1/18)` when `Q*2^m≤N²`, and sufficient
  physical width `128*clog₂(N+Q+A+2)` for entry bound `A`.
* `QueriedProduct.thin_timeBound`: distinct-set sparsity gives a saving with an additive
  charge for every query occurrence, without imposing the stronger occurrence-count premise.

The program computes its own valid-subset tables, shared band encodings, tile keys, query
codes, counts, prefix offsets, stable scatter, tile pointers, pruned traversals, epochs and
answer reconstruction. Original query order and duplicates are retained. Signed mode uses
canonical `Signed.encode` input words. Raw mode requires nonnegative entries and actually
doubles each word before calling the signed producer; this includes raw unsigned 0/1 inputs.
One timestamp directory is initialized and reused across all tiles.

The component reuses the finite Section 2 tensor/pruning and thin-product mathematics from
[AlmanWilliams2026], with original programs and execution proofs against native WordRAM APIs.
It does not import the source Light machine or assume a solver, execution or cost contract.
Stage `exec_*` lemmas are internal implementation APIs shared between proof modules. Callers
use the results above; the initialized input contains no computed layout or query certificate.
This is a queried-product component, not a complete Exact Triangle or ordinary-3SUM algorithm.
The full endpoint and improved Section 4 route to exponent 1.9992 remain under #1394.

## References

* [AlmanWilliams2026], Section 2: finite tensor encodings and sparse queried products.
-/
