/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Flat
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Resources
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Width

/-!
# Native sparse queries against actual shared box tables

One fixed 64-register program constructs the shared geometry and signed value table,
then traverses only compatible prefixes leading to leaves through the requested order.
Low-order leaves consume the original signed arrays; threshold leaves consume actual
stored box values. The initialized answer is the existing finite query, and canonical
left/right encodings specialize it to the original bilinear product.

## Main definitions

* `BoxQuery.queryProgram`: reusable native traversal of an already constructed table.
* `BoxQuery.program`: actual input adaptation, shared construction and one sparse query.
* `BoxQuery.timeBound`: shared preparation, sparse query and final halt charged separately.

## Main results

* `BoxQuery.exec_queryProgram`: callable native execution from actual table readback.
* `BoxQuery.runs_wide`: actual initialized prefix and halt with one answer witness and frame.
* `BoxQuery.runs_bilinear`: the same execution computes the original bilinear product.
* `BoxQuery.queryTime_eq_alpha`: sparse query cost in terms of existing alpha counts.
* `BoxQuery.preparationTime_le`: separate shared geometry and beta-controlled tile cost.
* `BoxQuery.prefix_bounded`: original-input word and support bounds at every wider prefix.

## References

The finite partition follows [AlmanWilliams2026, Section 4.2] and the primary formal source
at [anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec4/Theorem30).
This native worklist and shared directory representation are original implementations
of that finite partition, with their own actual instruction costs. Shared preparation
is explicit; global all-tile amortization, wanted-query routing, Corollary 26 and the
full 1.9992 endpoint remain separate objectives.
-/
