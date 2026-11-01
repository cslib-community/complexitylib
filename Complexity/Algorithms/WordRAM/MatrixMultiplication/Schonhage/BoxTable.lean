/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Constructor
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Flat

/-!
# Native shared geometry and compact signed box tables

The existing finite boxes are now computed as a shared native directory and compact
catalogue. Each tile fills one value per actual box from the two canonical signed
leaf arrays, and lookup reads the actual stored signed word for a valid raw cube.
The caller routines permit dirty scratch and preserve the original arrays and outside memory.

## Main definitions

* `BoxTable.geometry`: compute the shared directory and descriptor catalogue once.
* `BoxTable.tile`: reuse that geometry to fill one compact value table.
* `BoxTable.lookup`: read a valid raw cube's actual stored value.
* `BoxTable.program`: complete initialized-input constructor with a fixed 64-register bank.

## Main results

* `BoxTable.runs_wide`: original-input admission, actual initialized prefix and charged halt,
  with the same final witness for the computed ranks, values and frame.
* `BoxTable.exec_lookup`: actual valid-box lookup, within `18*L+32` native instructions.
* `BoxTable.geometryTime_le`: shared geometry within `64*(L+1)^2*10^L` when `m ≤ L`.
* `BoxTable.tileTime_le`: per-tile work bounded using the existing finite box-count law.

## References

The finite boxes and recurrence are adapted from [AlmanWilliams2026, Section 4.2].
The shared directory and compact native representation are original alternatives to the
per-tile trie in the primary formal source at
[anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec4/Theorem30).
Both use the existing tensor terms and signed leaf-product sum, but the memory layout,
digit order and charged costs differ. Shared setup and retained tile storage remain explicit;
no global all-tile amortization, wanted-query program, Corollary 26 or tuned 1.9992 bound
is claimed.
-/
