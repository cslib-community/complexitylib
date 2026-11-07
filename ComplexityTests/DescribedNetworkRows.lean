/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedLift

/-! The row-count API works independently of the algorithm's vertex descriptors.
The edge hypothesis matters: an edgeless network can have a vacuous oversized row prefix. -/

namespace ComplexityTests.DescribedNetworkRows

open Cslib.Circuits.Frontier

private def edge : DescribedNetwork Unit := ⟨1, [([0], ()), ([0], ())]⟩

example : 1 ≤ edge.vertices.length :=
  DescribedNetwork.rows_le_of_isRowsFirstBipartite
    (D := edge) (r := 1) (by decide) (by decide)

example : (⟨0, []⟩ : DescribedNetwork Unit).IsRowsFirstBipartite 7 := by decide
example : ¬7 ≤ (⟨0, []⟩ : DescribedNetwork Unit).vertices.length := by decide

end ComplexityTests.DescribedNetworkRows
