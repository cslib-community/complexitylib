/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Computability.Complexity.Classes.LogSpace.Randomized
import Complexity.Computability.Complexity.Classes.LogSpace.USTCON

/-!
# Tests for randomized logarithmic space
-/

namespace ComplexityTests.RandomizedLogSpace

open Cslib.Complexity

-- Undirected connectivity, in `L` by Reingold, is in `RL` and in `BPL`.
example : USTCON ∈ RL encUSTCON := L_subset_RL USTCON_mem_L

example : USTCON ∈ BPL encUSTCON := L_subset_BPL USTCON_mem_L

-- Going through `RL` recovers `USTCON ∈ NL`.
example : USTCON ∈ NL encUSTCON := RL_subset_NL (L_subset_RL USTCON_mem_L)

end ComplexityTests.RandomizedLogSpace
