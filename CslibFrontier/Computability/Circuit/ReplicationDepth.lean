/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Replication.lean`)

public import CslibFrontier.Computability.Circuit.Replication

/-!
# The depth of replicated circuits

`Circuit.replicateScalar c k` runs `k` copies of the single-output circuit `c` side by side, one
on each block of the input. The copies share no gates, so the depth does not grow.

This is kept apart from the replication API so that adding it does not rebuild that module's
importers.

## Main results

* `Cslib.Circuits.Circuit.depth_replicateScalar_le`: `k` copies are at most as deep as one.
-/

public section

namespace Cslib.Circuits.Circuit

variable {σ : Signature} {n : ℕ}

/-- **Copies side by side are no deeper than one copy.** -/
theorem depth_replicateScalar_le (c : Circuit σ n 1) (k : ℕ) :
    (c.replicateScalar k).depth ≤ c.depth :=
  depth_pi_le _ fun _ => (depth_comp_le _ _).trans (by rw [depth_wiring, add_zero])

end Cslib.Circuits.Circuit
