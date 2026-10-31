/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.FastSimulation

/-! # Nondeterministic and probabilistic time in time `2 ^ O(T / √log T)`: checked instances

The class containments at `T n = n + 2`, which is at least `max n 2`. -/

namespace ComplexityTests.FastSimulation

open Cslib.Complexity Cslib.Complexity.CountingSimulation Turing.MultiTapeTM

example : ∀ n, max n 2 ≤ n + 2 := fun n => by omega

example {α : Type} {enc : α ↪ List Bool} (hT : TimeConstructible fun n => n + 2) :
    NTIME enc (fun n => n + 2) ⊆
      ⋃ C, DTIME enc fun n => 2 ^ (C * (n + 2) / Nat.sqrt (Nat.log 2 (n + 2))) :=
  NTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two hT fun n => by omega

end ComplexityTests.FastSimulation
