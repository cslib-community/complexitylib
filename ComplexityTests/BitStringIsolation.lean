/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.BitString.Isolation
import Mathlib.Data.Fin.VecNotation

/-! # Isolation of bit strings in a set

A single string is isolated in every direction, no string of the whole cube is isolated in any
direction, and both extremes meet the isolation inequality with equality.
-/

namespace ComplexityTests.BitStringIsolation

open Cslib.BitString

-- A singleton is isolated in all directions, no string of the whole cube is isolated, and
-- `{00, 11}` has isolation 2 and satisfies the isolation inequality.
example (σ : Fin 2 → Bool) :
    isolation {fun _ : Fin 3 => true} (fun _ => true) = 3 ∧
      isolation Finset.univ σ = 0 ∧
      isolation {![false, false], ![true, true]} ![true, true] = 2 ∧
      2 ^ 2 ≤ ∑ τ ∈ ({![false, false], ![true, true]} : Finset (Fin 2 → Bool)),
        2 ^ isolation {![false, false], ![true, true]} τ :=
  ⟨by decide, by simp [isolation], by decide,
    two_pow_le_sum_two_pow_isolation _ ⟨_, Finset.mem_insert_self _ _⟩⟩

end ComplexityTests.BitStringIsolation
