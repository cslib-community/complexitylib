/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Circuit/Counting.lean`)

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Counting

/-!
# Counting functions computed by finite circuits over a complete basis

This module provides the `complexity` characterization of `Cslib.Circuits.computableFunctions`
over a complete gate basis, complementing
`Cslib.Circuits.mem_computableFunctions_iff_ecomplexity_le`.

## Main results

* `Cslib.Circuits.mem_computableFunctions_iff_complexity_le`: over a complete basis, the scalar
  functions computable with at most `s` gates are those of complexity at most `s`.
-/

public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} [Finite σ.Op] {U : Type u}
variable {I : Interpretation σ U} [I.IsComplete] {n s : ℕ}

/-- Over a complete basis, the functions computable with at most `s` gates are those of
complexity at most `s`. -/
theorem mem_computableFunctions_iff_complexity_le {f : (Fin n → U) → U} :
    f ∈ computableFunctions I n s ↔ complexity I (single f) ≤ s := by
  rw [mem_computableFunctions, complexity_le_iff]

end Cslib.Circuits
