/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.Karger.Memory.Layout

/-!
# Karger's contraction structure over memory on a triangle

The unit-weight triangle is laid out at address `0` with capacity `3`: size `3`, total `6`,
degrees `2, 2, 2`, then the matrix row by row. The tests check that this memory state satisfies
the invariant, and evaluate the sampling query on it against `sampledPair`.
-/

@[expose] public section

namespace ComplexityTests.KargerMemory

open scoped ENNReal
open Cslib Cslib.WeightedCut Cslib.DataStructure Cslib.Algorithms.Lean.Karger
  Cslib.Algorithms.Lean.Karger.Memory

/-- The triangle with unit weights. -/
def triangle : Fin 3 → Fin 3 → ℕ := fun i j => if i = j then 0 else 1

theorem isMultigraph_triangle : IsMultigraph triangle := ⟨by decide, by decide⟩

/-- The layout at address `0` for at most three supervertices. -/
def L : Layout := ⟨0, 3⟩

/-- The triangle in memory: size, total, degrees, then the matrix. -/
def triangleMem : DataStructure.Memory.State :=
  ⟨fun a => [3, 6, 2, 2, 2, 0, 1, 1, 1, 0, 1, 1, 1, 0].getD a 0, 14⟩

/-- The memory state holds the triangle and satisfies the invariant at word size `8`. -/
theorem triangleMem_holds : abs L triangleMem = ⟨3, triangle⟩ ∧ Inv L 8 triangleMem :=
  abs_eq_and_inv isMultigraph_triangle (by decide) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide) (by decide)

/-- The scans find the pair at offset `3`: row `1`, then column `2`, as `sampledPair` does. -/
example : (DataStructure.Memory.spec 8).clientResult triangleMem (pairAt L 3) = (1, 2) ∧
    sampledPair triangle 3 = (1, 2) :=
  ⟨by decide, sampledPair_eq (u := 1) (v := 2) (by decide)⟩

/-- The sampling query at every offset below the total answers `sampledPair` within
`2 · 3 + 1` memory units. -/
example (r : ℕ) (hr : r < 6) :
    (DataStructure.Memory.spec 8).wp DataStructure.Memory.charge (pairAt L r)
      (fun a s t => a = sampledPair triangle r ∧ s = triangleMem ∧ t ≤ 7) triangleMem := by
  have h := wp_pairAt triangleMem_holds.2 (r := r) (by rw [triangleMem_holds.1]; decide +revert)
  rw [triangleMem_holds.1] at h
  exact h

end ComplexityTests.KargerMemory
