/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.AndreevThresholdAbstract

/-! # Concrete clients and non-vacuity checks for the Andreev threshold-circuit abstract

Verifies that the public definitions of `AndreevThresholdAbstract` match the library's
(`WeightedThreshold.interpretation`, `Circuit.wireCount`, `Boolean.andreev`,
`WeightedThreshold.andreevSimultaneousTail`), and checks that the exact and average-case
upper-bound and lower-bound headline theorems instantiate at concrete small parameters
(`b = 2, m = 2`, `n = 8`).
-/

namespace ComplexityTests.Abstracts.AndreevThresholdTests

open ComplexityAbstracts.AndreevThresholdAbstract
open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.WeightedThreshold

example {n : ℕ} (c : ThrCircuit n) (x : Fin n → Bool) :
    evaluate c x = c.eval interpretation x 0 :=
  rfl

example {n : ℕ} (c : ThrCircuit n) :
    ComplexityAbstracts.AndreevThresholdAbstract.wireCount c = c.wireCount :=
  rfl

example (b m : ℕ) :
    ComplexityAbstracts.AndreevThresholdAbstract.andreev b m =
      Cslib.Circuits.Boolean.andreev b m :=
  rfl

example (b : ℕ) (α : ℝ) :
    ComplexityAbstracts.AndreevThresholdAbstract.andreevSimultaneousTail b α =
      Cslib.Circuits.Boolean.WeightedThreshold.andreevSimultaneousTail b α :=
  rfl

/-- At `b = 2, m = 2` (`n = 8` bits), `exact_upper_bound` gives a depth-two weighted threshold
circuit of `81` gates (`80` bottom gates and `1` top gate) and at most `720` active wires computing
`andreev 2 2` on all `256` inputs, and for any `α ≥ 1` with `andreevSimultaneousTail 2 α ≤ 1 / 2`
it satisfies both `exact_gate_lower_bound` and `exact_wire_lower_bound`. -/
example {α : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ 2) / 2 ≤ α)
    (htail : ComplexityAbstracts.AndreevThresholdAbstract.andreevSimultaneousTail 2 α ≤ 1 / 2) :
    ∃ c : ThrCircuit 8,
      c.depth ≤ 2 ∧
      c.size = 81 ∧
      ComplexityAbstracts.AndreevThresholdAbstract.wireCount c ≤ 720 ∧
      (∀ x, evaluate c x = ComplexityAbstracts.AndreevThresholdAbstract.andreev 2 2 x) ∧
      (2 : ℝ) * (((2 : ℝ) ^ 2 * (1 / 2 -
        ComplexityAbstracts.AndreevThresholdAbstract.andreevSimultaneousTail 2 α)) ^ 2 - α ^ 2) ≤
        4 * α ^ 2 * (c.size : ℝ) * Real.sqrt ((2 ^ 2 + 2 * 2 : ℕ) : ℝ) ∧
      ((2 : ℝ) ^ 2 * (1 / 2 -
        ComplexityAbstracts.AndreevThresholdAbstract.andreevSimultaneousTail 2 α)) ^ 2 - α ^ 2 ≤
        4 * α ^ 2 * (ComplexityAbstracts.AndreevThresholdAbstract.wireCount c : ℝ) *
          (1 / (2 : ℝ)) * Real.sqrt (1 / (2 : ℝ)) := by
  obtain ⟨c, hd, hs, hw, hcomp⟩ := exact_upper_bound 2 2
  exact ⟨c, hd, hs, hw, hcomp,
    exact_gate_lower_bound (by decide) hα htail c hd hcomp,
    exact_wire_lower_bound (by decide) hα htail c hd hcomp⟩

end ComplexityTests.Abstracts.AndreevThresholdTests
