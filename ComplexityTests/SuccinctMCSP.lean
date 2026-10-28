/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.SuccinctNP

/-!
# Tests: Succinct MCSP and NP Membership

Tests for `SuccinctMCSP`, the sparse sample-set complexity bound, certificate gate budget,
canonical sample enumeration, and `NP` membership under unary and binary thresholds.
-/

namespace ComplexityTests.SuccinctMCSP

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Concrete instances and verifier checks -/

/-- The 1-input negation sample set `{(![false], true), (![true], false)}`. -/
def notSamples : Finset (BitString 1 × Bool) :=
  {(![false], true), (![true], false)}

/-- `sampleFunction notSamples` evaluates to `true` on `![false]` and `false` on `![true]`. -/
example :
    SuccinctMCSP.sampleFunction notSamples ![false] = true ∧
      SuccinctMCSP.sampleFunction notSamples ![true] = false := by
  decide

/-- The sparse synthesis bound `complexity_sampleFunction_le` bounds `sampleFunction notSamples`
by `2 * (2 * 1 + 3) + 1 = 11` gates. -/
example : complexity interpretation (single (SuccinctMCSP.sampleFunction notSamples)) ≤ 11 := by
  have hcard : notSamples.card = 2 := by decide
  simpa [hcard] using SuccinctMCSP.complexity_sampleFunction_le notSamples

/-- Canonical sample enumeration `rawSamples` orders `notSamples` by input bitstring (`[false]` then
`[true]`). -/
example :
    SuccinctMCSP.rawSamples ⟨1, notSamples, 1⟩ = [([false], true), ([true], false)] := by
  decide

/-- An instance with empty samples on `1` input is a yes-instance at threshold `0`. -/
example : (⟨1, ∅, 0⟩ : SuccinctMCSP.Instance) ∈ SuccinctMCSP :=
  ⟨⟨.empty, fun _ => Wire.input 0⟩, le_rfl, fun _ h => by simp at h⟩

/-- A single sample `((![false]), false)` on `1` input is computed by a 0-gate wire circuit. -/
example : (⟨1, {(![false], false)}, 0⟩ : SuccinctMCSP.Instance) ∈ SuccinctMCSP := by
  refine ⟨⟨.empty, fun _ => Wire.input 0⟩, le_rfl, ?_⟩
  intro p hp
  rw [Finset.mem_singleton] at hp
  subst hp
  rfl

/-- Contradictory samples at the same input `![false]` form a no-instance at any threshold `s`. -/
example (s : ℕ) :
    (⟨1, {(![false], true), (![false], false)}, s⟩ : SuccinctMCSP.Instance) ∉ SuccinctMCSP :=
  SuccinctMCSP.notMem_of_mem_samples (y := ![false]) (by simp) (by simp)

-- The verifier accepts the 1-gate NOT certificate on `notSamples` at threshold 1.
example : SuccinctMCSP.verifier
    (⟨1, notSamples, 1⟩, certificate 1 1 [(.not, [0])] 1) = true := by
  decide

-- The verifier rejects a malformed certificate where gate 0 reads wire 1 (itself).
example : SuccinctMCSP.verifier
    (⟨1, notSamples, 1⟩, certificate 1 1 [(.not, [1])] 1) = false := by
  decide

-- The verifier rejects the 0-gate identity wire certificate on `notSamples` at threshold 0.
example : SuccinctMCSP.verifier
    (⟨1, notSamples, 0⟩, certificate 1 0 [] 0) = false := by
  decide

/-- The 1-input negation samples are a yes-instance at threshold `1`. -/
example : (⟨1, notSamples, 1⟩ : SuccinctMCSP.Instance) ∈ SuccinctMCSP :=
  SuccinctMCSP.mem_of_verifier_eq_true (w := certificate 1 1 [(.not, [0])] 1) (by decide)

/-- The 1-input negation samples are a no-instance at threshold `0`: any 0-gate certificate has
length `certLength 1 0 = 1` and is rejected by `SuccinctMCSP.verifier`. -/
example : (⟨1, notSamples, 0⟩ : SuccinctMCSP.Instance) ∉ SuccinctMCSP := by
  intro hx
  obtain ⟨_ | ⟨b, _ | _⟩, hu, hV⟩ := SuccinctMCSP.exists_verifier_append hx
  · revert hu; decide
  · have := hV []; revert this; cases b <;> decide
  · simp [certLength, MCSP.sampleBudget] at hu

end ComplexityTests.SuccinctMCSP
