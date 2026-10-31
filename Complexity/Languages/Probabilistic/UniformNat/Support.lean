/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.UniformNat

/-!
# Supported residues of bounded samplers

The positive-modulus support bound for `sampleModNat` lets callers recover a canonical residue
from a supported sampled natural. It is kept separate from the sampler's definition and exact law.

## Main results

* `Cslib.ProbComp.lt_of_mem_support_sampleModNat`: every sampled residue is below a positive
  modulus.
-/

public section

namespace Cslib.ProbComp

open Probability

/-- Every supported residue is strictly below a positive modulus. -/
theorem lt_of_mem_support_sampleModNat {width modulus value : ℕ} (hmodulus : 0 < modulus)
    (hvalue : value ∈ (ProbComp.eval (sampleModNat width modulus)).support) :
    value < modulus := by
  rw [eval_sampleModNat, PMF.mem_support_map_iff] at hvalue
  obtain ⟨i, _, rfl⟩ := hvalue
  exact Nat.mod_lt _ hmodulus

end Cslib.ProbComp
