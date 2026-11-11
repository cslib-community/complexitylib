/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.MassProduction.Basic
import CslibFrontier.Computability.Circuit.Boolean.ShannonSynthesis

/-!
# Replicated Shannon synthesis

Independently replicate the finite Shannon construction to bound the mass complexity of
any finite batch. The bound grows linearly with the number of copies; later mass-production
constructions improve this dependence by sharing work between copies.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.massComplexity_le_shannon`: the finite replication bound.

## References

* Adapted from MassProduction/ShannonSynthesis.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

public section

namespace Cslib.Circuits.Boolean.MassProduction

/-- Independent Shannon synthesis bounds every finite batch, including zero copies.
The natural division occurs inside the per-copy budget, after multiplication by 27. -/
theorem massComplexity_le_shannon {n : ℕ} (hn : 16 ≤ n) (f : BooleanFunction n) (k : ℕ) :
    massComplexity f k ≤ (k * (27 * 2 ^ n / n) : ℕ) := by
  apply massComplexity_le_iff.mpr
  refine ⟨(ShannonSynthesis.synthesize f).replicateScalar k,
    (ShannonSynthesis.computes_synthesize f).replicateScalar k, ?_⟩
  apply (Program.cost_nonconstantCost_le _).trans
  simpa only [Circuit.size_replicateScalar] using
    Nat.mul_le_mul_left k (ShannonSynthesis.size_synthesize_le hn f)

end Cslib.Circuits.Boolean.MassProduction
