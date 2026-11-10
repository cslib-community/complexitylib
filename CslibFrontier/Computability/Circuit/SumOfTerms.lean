/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SumOfTerms.Basic
public import Mathlib.LinearAlgebra.Dimension.LinearMap
import CslibFrontier.Foundations.LinearAlgebra.Rank
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Computability.Circuit.Simulation

/-!
# Rank bounds for sums of dictionary terms

A linear feature whose dictionary values have bounded rank gives a lower bound on the total
weighted dictionary cost. Each shared gate is charged once. Supplied inputs are permitted when
their features vanish. The signature and its costs are re-exported from `SumOfTerms.Basic`.

## Main results

* `Cslib.Circuits.SumOfTerms.rank_trace_le`: every wire's feature rank is bounded by program cost.

## References

* Adapted from LowerBound/Fusion/SumOfTerms/Rank.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

public section

namespace Cslib.Circuits.SumOfTerms

variable {T K V A B : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] {n g : ℕ}

/-- A rank budget for each dictionary term bounds every wire's feature rank. The span argument
counts shared gates once, even when additions reuse them. -/
theorem rank_trace_le (p : Program (signature T) n g) (value : T → V)
    (feature : V →ₗ[K] A →ₗ[K] B) (weight : T → ℕ)
    (hterm : ∀ t, (feature (value t)).rank ≤ weight t)
    (input : Fin n → V) (hinput : ∀ i, feature (input i) = 0) (w : Wire n g) :
    (feature (p.trace (interpretation value) input w)).rank ≤ p.cost (dictionaryCost weight) := by
  let contribution : Op T → A →ₗ[K] B
    | .add => 0
    | .term t => feature (value t)
  let family := fun k => contribution (p.lines k).op
  let S := Submodule.span K (Set.range family)
  have step (op : Op T) (args : Fin op.arity → V)
      (hargs : ∀ a, feature (args a) ∈ S) (hnew : contribution op ∈ S) :
      feature (interpretation value op args) ∈ S := by
    cases op with
    | add => simpa [interpretation] using S.add_mem (hargs 0) (hargs 1)
    | term t => exact hnew
  have hmem : ∀ w, feature (p.trace (interpretation value) input w) ∈ S := by
    refine p.trace_induction (interpretation value) input (P := fun v => feature v ∈ S)
      (fun i => ?_) (fun k ih => ?_)
    · simp [hinput]
    · exact step _ _ ih (Submodule.subset_span ⟨k, rfl⟩)
  have h := LinearMap.rank_le_sum_of_mem_span _ family
    (fun k => dictionaryCost weight (p.lines k).op) (hmem w) (fun k => ?_)
  · simpa only [← Nat.cast_sum, ← p.cost_eq_sum] using h
  · cases hop : (p.lines k).op with
    | add => simp [family, contribution, hop, dictionaryCost]
    | term t => simpa [family, contribution, hop, dictionaryCost] using hterm t

end Cslib.Circuits.SumOfTerms
