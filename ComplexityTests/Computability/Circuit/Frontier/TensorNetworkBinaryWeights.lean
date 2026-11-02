/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.BinaryWeights

/-!
# Native weighted contraction regression tests

The large natural table entries exceed a fixed small numeric weight bound, but their binary
lengths fit the polynomial promise. The native certificate computes the exact natural contraction
and its runtime theorem has an actual rows-first instance. The zero-edge case remains correct
even though the asymptotic resource theorem starts at two edges.
-/

public section

namespace ComplexityTests.TensorNetworkBinaryWeights

open Cslib.Circuits.Frontier Turing.MultiTapeTM

def weighted : ExplicitTensorNetwork ℕ :=
  ⟨2, [([0, 1], [2 ^ 32, 0, 3, 5]), ([0, 1], [1, 1, 1, 1])]⟩

example : weighted.IsRowsFirstBipartite 1 := by decide

example : weighted.binaryTableBound ≤ 100 * (weighted.numEdges + 1) ^ 2 := by decide

-- A genuine native machine, with all assumptions of its rate theorem discharged.
example : ∃ K : ℕ,
    (BinaryWeights.certificate 2).time (1, weighted) ≤
        K * ((BinaryWeights.encInput (1, weighted)).length + 1) ^ K *
          2 ^ (K * 2 / Nat.sqrt (Nat.log 2 2)) ∧
      (BinaryWeights.certificate 2).space (1, weighted) ≤
        K * ((BinaryWeights.encInput (1, weighted)).length + 1) ^ K := by
  obtain ⟨K, hK⟩ := BinaryWeights.certificate_bound 2 1 100 2
  exact ⟨K, hK 1 weighted (by decide) (by decide) (by decide) (by decide) (by decide)⟩

example : IsComputable (fun x : ℕ × ExplicitTensorNetwork ℕ => x.2.contraction)
    BinaryWeights.encInput encNat := (BinaryWeights.certificate 2).isComputable

-- Empty networks retain exact correctness without any structural premise.
example : Polynomial.evalCoeffList 2
    ((⟨0, []⟩ : ExplicitTensorNetwork ℕ).truncContraction ExplicitTensorNetwork.binaryEntry
      (ExplicitTensorNetwork.binaryPrecision 1 ⟨0, []⟩)
      (ExplicitTensorNetwork.binaryDegreeBound 1 ⟨0, []⟩ + 1)) = 1 := by
  rw [ExplicitTensorNetwork.evalCoeffList_truncContraction_binaryEntry
    (by simp : ∀ v ∈ ([] : List (List ℕ × List ℕ)), ∀ n ∈ v.2, n.size ≤ 1)]
  simp [ExplicitTensorNetwork.contraction]

end ComplexityTests.TensorNetworkBinaryWeights
