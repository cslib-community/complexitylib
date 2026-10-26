/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.Search

/-! Measurement of finite-dimensional states: basis states, and the query model's register
probability as an instance. -/

namespace ComplexityTests.QuantumMeasurement

open Cslib.Quantum

-- Measuring a basis state of a qutrit gives that outcome with certainty.
example : measure (ket (1 : Fin 3)) (norm_ket _) 1 = 1 := by simp

example : measure (ket (1 : Fin 3)) (norm_ket _) 2 = 0 := by simp

-- `|0⟩ + |1⟩` has squared norm `2`, so its outcome probabilities sum to `2`, not `1`: `measure`
-- needs a unit state, while `measureProb` is defined for every vector.
example : measureProb (ket (0 : Fin 2) + ket 1) Finset.univ = 2 := by
  simp [measureProb, Fin.sum_univ_two]
  norm_num

-- In the query model, the basis state `|z, 1, ·⟩` has query index `z` with certainty, and the
-- register probability is the measurement probability of the outcomes with query index `z`.
example (z : Fin 4) : regProb (ket (z, true, ()) : State 4 Unit) z = 1 := by
  simp [regProb_eq_sum, Fintype.sum_prod_type]

example (ψ : State 4 Unit) (i : Fin 4) :
    regProb ψ i = measureProb ψ (Finset.univ.filter fun p => p.1 = i) :=
  rfl

end ComplexityTests.QuantumMeasurement
