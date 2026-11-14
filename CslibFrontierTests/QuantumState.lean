/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.GateMatrix

/-! Shared one-qubit test fixtures, extracted from the quantum protocol clients. -/

public section

namespace CslibFrontierTests.QuantumProtocols

open Cslib.Quantum Matrix Gate

/-- The state `|+⟩ = H|0⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def plus : EuclideanSpace ℂ Bool :=
  unitaryEquiv ⟨hadamardMatrix, hadamardMatrix_mem_unitaryGroup⟩ (ket false)

theorem plus_apply (b : Bool) : plus.ofLp b = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  rw [plus, unitaryEquiv_apply, hadamardMatrix_mulVec]
  cases b <;> simp

theorem norm_plus : ‖plus‖ = 1 := by
  rw [plus, LinearIsometryEquiv.norm_map, norm_ket]

end CslibFrontierTests.QuantumProtocols
