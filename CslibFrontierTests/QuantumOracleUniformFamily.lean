/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! A native generator and resource clients checked through the public module interface. -/

public section

namespace CslibFrontierTests.QuantumOracleUniform

open Cslib Cslib.Quantum Turing.MultiTapeTM

/-- The last qubit carries the quantum input; the preceding qubits hold `(n, x)`. -/
abbrev phaseDescription (n ℓ : ℕ) : OracleCircuitDescription where
  width := 2 * n + 1 + ℓ + 1
  queryWidth := 1
  responseWidth := 1
  quantumInputWidth := 1
  outputWidth := 2 * n + 1 + ℓ + 1
  instructions := List.replicate (2 * (n + ℓ)) .query ++
    [.gate (true, true, 2 * n + 1 + ℓ, []), .gate (false, true, 2 * n + 1 + ℓ, [])]

private theorem polyTime_phaseDescription : ComputableInPolyTime
    (fun s : OracleInputSize => phaseDescription s.securityParameter s.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription := by
  dsimp only [phaseDescription]
  fun_prop

private theorem wellFormed_phaseDescription (n ℓ : ℕ) :
    (phaseDescription n ℓ).WellFormed ⟨n, ℓ⟩ := by
  refine ⟨le_rfl, by dsimp only [phaseDescription]; omega, le_rfl, ?_⟩
  intro g hg
  simp only [List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with ⟨_, rfl⟩ | rfl | rfl
  · change 1 + 1 ≤ 2 * n + 1 + ℓ + 1
    omega
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed]
  · simp [OracleGateCode.WellFormed, PhaseGateCode.WellFormed, GateCode.WellFormed]

/-- This is one native algorithm for every parameter and input length. -/
abbrev phaseFamily : UniformOracleCircuitFamily :=
  ⟨phaseDescription, by exact polyTime_phaseDescription, by exact wellFormed_phaseDescription⟩

example (n ℓ : ℕ) : (phaseFamily.description n ℓ).width = 2 * n + 1 + ℓ + 1 := rfl

example (n ℓ : ℕ) : (phaseFamily.description n ℓ).instructions.gateCount = 2 := by
  simp [OracleCircuit.gateCount, OracleGateCode.isQuery]

example (n ℓ : ℕ) : (phaseFamily.description n ℓ).instructions.queryCount = 2 * (n + ℓ) := by
  simp [OracleCircuit.queryCount, List.countP_replicate,
    OracleGateCode.isQuery]

-- The public output law retains its explicit length for arbitrary supplied unit states.
example (n : ℕ) (x : List Bool) (H : (Fin 1 → Bool) → Fin 1 → Bool)
    (ψ : Qubits 1) (hψ : ‖ψ‖ = 1) {out : List Bool}
    (hout : out ∈ (phaseFamily.output n x H ψ hψ).support) :
    out.length = 2 * n + 1 + x.length + 1 :=
  phaseFamily.length_of_mem_support_output n x H ψ hψ hout

end CslibFrontierTests.QuantumOracleUniform
