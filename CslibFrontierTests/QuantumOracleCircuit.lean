/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Quantum.Oracle.Code
import CslibFrontierTests.QuantumCircuitFixture
import CslibFrontierTests.QuantumOracleFixture

/-! Coherent oracle circuits: explicit basis actions, entanglement, interference and costs. -/

namespace CslibFrontierTests.QuantumOracleCircuit

open Cslib.Quantum CslibFrontierTests.QuantumCircuit

private abbrev identityHash : (Fin 1 → Bool) → Fin 1 → Bool := id

private noncomputable def query : PlacedGate 2 :=
  xorQuery identityHash (Function.Embedding.refl _)

-- A one-bit identity hash is CNOT, on all basis inputs, including a nonzero response.
private theorem query_ket (x : Fin 2 → Bool) :
    query.eval (ket x) = ket ![x 0, x 1 ^^ x 0] := by
  simpa [query, identityHash] using
    CslibFrontierTests.QuantumOracle.xorQuery_oneBit_ket identityHash x

example : query.eval (ket ![true, false]) = ket ![true, true] := by
  simpa using query_ket ![true, false]

example : query.eval (ket ![true, true]) = ket ![true, false] := by
  simpa using query_ket ![true, true]

-- Linearity preserves the relative phase and produces an entangled state.
example : query.eval (((Real.sqrt 2)⁻¹ : ℂ) • (ket ![false, false] - ket ![true, false])) =
    ((Real.sqrt 2)⁻¹ : ℂ) • (ket ![false, false] - ket ![true, true]) := by
  simp [map_smul, map_sub, query_ket]

-- Queries between the two Hadamards cancel before final measurement. A measured query
-- register would instead destroy the interference that makes the final answer certain.
example : Circuit.run [hq₀, query, query, hq₀] ![false, false] = ket ![false, false] := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, query, xorQuery_eval_twice]
  change unitaryEquiv (place w₀ Gate.hadamard)
    (unitaryEquiv (place w₀ Gate.hadamard) (ket ![false, false])) = _
  rw [← unitaryEquiv_mul, ← map_mul, Gate.hadamard_mul_self, map_one, unitaryEquiv_one]

private def program : OracleCircuit :=
  [.gate (false, true, 0, []), .query, .query, .gate (false, true, 0, [])]

example : OracleCircuit.toCircuit 2 identityHash program = [hq₀, query, query, hq₀] := by
  simp only [program, OracleCircuit.toCircuit, List.filterMap_cons,
    OracleGateCode.toPlacedGate?, PhaseGateCode.toPlacedGate?, GateCode.toPlacedGate?,
    show 0 < 2 by decide,
    show 1 + 1 ≤ 2 by decide, ↓reduceDIte, List.filterMap_nil]
  rfl

example : (OracleCircuit.gateCount program, OracleCircuit.queryCount program) = (2, 2) := rfl

example : ∀ g ∈ program, g.WellFormed 1 1 2 := by decide

example : (OracleCircuit.toCircuit 2 identityHash program).length = 4 := by
  exact OracleCircuit.length_toCircuit identityHash program (by decide)

-- Ordinary gate lists embed through the existing phase-code inclusion without changing semantics.
example (codes : List GateCode) :
    OracleCircuit.toCircuit 2 identityHash
      ((codes.map fun g => (false, g)).map OracleGateCode.gate) = Circuit.ofCodes 2 codes := by
  rw [OracleCircuit.toCircuit_map_gate, Circuit.ofPhaseCodes_map]

private def phaseProgram : OracleCircuit := [.gate (true, false, 0, []), .query]

private theorem phaseProgram_toCircuit : OracleCircuit.toCircuit 2 identityHash phaseProgram =
    [PlacedGate.ctrlPhase false w₀, query] := by
  simp only [phaseProgram, OracleCircuit.toCircuit, List.filterMap_cons,
    OracleGateCode.toPlacedGate?, PhaseGateCode.toPlacedGate?, show 0 < 2 by decide,
    show 1 + 1 ≤ 2 by decide, ↓reduceDIte, List.filterMap_nil]
  rfl

-- A phase gate and oracle query produce a complex relative phase on an entangled state.
example : Circuit.eval (OracleCircuit.toCircuit 2 identityHash phaseProgram)
    (((Real.sqrt 2)⁻¹ : ℂ) • (ket ![false, false] + ket ![true, false])) =
      ((Real.sqrt 2)⁻¹ : ℂ) • (ket ![false, false] + Complex.I • ket ![true, true]) := by
  rw [phaseProgram_toCircuit]
  simp [Circuit.eval_cons, Circuit.eval_nil, map_smul, map_add,
    PlacedGate.eval_ctrlPhase_ket, w₀, query_ket]

example : (OracleCircuit.gateCount phaseProgram, OracleCircuit.queryCount phaseProgram) = (1, 1) :=
  rfl

example : ∀ g ∈ phaseProgram, g.WellFormed 1 1 2 := by decide

-- Queries whose input and response do not fit are rejected; ordinary valid gates remain.
example : ¬OracleGateCode.WellFormed 1 1 1 .query := by decide

example : OracleGateCode.toPlacedGate? 1 identityHash .query = none := by
  simp [OracleGateCode.toPlacedGate?]

example : OracleCircuit.toCircuit 1 identityHash [.query, .gate (false, false, 0, [])] =
    Circuit.ofCodes 1 [(false, 0, [])] := by
  simp only [OracleCircuit.toCircuit, List.filterMap_cons, OracleGateCode.toPlacedGate?,
    show ¬1 + 1 ≤ 1 by decide, ↓reduceDIte]
  rfl

-- Empty response registers are valid: the sole possible answer makes the query the identity.
example (ψ : Qubits 1) :
    (xorQuery (b := 0) (fun _ _ => false) (Function.Embedding.refl _)).eval ψ = ψ := by
  ext z
  let A : Fin (1 + 0) ↪ Fin 1 := Function.Embedding.refl _
  obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters A).symm.surjective z
  rw [xorQuery_eval_apply]
  have heq : y + (fun _ : Fin 0 => false) = y := Subsingleton.elim _ _
  rw [heq]

end CslibFrontierTests.QuantumOracleCircuit
