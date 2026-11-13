/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontierTests.QuantumOracleUniformFamily
public import CslibFrontierTests.QuantumInput

/-! A native generator with growing width, varying wire addresses and growing query count.
It queries and unqueries the same oracle, then decodes the supplied imaginary-phase qubit.
The output retains the classical input and distinguishes the two quantum inputs. -/

public section

namespace CslibFrontierTests.QuantumOracleUniform

open Cslib Cslib.Quantum Turing.MultiTapeTM
open CslibFrontierTests.QuantumInput

private theorem decode_toCircuit (n ℓ : ℕ) (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    OracleCircuit.toCircuit (2 * n + 1 + ℓ + 1) H
      [.gate (true, true, 2 * n + 1 + ℓ, []), .gate (false, true, 2 * n + 1 + ℓ, [])] =
    Circuit.mapWires (blockEmb (2 * n + 1 + ℓ) (by omega)) phaseDecode := by
  simp only [OracleCircuit.toCircuit, List.filterMap_cons, OracleGateCode.toPlacedGate?,
    PhaseGateCode.toPlacedGate?, GateCode.toPlacedGate?, Nat.lt_add_one, ↓reduceDIte,
    List.filterMap_nil, phaseDecode, Circuit.mapWires, List.map_cons, List.map_nil,
    PlacedGate.mapWires_ctrlPhase, CslibFrontierTests.QuantumCircuit.h₀]
  simp only [PlacedGate.mapWires]
  congr 3 <;> ext i <;> fin_cases i <;>
    change 2 * n + 1 + ℓ = 0 + (2 * n + 1 + ℓ) <;> omega

/-- For every oracle and every classical word, the growing circuit decodes the supplied phase
and preserves the encoded classical input, including the security parameter. -/
theorem run_phaseFamily (n : ℕ) (x : List Bool) (H : (Fin 1 → Bool) → Fin 1 → Bool) (b : Bool) :
    phaseFamily.run n x H (phaseInput b) =
      ket (inputState (2 * n + 1 + x.length + 1)
        (encPair encUnary encBits (n, x) ++ [b])) := by
  rw [UniformOracleCircuitFamily.run_apply]
  rw [OracleCircuit.toCircuit_append, Circuit.eval_append,
    OracleCircuit.eval_toCircuit_replicate_query_pairs, decode_toCircuit]
  rw [UniformOracleCircuitFamily.initialState_apply]
  rw [Circuit.eval_mapWires_embedState, eval_phaseDecode, embedState_ket,
    glue_blockEmb_inputState _ _ (by simp)]
  rfl

/-- Terminal measurement returns the original encoded word followed by the decoded quantum bit.
The query/unquery sequence cancels for every supplied fixed oracle. -/
theorem output_phaseFamily (n : ℕ) (x : List Bool)
    (H : (Fin 1 → Bool) → Fin 1 → Bool) (b : Bool) :
    phaseFamily.output n x H (phaseInput b) (norm_phaseInput b) =
      PMF.pure (encPair encUnary encBits (n, x) ++ [b]) := by
  rw [UniformOracleCircuitFamily.output_eq]
  trans measureOut (ket (inputState (2 * n + 1 + x.length + 1)
    (encPair encUnary encBits (n, x) ++ [b]))) (norm_ket _) List.ofFn
  · congr 1
    exact run_phaseFamily n x H b
  rw [measureOut_ket]
  congr 1
  rw [ofFn_inputState (by simp [Nat.add_assoc])]
  simp [Nat.add_assoc]

end CslibFrontierTests.QuantumOracleUniform
