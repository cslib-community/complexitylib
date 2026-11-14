/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.EncodingSize
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Resources
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling
import CslibFrontier.Computability.Circuit.Quantum.Reversible.Resources

/-!
# Concrete costs of reversible Boolean samplers

The exact sampler construction uses `n` Hadamard gates to prepare `n` fair seed bits, at most
three reversible gates per Boolean gate, and one CNOT per copied output. Its active register keeps
all `n` seeds and `G` Boolean gate values, one compiler zero qubit, and `m` copied outputs. The
description has no coherent oracle query and `samplerDist` performs one final measurement.

The encoded-length bound charges the generated instruction list, including its unary wire numbers
and framing. It does not bound the static generator program or its offline running time. Those are
separate from the online gate and qubit costs recorded here.

## Main results

* `Cslib.Quantum.Reversible.samplerWidth_circuit`: exact active width for a typed circuit.
* `Cslib.Quantum.Reversible.length_samplerCodes_le`: at most `n + 3 * G + m` gates.
* `Cslib.Quantum.Reversible.length_encoding_samplerCodes_le`: encoded instruction length.
* `Cslib.Quantum.Reversible.within_samplerCodes`: separate qubit, gate, and zero-query budgets.
-/

public section

namespace Cslib.Quantum.Reversible

open Circuits Circuits.Boolean GateCode Turing.MultiTapeTM

/-- A typed circuit sampler retains every input and gate value, one fixed-zero qubit, and one
fresh qubit for every output. -/
theorem samplerWidth_circuit {n m : ℕ} (C : Circuit signature n m) :
    samplerWidth n C.code = n + C.size + 1 + m := by
  simp [samplerWidth, samplerOutputStart, samplerZero, Circuit.code]

/-- The complete sampler uses at most one Hadamard per seed, three reversible gates per Boolean
gate, and one CNOT per copied output. -/
theorem length_samplerCodes_le (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (samplerCodes n code).length ≤ n + 3 * code.1.length + code.2.length := by
  have h := length_codes_le n (samplerZero n code) code.1
  rw [length_samplerCodes]
  omega

/-- The generated sampler's encoded instruction list, including framing and unary wire indices,
has the stated construction-derived bound. -/
theorem length_encoding_samplerCodes_le (n : ℕ)
    (code : List (Op × List ℕ) × List ℕ) :
    (encList encGateCode (samplerCodes n code)).length ≤
      (n + 3 * code.1.length + code.2.length) * (12 * samplerWidth n code + 1) :=
  (length_encGateCodes_le (wellFormed_samplerCodes n code)).trans
    (Nat.mul_le_mul_right _ (length_samplerCodes_le n code))

/-- Reading the sampler's elementary gates as oracle instructions uses the exact active width,
the construction-derived gate budget, and no coherent oracle queries. -/
theorem within_samplerCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    OracleCircuit.Within ((samplerCodes n code).map fun g => OracleGateCode.gate (false, g))
      (samplerWidth n code)
      ⟨samplerWidth n code, n + 3 * code.1.length + code.2.length, 0⟩ := by
  simp [OracleCircuit.Within, OracleCircuit.gateCount, OracleCircuit.queryCount,
    OracleGateCode.isQuery, List.countP_map, Function.comp_def, length_samplerCodes_le]

end Cslib.Quantum.Reversible
