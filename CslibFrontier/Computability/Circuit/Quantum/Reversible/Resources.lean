/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Circuit
public import CslibFrontier.Computability.Circuit.Quantum.EncodingSize
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Resources

/-!
# Concrete costs of reversible Boolean compilation

The existing compiler emits at most three NOT/CNOT/Toffoli gates per Boolean gate and at most
three more to relocate the output. It uses `n + G + 1` qubits and makes no oracle queries.
The encoded-length bound charges the per-instance instruction description, including framing
and unary wire numbers in `encGateCode`. It does not measure implementation bytes.
All bounds apply to the actual compiler, including its default-false malformed-code semantics.

These original bounds concern a generated circuit. They do not bound the static description of
the uniform generator or its running time, and do not certify a sampler or a cryptographic
reduction. Offline compilation time is separate from circuit execution; a reduction that runs a
compiler during its attack must account for that computation. The compiler's existing
polynomial-time certificate is preserved in `Reversible.Circuit`.

## Main results

* `Cslib.Quantum.Reversible.length_circuitCodes`: exact output-relocation overhead.
* `Cslib.Quantum.Reversible.length_circuitCodes_le`: at most `3 * G + 3` gates.
* `Cslib.Quantum.Reversible.length_encoding_circuitCodes_le`: encoded instruction length.
* `Cslib.Quantum.Reversible.within_circuitCodes`: separate qubit, gate and zero-query budgets.
-/

public section

namespace Cslib.Quantum.Reversible

open Circuits Circuits.Boolean GateCode Turing.MultiTapeTM

/-- Every De Morgan gate produces at most three elementary reversible gates. -/
theorem length_gateCodes_le (z t : ℕ) (g : Op × List ℕ) : (gateCodes z t g).length ≤ 3 := by
  obtain ⟨op, args⟩ := g
  cases op with
  | const b => cases b <;> simp [gateCodes]
  | not => simp [gateCodes]
  | and => simp only [gateCodes]; split_ifs <;> simp
  | or => simp only [gateCodes]; split_ifs <;> simp

/-- Gate-list compilation costs at most three elementary gates per source gate. -/
theorem length_codes_le (n z : ℕ) (gates : List (Op × List ℕ)) :
    (codes n z gates).length ≤ 3 * gates.length := by
  induction gates using List.reverseRecOn with
  | nil => simp [codes]
  | append_singleton gates g ih =>
    have hg := length_gateCodes_le z (n + gates.length) g
    rw [codes_append_singleton, List.length_append, List.length_append, List.length_singleton]
    omega

/-- Output relocation costs zero gates when its wire is already zero, and three otherwise. -/
theorem length_circuitCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (circuitCodes n code).length = (codes n (n + code.1.length) code.1).length +
      if outQubit (n + code.1.length) (code.2.getD 0 0) = 0 then 0 else 3 := by
  simp only [circuitCodes, List.length_append]
  split_ifs <;> simp [swapCodes]

/-- The whole compiled circuit uses at most three gates per source gate and three for relocation. -/
theorem length_circuitCodes_le (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (circuitCodes n code).length ≤ 3 * code.1.length + 3 := by
  have h := length_codes_le n (n + code.1.length) code.1
  rw [length_circuitCodes]
  split_ifs <;> omega

/-- Unary wire indices and framing contribute at most `12 * (n + G + 1) + 1` bits per gate. -/
theorem length_encoding_circuitCodes_le (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (encList encGateCode (circuitCodes n code)).length ≤
      (3 * code.1.length + 3) * (12 * (n + code.1.length + 1) + 1) :=
  (length_encGateCodes_le fun g hg => (isClassical_circuitCodes n code g hg).2).trans
    (Nat.mul_le_mul_right _ (length_circuitCodes_le n code))

/-- Reading the compiled elementary gates as oracle instructions introduces no coherent queries. -/
theorem within_circuitCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    OracleCircuit.Within ((circuitCodes n code).map fun g => OracleGateCode.gate (false, g))
      (n + code.1.length + 1) ⟨n + code.1.length + 1, 3 * code.1.length + 3, 0⟩ := by
  simp [OracleCircuit.Within, OracleCircuit.gateCount, OracleCircuit.queryCount,
    OracleGateCode.isQuery, List.countP_map, Function.comp_def, length_circuitCodes_le]

end Cslib.Quantum.Reversible
