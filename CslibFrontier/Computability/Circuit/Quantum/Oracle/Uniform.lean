/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Resources
public import CslibFrontier.Computability.Circuit.Quantum.Input
public import CslibFrontier.Foundations.Quantum.Measurement.Readout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Native uniform quantum oracle circuits with explicit inputs

`encOracleGateCode` uses the existing option encoding: a query is the empty word, and an
elementary instruction is `true` followed by its phase-gate encoding. The latter retains the
phase flag, Hadamard/inverse flag, unary target and list of unary controls. Lists of instructions
use the usual framed list encoding, so even a query contributes to the encoded program length.

A native polynomial-time generator receives the unary security parameter and classical input
length separately. It returns every register size and instruction. Its encoded output length
therefore bounds active qubits and instruction count; restricting auxiliary lengths by any
polynomial bound yields a computable polynomial resource schedule. No resource bound is assumed
as a field of the family.

Execution places a supplied quantum state after the encoded classical input, initializes the
other wires to zero, and uses one fixed coherent oracle throughout. Terminal measurement returns
the declared output prefix. Supplied states need not be efficiently preparable. `Oracle.Density`
extends this execution to mixed states and inaccessible entangled references. Interactive classical
oracles, consistent random-oracle sampling across widths, and a gate-approximation theorem are
separate obligations.
The definitions and results are original infrastructure, not a QROM security claim.

## Main definitions

* `Cslib.Quantum.encOracleGateCode`: a finite binary encoding of oracle instructions.
* `Cslib.Quantum.OracleCircuitDescription`: all register sizes and instructions.
* `Cslib.Quantum.UniformOracleCircuitFamily`: a native generator of valid descriptions.
* `Cslib.Quantum.UniformOracleCircuitFamily.run`, `.output`: isometric execution and measurement.

## Main results

* `Cslib.Quantum.UniformOracleCircuitFamily.exists_resource_bound`: generation bounds resources.
* `Cslib.Quantum.UniformOracleCircuitFamily.exists_computable_resource_bound`: a computable
  polynomial schedule bounds every allowed auxiliary length.
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- A query is encoded as the empty word; a gate is `true` followed by its phase-gate code,
including unary target/control indices. Instruction lists use `encList encOracleGateCode`. -/
@[expose] def encOracleGateCode : OracleGateCode ↪ List Bool :=
  encOfEquiv
    { toFun := fun g => match g with
        | .gate code => some code
        | .query => none
      invFun := fun g => match g with
        | some code => .gate code
        | none => .query
      left_inv := fun g => by cases g <;> rfl
      right_inv := fun g => by cases g <;> rfl }
    (encOption encPhaseGateCode)

@[simp] theorem encOracleGateCode_query : encOracleGateCode .query = [] := rfl

@[simp] theorem encOracleGateCode_gate (g : PhaseGateCode) :
    encOracleGateCode (.gate g) = true :: encPhaseGateCode g := rfl

/-- Construct an elementary oracle instruction from a natively computed phase-gate code. -/
@[fun_prop] theorem OracleGateCode.computableInPolyTime_gate {α : Type}
    {enc : α ↪ List Bool} {g : α → PhaseGateCode}
    (hg : ComputableInPolyTime g enc encPhaseGateCode) :
    ComputableInPolyTime (fun x => OracleGateCode.gate (g x)) enc encOracleGateCode :=
  ((ComputableInPolyTime.optionSome encPhaseGateCode).comp hg).of_enc_eq fun _ => rfl

/-- Inputs to the uniform circuit generator. The security parameter and classical input length
are separate: distinct pairs with the same sum may generate different circuits. -/
structure OracleInputSize where
  /-- The security parameter, supplied in unary to the generator. -/
  securityParameter : ℕ
  /-- Length of the classical auxiliary input, also supplied in unary. -/
  classicalInputLength : ℕ

/-- Generator input encoding: the framed unary security parameter followed by the unary
classical input length. -/
enc_structure encOracleInputSize : OracleInputSize where
  securityParameter : encUnary, classicalInputLength : encUnary

/-- A finite oracle-circuit description, including the input, output and query register sizes.
The quantum input follows the encoded classical input; output and query registers are prefixes. -/
structure OracleCircuitDescription where
  /-- Total number of active qubits. -/
  width : ℕ
  /-- Number of qubits in the oracle argument. -/
  queryWidth : ℕ
  /-- Number of qubits in the XOR response accumulator. -/
  responseWidth : ℕ
  /-- Number of supplied quantum input qubits. -/
  quantumInputWidth : ℕ
  /-- Number of prefix qubits returned by terminal measurement. -/
  outputWidth : ℕ
  /-- Elementary gates and oracle calls, in execution order. -/
  instructions : OracleCircuit

/-- Description encoding: width, query width, response width, quantum-input width and output
width, each in framed unary, followed by the framed list encoding of the instructions. -/
enc_structure encOracleCircuitDescription : OracleCircuitDescription where
  width : encUnary, queryWidth : encUnary, responseWidth : encUnary,
  quantumInputWidth : encUnary, outputWidth : encUnary,
  instructions : (encList encOracleGateCode)

namespace OracleCircuitDescription

/-- The encoded description pays for all active qubits and every instruction, including a
query whose own code is empty. -/
theorem width_add_length_le_encoding_length (D : OracleCircuitDescription) :
    D.width + D.instructions.length ≤ (encOracleCircuitDescription D).length := by
  have h := length_le_length_encList encOracleGateCode D.instructions
  simp only [encOracleCircuitDescription_apply, encOracleCircuitDescriptionFields,
    length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- All declared registers fit and every instruction is valid. The classical input is
`encPair encUnary encBits (n, x)`, of length `2 * n + 1 + x.length`. -/
structure WellFormed (D : OracleCircuitDescription) (s : OracleInputSize) : Prop where
  /-- The encoded classical input and supplied quantum input fit without overlap. -/
  input_le : 2 * s.securityParameter + 1 + s.classicalInputLength + D.quantumInputWidth ≤ D.width
  /-- The adjacent argument and response registers fit. -/
  query_le : D.queryWidth + D.responseWidth ≤ D.width
  /-- Every output bit is an active qubit. -/
  output_le : D.outputWidth ≤ D.width
  /-- The total interpreter does not skip any instruction. -/
  instructions : ∀ g ∈ D.instructions, g.WellFormed D.queryWidth D.responseWidth D.width

end OracleCircuitDescription

/-- A native polynomial-time generator of valid oracle circuits. Its polynomial bound is in
the unary security parameter and classical input length. Quantum inputs are supplied states;
this structure does not certify their preparation, gate universality or interactive QROM access. -/
structure UniformOracleCircuitFamily where
  /-- The complete circuit description for the security parameter and classical input length. -/
  description : ℕ → ℕ → OracleCircuitDescription
  /-- One native generator computes every size and every instruction. -/
  computableInPolyTime_description : ComputableInPolyTime
    (fun s : OracleInputSize => description s.securityParameter s.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription
  /-- Validity for every input size. -/
  wellFormed : ∀ n ℓ, (description n ℓ).WellFormed ⟨n, ℓ⟩

namespace UniformOracleCircuitFamily

variable (F : UniformOracleCircuitFamily)

/-- Native generation bounds both register size and instruction count by one polynomial in
the two input sizes. Separate elementary/query counts are bounded by the instruction count. -/
theorem exists_resource_bound : ∃ c d : ℕ, ∀ n ℓ,
    (F.description n ℓ).width + (F.description n ℓ).instructions.length ≤
      c * (2 * n + ℓ + 2) ^ d := by
  obtain ⟨c, d, h⟩ := F.computableInPolyTime_description.polyBounded_length.exists_le
  refine ⟨c, d, fun n ℓ => ?_⟩
  refine (F.description n ℓ).width_add_length_le_encoding_length.trans ?_
  have hlen : (encOracleInputSize ⟨n, ℓ⟩).length + 1 = 2 * n + ℓ + 2 := by
    simp only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
      encUnary_apply, List.length_replicate]
    omega
  simpa only [hlen] using h ⟨n, ℓ⟩

/-- A polynomial bound on classical auxiliary lengths gives a native-computable polynomial
resource schedule for every shorter word. The length bound itself need not be computable. -/
theorem exists_computable_resource_bound {L : ℕ → ℕ} (hL : PolynomiallyBounded L) :
    ∃ B : ℕ → ℕ, ComputableInPolyTime B encUnary encUnary ∧ PolynomiallyBounded B ∧
      ∀ n ℓ, ℓ ≤ L n →
      (F.description n ℓ).width + (F.description n ℓ).instructions.length ≤ B n := by
  obtain ⟨c, d, h⟩ := F.exists_resource_bound
  obtain ⟨cL, dL, hLp⟩ := polynomiallyBounded_iff_le.mp hL
  let B : ℕ → ℕ := fun n => c * (2 * n + cL * (n + 1) ^ dL + 2) ^ d
  have hB : ComputableInPolyTime B encUnary encUnary := by
    dsimp only [B]
    fun_prop
  refine ⟨B, hB, hB.polynomiallyBounded, fun n ℓ hℓ => ?_⟩
  have hℓ' := hℓ.trans (hLp n)
  exact (h n ℓ).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d))

/-- Place a supplied quantum state after the encoded classical input `(n, x)`, with zero
ancillas elsewhere. This is an isometric embedding, not an efficient preparation of that state. -/
noncomputable def initialState (n : ℕ) (x : List Bool) :
    Qubits (F.description n x.length).quantumInputWidth →ₗᵢ[ℂ]
      Qubits (F.description n x.length).width :=
  embedState (blockEmb (2 * n + 1 + x.length) (F.wellFormed n x.length).input_le)
    (inputState (F.description n x.length).width (encPair encUnary encBits (n, x)))

/-- Initialization embeds an arbitrary supplied state after the encoded classical input. -/
theorem initialState_apply (n : ℕ) (x : List Bool)
    (ψ : Qubits (F.description n x.length).quantumInputWidth) :
    F.initialState n x ψ =
      embedState (blockEmb (2 * n + 1 + x.length) (F.wellFormed n x.length).input_le)
        (inputState (F.description n x.length).width (encPair encUnary encBits (n, x))) ψ := by
  unfold initialState
  rfl

/-- A basis quantum input is appended to the encoded classical input before the zero ancillas. -/
theorem initialState_ket (n : ℕ) (x : List Bool)
    (z : Fin (F.description n x.length).quantumInputWidth → Bool) :
    F.initialState n x (ket z) = ket (inputState (F.description n x.length).width
      (encPair encUnary encBits (n, x) ++ List.ofFn z)) := by
  rw [initialState, embedState_ket, glue_blockEmb_inputState _ _ (by simp)]

/-- Execute the generated circuit with the same fixed oracle throughout. The resulting map
retains every active qubit; terminal measurement is specified separately by `output`. -/
noncomputable def run (n : ℕ) (x : List Bool)
    (H : (Fin (F.description n x.length).queryWidth → Bool) →
      Fin (F.description n x.length).responseWidth → Bool) :
    Qubits (F.description n x.length).quantumInputWidth →ₗᵢ[ℂ]
      Qubits (F.description n x.length).width :=
  (Circuit.eval (OracleCircuit.toCircuit (F.description n x.length).width H
    (F.description n x.length).instructions)).toLinearIsometry.comp (F.initialState n x)

/-- Running the family uses the existing finite-circuit interpretation on its initialized state. -/
theorem run_apply (n : ℕ) (x : List Bool)
    (H : (Fin (F.description n x.length).queryWidth → Bool) →
      Fin (F.description n x.length).responseWidth → Bool)
    (ψ : Qubits (F.description n x.length).quantumInputWidth) :
    F.run n x H ψ = Circuit.eval (OracleCircuit.toCircuit (F.description n x.length).width H
      (F.description n x.length).instructions) (F.initialState n x ψ) := by
  unfold run
  rfl

/-- Terminal computational-basis measurement of the generated output prefix, returned as a bit
word. The supplied quantum input must be normalized. -/
noncomputable def output (n : ℕ) (x : List Bool)
    (H : (Fin (F.description n x.length).queryWidth → Bool) →
      Fin (F.description n x.length).responseWidth → Bool)
    (ψ : Qubits (F.description n x.length).quantumInputWidth) (hψ : ‖ψ‖ = 1) : PMF (List Bool) :=
  measureOut (F.run n x H ψ) (by rw [LinearIsometry.norm_map, hψ])
    (fun y => List.ofFn fun i => y (Fin.castLEEmb (F.wellFormed n x.length).output_le i))

/-- The output law is exactly the existing computational-basis measurement and prefix readout. -/
theorem output_eq (n : ℕ) (x : List Bool)
    (H : (Fin (F.description n x.length).queryWidth → Bool) →
      Fin (F.description n x.length).responseWidth → Bool)
    (ψ : Qubits (F.description n x.length).quantumInputWidth) (hψ : ‖ψ‖ = 1) :
    F.output n x H ψ hψ = measureOut (F.run n x H ψ)
      (by rw [LinearIsometry.norm_map, hψ])
      (fun y => List.ofFn fun i => y (Fin.castLEEmb (F.wellFormed n x.length).output_le i)) := by
  unfold output
  rfl

/-- Every supported output word has the declared output length. -/
theorem length_of_mem_support_output (n : ℕ) (x : List Bool)
    (H : (Fin (F.description n x.length).queryWidth → Bool) →
      Fin (F.description n x.length).responseWidth → Bool)
    (ψ : Qubits (F.description n x.length).quantumInputWidth) (hψ : ‖ψ‖ = 1)
    {out : List Bool} (h : out ∈ (F.output n x H ψ hψ).support) :
    out.length = (F.description n x.length).outputWidth := by
  rw [output_eq, measureOut, PMF.mem_support_map_iff] at h
  obtain ⟨y, _, rfl⟩ := h
  exact List.length_ofFn

end UniformOracleCircuitFamily

end Cslib.Quantum
