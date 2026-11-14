/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Generator
public import CslibFrontierTests.QuantumOracleUniformFamily

/-! The selected generator for a genuinely growing family exposes static code, separate
time/workspace bounds and exact generated output size. -/

public section

namespace CslibFrontierTests.QuantumOracleGenerator

open Cslib Cslib.Quantum Turing.MultiTapeTM
open Cslib.Quantum.UniformOracleCircuitFamily
open CslibFrontierTests.QuantumOracleUniform

noncomputable def phaseGeneratorCertificate : phaseFamily.GeneratorCertificate :=
  phaseFamily.generatorCertificate

-- The client is nonconstant in both its finite description and its encoded output.
example : (phaseFamily.description 0 0).width ≠ (phaseFamily.description 1 0).width := by decide

example : (encOracleCircuitDescription (phaseFamily.description 0 0)).length <
    (encOracleCircuitDescription (phaseFamily.description 1 0)).length := by decide

-- One static program produces both exact encoded descriptions at its certified time bounds.
example :
    Universal.simulate phaseGeneratorCertificate.code
        (List.map Universal.eBit (encOracleInputSize ⟨0, 0⟩))
        (phaseGeneratorCertificate.time (encOracleInputSize ⟨0, 0⟩).length) =
      (List.map Universal.eBit (encOracleCircuitDescription (phaseFamily.description 0 0)), true) :=
  phaseGeneratorCertificate.computes ⟨0, 0⟩

example :
    Universal.simulate phaseGeneratorCertificate.code
        (List.map Universal.eBit (encOracleInputSize ⟨1, 0⟩))
        (phaseGeneratorCertificate.time (encOracleInputSize ⟨1, 0⟩).length) =
      (List.map Universal.eBit (encOracleCircuitDescription (phaseFamily.description 1 0)), true) :=
  phaseGeneratorCertificate.computes ⟨1, 0⟩

-- Static code bits and generated output bits remain separate exact coordinates.
example (input : OracleInputSize) :
    (phaseGeneratorCertificate.resources input).codeBits =
      (Universal.eDesc phaseGeneratorCertificate.code).length := rfl

example (input : OracleInputSize) :
    (phaseGeneratorCertificate.resources input).outputBits =
      (encOracleCircuitDescription
        (phaseFamily.description input.securityParameter input.classicalInputLength)).length :=
  phaseGeneratorCertificate.resources_outputBits input

-- A polynomial family of encoded inputs has a componentwise polynomial generator schedule.
example : GeneratorResources.IsPolynomial
    (fun n => phaseGeneratorCertificate.resources ⟨n, n + 1⟩) := by
  apply phaseGeneratorCertificate.resources_isPolynomial
  simp only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
    encUnary_apply, List.length_replicate]
  fun_prop

-- Composition adds each coordinate to itself; it does not fold code/output bits into time.
example : GeneratorResources.IsPolynomial
    (fun n => phaseGeneratorCertificate.resources ⟨n, n + 1⟩ +
      phaseGeneratorCertificate.resources ⟨n, 0⟩) := by
  apply GeneratorResources.IsPolynomial.add
  · apply phaseGeneratorCertificate.resources_isPolynomial
    simp only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
      encUnary_apply, List.length_replicate]
    fun_prop
  · apply phaseGeneratorCertificate.resources_isPolynomial
    simp only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
      encUnary_apply, List.length_replicate]
    fun_prop

end CslibFrontierTests.QuantumOracleGenerator
