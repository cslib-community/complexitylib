/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run

/-!
# Encoded generators of uniform quantum oracle circuits

`UniformOracleCircuitFamily.GeneratorCertificate` selects one deterministic multi-tape machine
behind the existential polynomial-time uniformity proof. Its static program is the exact word
`Universal.eDesc certificate.code`. The certificate keeps its time and work-tape-space bounds
separate and identifies the exact generated output word with `encOracleCircuitDescription`.

`GeneratorResources` records four independent coordinates: static generator-program bits,
generator time, generator workspace and generated output bits. Addition and polynomial schedules
are componentwise. No result in this module adds static code or generated output bits to online
adversary runtime. Such a charge requires a separate theorem for the particular operation that
executes, interprets or copies those words. Random coins, circuit execution resources and oracle
queries likewise remain outside this deterministic offline certificate.

## Main definitions

* `Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate`: an encoded deterministic
  generator with separate polynomial time and workspace bounds.
* `Cslib.Quantum.UniformOracleCircuitFamily.GeneratorResources`: static code, time, workspace and
  exact output-size coordinates.
* `Cslib.Quantum.UniformOracleCircuitFamily.GeneratorResources.IsPolynomial`: componentwise
  polynomial schedules.

## Main results

* `Cslib.Quantum.UniformOracleCircuitFamily.exists_generatorCertificate` and
  `Cslib.Quantum.UniformOracleCircuitFamily.generatorCertificate`: every native uniform family
  has a selected encoded generator certificate.
* `Cslib.Quantum.UniformOracleCircuitFamily.GeneratorCertificate.resources_isPolynomial`:
  polynomial encoded input schedules induce componentwise polynomial generator schedules.
* `Cslib.Quantum.UniformOracleCircuitFamily.GeneratorResources.IsPolynomial.add`:
  componentwise sums preserve polynomial schedules.
-/

public section

namespace Cslib.Quantum.UniformOracleCircuitFamily

open Turing.MultiTapeTM

/-- One explicit encoded deterministic generator for a uniform oracle-circuit family. Time and
workspace are bounds indexed by the exact encoded input length. -/
structure GeneratorCertificate (F : UniformOracleCircuitFamily) where
  /-- The static deterministic generator program. -/
  code : Universal.Desc
  /-- An upper bound on generator steps as a function of encoded input length. -/
  time : ℕ → ℕ
  /-- An upper bound on visited work-tape cells as a function of encoded input length. -/
  workspace : ℕ → ℕ
  /-- The generator time bound is polynomial. -/
  time_polynomiallyBounded : PolynomiallyBounded time
  /-- The generator workspace bound is polynomial independently of time. -/
  workspace_polynomiallyBounded : PolynomiallyBounded workspace
  /-- At the stated time bound, the encoded program has halted with the exact encoded circuit
  description. -/
  computes : ∀ input : OracleInputSize,
    Universal.simulate code (List.map Universal.eBit (encOracleInputSize input))
        (time (encOracleInputSize input).length) =
      (List.map Universal.eBit (encOracleCircuitDescription
        (F.description input.securityParameter input.classicalInputLength)), true)
  /-- The universal simulation visits at most the stated number of work-tape cells. -/
  workspace_le : ∀ input : OracleInputSize,
    Universal.simSpace code (List.map Universal.eBit (encOracleInputSize input))
        (time (encOracleInputSize input).length) ≤
      workspace (encOracleInputSize input).length

/-- Independent resource coordinates of one offline generator run. `codeBits` is static across
inputs and `outputBits` is the exact generated circuit-description length. -/
structure GeneratorResources where
  /-- Bits in the selected static generator-program encoding. -/
  codeBits : ℕ
  /-- Generator steps. -/
  time : ℕ
  /-- Visited generator work-tape cells. -/
  workspace : ℕ
  /-- Bits in the generated circuit description. -/
  outputBits : ℕ

namespace GeneratorResources

/-- Componentwise addition of independent generator costs. This operation does not assert that
either generator is executed online. -/
@[expose] protected def add (r s : GeneratorResources) : GeneratorResources :=
  ⟨r.codeBits + s.codeBits, r.time + s.time, r.workspace + s.workspace,
    r.outputBits + s.outputBits⟩

instance : Add GeneratorResources := ⟨GeneratorResources.add⟩

@[simp] theorem add_codeBits (r s : GeneratorResources) :
    (r + s).codeBits = r.codeBits + s.codeBits := rfl

@[simp] theorem add_time (r s : GeneratorResources) :
    (r + s).time = r.time + s.time := rfl

@[simp] theorem add_workspace (r s : GeneratorResources) :
    (r + s).workspace = r.workspace + s.workspace := rfl

@[simp] theorem add_outputBits (r s : GeneratorResources) :
    (r + s).outputBits = r.outputBits + s.outputBits := rfl

/-- Every generator coordinate is polynomially bounded independently. -/
@[expose] def IsPolynomial (schedule : ℕ → GeneratorResources) : Prop :=
  PolynomiallyBounded (fun n => (schedule n).codeBits) ∧
    PolynomiallyBounded (fun n => (schedule n).time) ∧
    PolynomiallyBounded (fun n => (schedule n).workspace) ∧
    PolynomiallyBounded (fun n => (schedule n).outputBits)

/-- Componentwise sums of polynomial generator schedules remain polynomial. -/
theorem IsPolynomial.add {r s : ℕ → GeneratorResources}
    (hr : IsPolynomial r) (hs : IsPolynomial s) :
    IsPolynomial (fun n => r n + s n) :=
  ⟨hr.1.add hs.1, hr.2.1.add hs.2.1, hr.2.2.1.add hs.2.2.1,
    hr.2.2.2.add hs.2.2.2⟩

end GeneratorResources

namespace GeneratorCertificate

variable {F : UniformOracleCircuitFamily} (certificate : F.GeneratorCertificate)

/-- The four separate costs of the certified generator on one input. -/
@[expose] def resources (input : OracleInputSize) : GeneratorResources :=
  ⟨(Universal.eDesc certificate.code).length,
    certificate.time (encOracleInputSize input).length,
    certificate.workspace (encOracleInputSize input).length,
    (encOracleCircuitDescription
      (F.description input.securityParameter input.classicalInputLength)).length⟩

/-- The certificate's output-size coordinate is exactly the circuit-description encoding charged
by `OracleCircuit.Resources.descriptionBits`. -/
theorem resources_outputBits (input : OracleInputSize) :
    (certificate.resources input).outputBits =
      (encOracleCircuitDescription
        (F.description input.securityParameter input.classicalInputLength)).length := rfl

/-- A polynomial schedule of encoded generator inputs induces polynomial bounds for every
generator coordinate, without collapsing any coordinate into another. -/
theorem resources_isPolynomial {input : ℕ → OracleInputSize}
    (hinput : PolynomiallyBounded fun n => (encOracleInputSize (input n)).length) :
    GeneratorResources.IsPolynomial (fun n => certificate.resources (input n)) := by
  refine ⟨.const _, certificate.time_polynomiallyBounded.comp hinput,
    certificate.workspace_polynomiallyBounded.comp hinput, ?_⟩
  exact (F.computableInPolyTime_description.polyBounded_length.comp
    (PolyBounded.of_polynomiallyBounded id hinput)).polynomiallyBounded

end GeneratorCertificate

/-- Native polynomial-time uniformity has a finite-state witness whose exact universal-machine
description, time, workspace and output can be exposed componentwise. -/
theorem exists_generatorCertificate (F : UniformOracleCircuitFamily) :
    Nonempty F.GeneratorCertificate := by
    classical
    obtain ⟨time, workspace, htime, hworkspace, k, State, hfinite, machine, hmachine⟩ :=
      F.computableInPolyTime_description
    let _ : Finite State := hfinite
    have _ := Fintype.ofFinite State
    let encodeState : State ↪ ℕ :=
      (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
    refine ⟨
      { code := Universal.desc encodeState Universal.eBit machine
        time := time
        workspace := workspace
        time_polynomiallyBounded := htime
        workspace_polynomiallyBounded := hworkspace
        computes := ?_
        workspace_le := ?_ }⟩
    · intro input
      have hrun := (hmachine input).runFrom_of_le le_rfl
      rw [Universal.simulate_desc, hrun.2]
      have hhalt : (machine.runFrom (machine.initCfg (encOracleInputSize input))
          (time (encOracleInputSize input).length)).state = none := hrun.1
      exact Prod.ext rfl (by rw [hhalt]; rfl)
    · intro input
      rw [Universal.simSpace_desc]
      exact space_le_of_runsInSpace (hmachine input).2.2 _

/-- Select the finite-state machine witnessed by native polynomial-time uniformity and expose its
exact universal-machine description. The choice is static; this definition does not run the
generator as part of circuit execution. -/
noncomputable def generatorCertificate (F : UniformOracleCircuitFamily) : F.GeneratorCertificate :=
  Classical.choice F.exists_generatorCertificate

end Cslib.Quantum.UniformOracleCircuitFamily
