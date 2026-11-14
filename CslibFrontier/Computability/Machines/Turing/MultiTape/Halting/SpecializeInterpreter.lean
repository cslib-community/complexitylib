/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Specialize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Interpreter

/-!
# Componentwise resources for interpreting specialized descriptions

This module applies the encoded deterministic interpreter to
`Turing.MultiTapeTM.Universal.specialize`. Its certificate keeps five quantities separate:

1. static bits of the interpreter description;
2. bits of the generated specialized program;
3. bits of the unary-clock interpreter request;
4. online native interpreter steps; and
5. online native interpreter workspace.

The online fields include `encodedUniversalInterpreterFactor`, the named constant still hidden by
the existing native machine construction. The `100025` and `205` constants bound the established
implementation formulas; they are not presented alone as native machine constants. The offline
compiler remains the separate theorem `computableInPolyTime_specialize` and is not charged to a
later run. No scalar total combines the five fields: a client must state and prove any convention
that converts their unlike units.

## Main definitions

* `Turing.MultiTapeTM.Universal.specializeInterpreterRequest`: the generated description, input,
  and complete online clock.
* `Turing.MultiTapeTM.Universal.SpecializeInterpreterResources`: the five resource components.
* `Turing.MultiTapeTM.Universal.specializeInterpreterResources`: their explicit values.

## Main results

* `Turing.MultiTapeTM.Universal.specializeInterpreterResources_certifies`: all five components
  bound the corresponding construction or run quantity.
* `Turing.MultiTapeTM.Universal.universal_encodedUniversalInterpreter_specialize`: the selected
  encoded interpreter executes the specialized request within the componentwise online clock.
-/

public section

namespace Turing.MultiTapeTM.Universal

/-- The request executed after specializing `controller` with `program`. Its clock contains the
online preparation and controller steps, but no offline compilation cost. -/
@[expose] def specializeInterpreterRequest (controller program : Desc) (x : List Bool) (t : ℕ) :
    Desc × List ℕ × ℕ :=
  (specialize controller program, x.map eBit, specializePrepareSteps program x + t)

/-- Separate static, request, time and workspace components for executing a specialized program
through `encodedUniversalInterpreter`. -/
structure SpecializeInterpreterResources where
  /-- Static bits of the encoded universal interpreter. -/
  interpreterBits : ℕ
  /-- Static bits of the generated specialized description. -/
  programBits : ℕ
  /-- Bits of the unary-clock request used to bound the implementation formulas. -/
  requestBits : ℕ
  /-- Online steps of the selected native interpreter, including its named construction factor. -/
  onlineSteps : ℕ
  /-- Online workspace of the selected native interpreter, including the same factor. -/
  workspaceCells : ℕ

/-- The componentwise resources for a specialized interpreter request. Interpreter bits and
generated program bits remain static fields; neither is silently added to `onlineSteps`. -/
@[expose] noncomputable def specializeInterpreterResources (controller program : Desc)
    (x : List Bool) (t : ℕ) : SpecializeInterpreterResources :=
  let requestBits := specializeInterpreterInputBound controller program x t
  {
    interpreterBits := encodedUniversalInterpreterSizeBound
    programBits := specializeSize controller program
    requestBits
    onlineSteps := encodedUniversalInterpreterFactor *
      (100025 * (requestBits + 1) ^ 6 + 1)
    workspaceCells := encodedUniversalInterpreterFactor *
      (205 * (requestBits + 1) ^ 3 + 1) }

/-- What it means for the five resource components to certify a specialized request. -/
structure SpecializeInterpreterResources.Certifies (resources : SpecializeInterpreterResources)
    (controller program : Desc) (x : List Bool) (t : ℕ) : Prop where
  /-- The selected interpreter's `eDesc` length is charged statically. -/
  interpreterBits : descLen encodedUniversalInterpreter ≤ resources.interpreterBits
  /-- The generated specialized program's `eDesc` length is charged statically. -/
  programBits : descLen (specialize controller program) ≤ resources.programBits
  /-- The unary-clock request length is charged separately. -/
  requestBits : (eInUnary (specializeInterpreterRequest controller program x t)).length ≤
    resources.requestBits
  /-- The selected native interpreter's certified clock is bounded by `onlineSteps`. -/
  onlineSteps : encodedUniversalInterpreterTime
    (specializeInterpreterRequest controller program x t) ≤ resources.onlineSteps
  /-- Its certified workspace is bounded separately. -/
  workspaceCells : encodedUniversalInterpreterSpace
    (specializeInterpreterRequest controller program x t) ≤ resources.workspaceCells

/-- The explicit resource components certify the interpreter, generated program, request, online
runtime and workspace independently. The `100025` and `205` formulas are lifted through the named
native factor rather than mistaken for exact native constants. -/
theorem specializeInterpreterResources_certifies (controller program : Desc) (x : List Bool)
    (t : ℕ) :
    (specializeInterpreterResources controller program x t).Certifies controller program x t := by
  have hformulas := universal_specialize_resource_bounds controller program x t
  refine ⟨descLen_encodedUniversalInterpreter_le, descLen_specialize_le controller program,
    ?_, ?_, ?_⟩
  · exact length_eInUnary_specialize_le controller program x t
  · simp only [encodedUniversalInterpreterTime, specializeInterpreterRequest,
      universalImplementationTime, specializeInterpreterResources]
    exact Nat.mul_le_mul_left encodedUniversalInterpreterFactor
      (Nat.add_le_add_right hformulas.1 1)
  · simp only [encodedUniversalInterpreterSpace, specializeInterpreterRequest,
      universalImplementationSpace, specializeInterpreterResources]
    exact Nat.mul_le_mul_left encodedUniversalInterpreterFactor
      (Nat.add_le_add_right hformulas.2 1)

/-- Executing the generated request through `encodedUniversalInterpreter` at its componentwise
online clock returns the controller result. The source program affects the generated program and
request fields; offline construction is still governed separately by
`computableInPolyTime_specialize`. -/
theorem universal_encodedUniversalInterpreter_specialize (controller program : Desc)
    (x : List Bool) (t : ℕ) :
    universal (encodedUniversalInterpreter,
        (eIn (specializeInterpreterRequest controller program x t)).map eBit,
        (specializeInterpreterResources controller program x t).onlineSteps) =
      ((eOut (universal
        (controller, (frame (eDesc program) ++ x).map eBit, t))).map eBit, true) := by
  have hresources := specializeInterpreterResources_certifies controller program x t
  calc
    _ = ((eOut (universal (specializeInterpreterRequest controller program x t))).map eBit,
        true) := universal_encodedUniversalInterpreter _ _ hresources.onlineSteps
    _ = _ := by
      simp only [specializeInterpreterRequest]
      rw [universal_specialize]

end Turing.MultiTapeTM.Universal
