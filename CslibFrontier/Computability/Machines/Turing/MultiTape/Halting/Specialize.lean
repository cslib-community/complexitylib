/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.SMNBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength

/-!
# Specializing an encoded controller with another description

`Turing.MultiTapeTM.Universal.specialize controller program` builds the framed encoding of
`program` into the input of `controller`. Unlike an existential polynomial-time certificate, the
result is an explicit `Turing.MultiTapeTM.Universal.Desc`. This module accounts separately for
the generated description, the preparation and controller steps when that description is run,
the resource formula for interpreting it, and the offline compiler that produces it.

All description sizes use the universal machine's rigorous unary-state encoding. They are exact
statements about that model, not byte counts or tight estimates for another implementation. The
offline compiler is not charged to execution of the generated description; a construction that
runs the compiler must account for it separately.

## Main definitions

* `Turing.MultiTapeTM.Universal.specialize`: specialize a controller description with the framed
  encoding of a program description.
* `Turing.MultiTapeTM.Universal.specializeSize`: a concrete generated-description bound.
* `Turing.MultiTapeTM.Universal.specializePrepareSteps`: the exact preparation clock.
* `Turing.MultiTapeTM.Universal.specializeInterpreterInputBound`: a concrete bound on the unary
  universal-interpreter input, including the generated description.

## Main results

* `Turing.MultiTapeTM.Universal.descLen_specialize_le`: generated descriptions have the stated
  concrete quadratic bound.
* `Turing.MultiTapeTM.Universal.iterate_specialize`: after the exact preparation clock, the
  specialized description simulates the controller step for step.
* `Turing.MultiTapeTM.Universal.universal_specialize`: the corresponding executable universal
  machine equality.
* `Turing.MultiTapeTM.Universal.universal_specialize_resource_bounds`: explicit universal-machine
  time and space formulas including program size and preparation.
* `Turing.MultiTapeTM.Universal.computableInPolyTime_specialize`: the offline compiler is
  polynomial time.
-/

public section

namespace Turing.MultiTapeTM.Universal

/-- Build the self-delimiting encoded description `program` into the input of `controller`. -/
@[expose] def specialize (controller program : Desc) : Desc :=
  hardwire controller (frame (eDesc program))

/-- A concrete upper bound on the unary `eDesc` length of a specialized description. -/
@[expose] def specializeSize (controller program : Desc) : ℕ :=
  10000 * (descLen controller + descLen program + 1) ^ 2

/-- The exact number of online steps used to install the program description and residual input
before the controller starts. -/
@[expose] def specializePrepareSteps (program : Desc) (x : List Bool) : ℕ :=
  4 * descLen program + 2 * x.length + 6

/-- The `eDesc` length of the generated program is bounded quadratically in the two source
description lengths. The constant is a proved coarse bound for this unary encoding, not a
tightness claim. -/
theorem descLen_specialize_le (controller program : Desc) :
    descLen (specialize controller program) ≤ specializeSize controller program := by
  calc
    descLen (specialize controller program) ≤
        2500 * (encPair eDesc encBits
          (controller, frame (eDesc program))).length ^ 2 :=
      Hardwire.descLen_hardwire_le controller (frame (eDesc program))
    _ = specializeSize controller program := by
      simp only [length_encPair, descLen, encBits_apply, length_frame, specializeSize]
      ring

/-- The specialized controller computes exactly what the controller computes after its framed
program description and the residual input have been concatenated. -/
theorem Desc.computes_specialize (controller program : Desc) (x : List Bool) (o : List ℕ) :
    (specialize controller program).Computes (x.map eBit) o ↔
      controller.Computes ((frame (eDesc program) ++ x).map eBit) o := by
  exact Desc.computes_hardwire controller (frame (eDesc program)) x o

/-- Specialization preserves halting with the framed program description prepended. -/
theorem Desc.halts_specialize (controller program : Desc) (x : List Bool) :
    (specialize controller program).Halts (x.map eBit) ↔
      controller.Halts ((frame (eDesc program) ++ x).map eBit) := by
  exact Desc.halts_hardwire controller (frame (eDesc program)) x

/-- The complete online clock map: preparation costs `specializePrepareSteps program x`, then each
controller step costs exactly one specialized-description step. The right side retains the
redirected configuration so this statement also certifies intermediate machine state. -/
theorem iterate_specialize (controller program : Desc) (x : List Bool) (t : ℕ) :
    (stepOut (specialize controller program) (x.map eBit))^[
        specializePrepareSteps program x + t]
      (init (specialize controller program), []) =
        (Redirect.redirectCfg (fun q => 2 * q + 1) (x.length + 1) 0 []
          ((frame (eDesc program) ++ x).map eBit) [] []
          (((stepOut controller ((frame (eDesc program) ++ x).map eBit))^[t]
            (init controller, [])).1),
          ((stepOut controller ((frame (eDesc program) ++ x).map eBit))^[t]
            (init controller, [])).2) := by
  change
    (stepOut (hardwire controller (frame (eDesc program))) (x.map eBit))^[
        specializePrepareSteps program x + t]
      (init (hardwire controller (frame (eDesc program))), []) = _
  rw [show specializePrepareSteps program x =
      2 * ((frame (eDesc program)).length + x.length) + 4 by
    simp only [specializePrepareSteps, descLen, length_frame]
    omega]
  exact Hardwire.iterate_hardwire controller (frame (eDesc program)) x t

/-- Executing the specialized description for its preparation clock plus `t` steps returns exactly
the controller's `t`-step result on the embedded program and residual input. -/
theorem simulate_specialize (controller program : Desc) (x : List Bool) (t : ℕ) :
    simulate (specialize controller program) (x.map eBit)
        (specializePrepareSteps program x + t) =
      simulate controller ((frame (eDesc program) ++ x).map eBit) t := by
  rw [simulate, simulate, iterate_specialize]
  simp [Redirect.redirectCfg]

/-- The executable universal machine observes the same exact specialization clock map. -/
theorem universal_specialize (controller program : Desc) (x : List Bool) (t : ℕ) :
    universal (specialize controller program, x.map eBit,
        specializePrepareSteps program x + t) =
      universal (controller, (frame (eDesc program) ++ x).map eBit, t) := by
  exact simulate_specialize controller program x t

/-- A concrete upper bound on the unary encoding length of the universal-interpreter request for
a specialized description. It includes the generated code, residual input, preparation clock and
controller clock. -/
@[expose] def specializeInterpreterInputBound (controller program : Desc)
    (x : List Bool) (t : ℕ) : ℕ :=
  2 * specializeSize controller program + 1 +
    (2 * (3 * x.length) + 1 + (specializePrepareSteps program x + t))

theorem length_eInUnary_specialize_le (controller program : Desc) (x : List Bool) (t : ℕ) :
    (eInUnary (specialize controller program, x.map eBit,
      specializePrepareSteps program x + t)).length ≤
        specializeInterpreterInputBound controller program x t := by
  have hd := descLen_specialize_le controller program
  have hd' : (eDesc (specialize controller program)).length ≤
      specializeSize controller program := by
    simpa only [descLen] using hd
  have hx := length_encList_map_eBit_le x
  simp only [eInUnary, length_encPair, encUnary_apply, List.length_replicate]
  unfold specializeInterpreterInputBound
  omega

/-- The time expression certified by the universal-machine implementation for interpreting the
specialized request. This is an upper-bound formula, not a claim of exact elapsed CPU time. -/
@[expose] def specializeUniversalTimeFormula (controller program : Desc)
    (x : List Bool) (t : ℕ) : ℕ :=
  let clock := specializePrepareSteps program x + t
  (clock + 1) *
      (stepBound (descLen (specialize controller program))
          (encList encUnary (x.map eBit)).length clock +
        runBound (descLen (specialize controller program))
          (encList encUnary (x.map eBit)).length clock +
        ((encNat clock).length + 1) ^ 2) +
    ((eIn (specialize controller program, x.map eBit, clock)).length + 1) ^ 2

/-- The space expression certified by the universal-machine implementation for interpreting the
specialized request. -/
@[expose] def specializeUniversalSpaceFormula (controller program : Desc)
    (x : List Bool) (t : ℕ) : ℕ :=
  let clock := specializePrepareSteps program x + t
  runBound (descLen (specialize controller program))
      (encList encUnary (x.map eBit)).length clock +
    (eIn (specialize controller program, x.map eBit, clock)).length

/-- Concrete universal-machine resource bounds for the generated description. The request-size
bound includes the generated program size; the clock includes all online preparation and
controller steps. The offline compiler is deliberately separate. -/
theorem universal_specialize_resource_bounds (controller program : Desc)
    (x : List Bool) (t : ℕ) :
    specializeUniversalTimeFormula controller program x t ≤
        100025 * (specializeInterpreterInputBound controller program x t + 1) ^ 6 ∧
      specializeUniversalSpaceFormula controller program x t ≤
        205 * (specializeInterpreterInputBound controller program x t + 1) ^ 3 := by
  have h := universal_bounds_unary
    (specialize controller program, x.map eBit, specializePrepareSteps program x + t)
  have hlen := length_eInUnary_specialize_le controller program x t
  have hlen' :
      (eInUnary (specialize controller program, x.map eBit,
          specializePrepareSteps program x + t)).length + 1 ≤
        specializeInterpreterInputBound controller program x t + 1 := by
    omega
  have hpow6 := Nat.pow_le_pow_left hlen' 6
  have hpow3 := Nat.pow_le_pow_left hlen' 3
  constructor
  · exact h.1.trans (Nat.mul_le_mul_left 100025 hpow6)
  · exact h.2.trans (Nat.mul_le_mul_left 205 hpow3)

/-- Producing a specialized description from a controller/program pair is polynomial time in the
two encoded descriptions. This is the uniform offline compilation result; it does not charge the
compiler to a later run of the generated description. -/
theorem computableInPolyTime_specialize :
    ComputableInPolyTime (fun p : Desc × Desc => specialize p.1 p.2)
      (encPair eDesc eDesc) eDesc := by
  unfold specialize
  exact computableInPolyTime_hardwire.comp
    ((ComputableInPolyTime.fst eDesc eDesc).prod
      ((ComputableInPolyTime.frame.comp (ComputableInPolyTime.snd eDesc eDesc))))

end Turing.MultiTapeTM.Universal
