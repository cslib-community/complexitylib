/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Input

/-!
# Initialized code from original raw dimension/bound and signed matrices

The input is the existing two-scalar `CountPrime.inputWords` representation, with its second
scalar interpreted as the original magnitude bound F, not as an externally selected prime.
The actual existing counter header only reads/copies that word and computes original pointers;
no modular counter is called until the later real selector computes eligible primes itself.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

/-- Reuse the real nine-instruction header, then deliver the original six-word host protocol. -/
@[expose] def entryHeader : Code .standard 640 :=
  let bank := selectorBank ∘ PrimeSelection.counterRegisters
  let n := bank CountPrime.Reg.side
  let F := bank CountPrime.Reg.modulus
  let ab := bank CountPrime.Reg.inputAB
  let bc := bank CountPrime.Reg.inputBC
  let ac := bank CountPrime.Reg.inputAC
  let free := bank CountPrime.Reg.scratch
  .seq (CountPrime.input.rename bank) (ram[
    Reg.side ← n; Reg.bound ← F; Reg.ab ← ab; Reg.bc ← bc; Reg.ac ← ac; Reg.free ← free ])

/-- One fixed program from actual initialized original inputs, with all parameters computed. -/
@[expose] def entryProgram : Code .standard 640 := .seq entryHeader program

/-- All original-input header and pointer work uses exactly fifteen actual instructions. -/
theorem entryHeader_fixed : entryHeader.size = 15 ∧ ¬entryHeader.ReadsWidth := by decide +kernel

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
