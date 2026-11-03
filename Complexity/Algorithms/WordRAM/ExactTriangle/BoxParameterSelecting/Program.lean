/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Properties
public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxDyadicParameters.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime.Program

/-!
# Automatic native Exact Triangle with integer box parameters

The existing original-argument saves, actual counting-based prime selector, exhaustive small
solver and restoration code are reused. The changed parameter block really computes the
2394-bit/63-level family, and the changed fast call really executes the compiled box solver.
The old host ABI and register banks are unchanged; no parameters, prime or solver certificate
is supplied to this fixed native program.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting

open Cslib.WordRAM ParameterSelecting

/-- Actual retuned parameter execution in the existing disjoint sixteen-register bank. -/
@[expose] def parameters : Code .standard 640 :=
  BoxDyadicParameters.program.rename parameterBank

/-- Deliver the actual selected prime and execute the complete box-backed callable solver. -/
@[expose] def solve : Code .standard 640 :=
  let p := CallableFixedPrime.Reg.prime
  let chosen := selectorBank PrimeSelection.Reg.best
  .seq (ram[ p ← chosen ]) CallableBoxFixedPrime.program

/-- Actual argument delivery, concrete prime selection and actual box solving. -/
@[expose] def fast : Code .standard 640 := .seq selectArguments (.seq selectPrime solve)

/-- One fixed native solver computes parameters/prime and decides the original signed input. -/
@[expose] def program : Code .standard 640 :=
  let flag := parameterBank DyadicParameters.Reg.fast
  .seq save (.seq parameters
    (.seq (.branch (.lt CallableFixedPrime.Reg.prime flag) fast slow) restore))

end Cslib.Algorithms.WordRAM.ExactTriangle.BoxParameterSelecting
