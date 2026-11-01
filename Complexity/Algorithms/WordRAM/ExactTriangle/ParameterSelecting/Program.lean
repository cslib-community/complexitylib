/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Program
public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Slow

/-!
# Actual parameter-selecting native ExactTriangle code

One fixed program consumes the existing host ABI: raw n,F,AB,BC,AC,workspace in registers0–5,
and returns a raw Boolean in6 while restoring0–5. The real dyadic parameter block occupies144–159,
the actual selector occupies the low160, and the complete callable solver retains its640 bank.
The original F is saved in143; original dimension/pointers/workspace stay in600,604–607.

The flag computed by the parameter program dispatches to the real exhaustive block below the
fast geometry threshold. Every save, delivery, selection, return and restoration is actual code.
No parameters, selected prime, layout, solver, execution or time certificate is an input.
These stage definitions are internal execution-composition interfaces.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

namespace Reg
/-- Original raw side length, restored on return. -/
abbrev side : Fin 640 := 0
/-- Original raw positive magnitude bound, restored on return. -/
abbrev bound : Fin 640 := 1
/-- Original canonical-signed AB pointer, restored on return. -/
abbrev ab : Fin 640 := 2
/-- Original canonical-signed BC pointer, restored on return. -/
abbrev bc : Fin 640 := 3
/-- Original canonical-signed AC pointer, restored on return. -/
abbrev ac : Fin 640 := 4
/-- Original dirty workspace boundary, restored on return. -/
abbrev free : Fin 640 := 5
/-- Raw original-weight ET Boolean. -/
abbrev result : Fin 640 := 6
/-- Saved original magnitude bound; both selector and callable solver preserve it. -/
abbrev savedBound : Fin 640 := 143
end Reg

/-- Actual disjoint placement of the complete16-register parameter code. -/
@[expose] def parameterBank (i : Fin 16) : Fin 640 := ⟨144 + i.val, by omega⟩

/-- The complete concrete selector occupies the low160 registers. -/
@[expose] def selectorBank : Fin 160 → Fin 640 := Fin.castLE (by decide)

/-- The existing exhaustive program occupies the low24 registers. -/
@[expose] def slowBank : Fin 24 → Fin 640 := Fin.castLE (by decide)

/-- Save all original host arguments and deliver n to the real parameter block. -/
@[expose] def save : Code .standard 640 :=
  let n := CallableFixedPrime.Reg.n
  let a := CallableFixedPrime.Reg.ab
  let b := CallableFixedPrime.Reg.bc
  let c := CallableFixedPrime.Reg.ac
  let free := CallableFixedPrime.Reg.base
  let prime := CallableFixedPrime.Reg.prime
  let input := parameterBank DyadicParameters.Reg.side
  ram[ Reg.savedBound ← Reg.bound; n ← Reg.side; a ← Reg.ab; b ← Reg.bc;
    c ← Reg.ac; free ← Reg.free; input ← Reg.side; prime ← #0 ]

/-- The entire actual parameter computation, not a supplied exponent or geometry flag. -/
@[expose] def parameters : Code .standard 640 := DyadicParameters.program.rename parameterBank

/-- Preserve actual D,g and deliver original arrays to the actual selector. -/
@[expose] def selectArguments : Code .standard 640 :=
  let dimension := CallableFixedPrime.Reg.dimension
  let groups := CallableFixedPrime.Reg.groups
  let computedD := parameterBank DyadicParameters.Reg.window
  let computedG := parameterBank DyadicParameters.Reg.groups
  let n := CallableFixedPrime.Reg.n
  let a := CallableFixedPrime.Reg.ab
  let b := CallableFixedPrime.Reg.bc
  let c := CallableFixedPrime.Reg.ac
  let free := CallableFixedPrime.Reg.base
  let side := selectorBank PrimeSelection.Reg.side
  let window := selectorBank PrimeSelection.Reg.window
  let ab := selectorBank PrimeSelection.Reg.inputAB
  let bc := selectorBank PrimeSelection.Reg.inputBC
  let ac := selectorBank PrimeSelection.Reg.inputAC
  let scratch := selectorBank PrimeSelection.Reg.scratch
  ram[ dimension ← computedD; groups ← computedG; side ← n; window ← dimension;
    ab ← a; bc ← b; ac ← c; scratch ← free ]

/-- Complete native prime enumeration and actual cyclic-Strassen counting. -/
@[expose] def selectPrime : Code .standard 640 :=
  (PrimeSelection.program CountPrime.program).rename selectorBank

/-- Deliver the actual selected prime to the actual complete callable solver. -/
@[expose] def solve : Code .standard 640 :=
  let p := CallableFixedPrime.Reg.prime
  let chosen := selectorBank PrimeSelection.Reg.best
  .seq (ram[ p ← chosen ]) CallableFixedPrime.program

/-- Deliver original arguments to the existing small-input exhaustive block. -/
@[expose] def slowArguments : Code .standard 640 := ram[
  Reg.side ← CallableFixedPrime.Reg.n; Reg.bound ← Reg.savedBound;
  Reg.ab ← CallableFixedPrime.Reg.ab; Reg.bc ← CallableFixedPrime.Reg.bc;
  Reg.ac ← CallableFixedPrime.Reg.ac; Reg.free ← CallableFixedPrime.Reg.base ]

/-- Real exhaustive small-input solving, including raw result transfer. -/
@[expose] def slow : Code .standard 640 :=
  .seq slowArguments (.seq (ThreeSum.Host.Slow.program.rename slowBank)
    (ram[ CallableFixedPrime.Reg.found ← Reg.result ]))

/-- Actual selector delivery, complete selection and complete fixed-prime solving. -/
@[expose] def fast : Code .standard 640 := .seq selectArguments (.seq selectPrime solve)

/-- Restore every original host argument and deliver the actual raw Boolean. -/
@[expose] def restore : Code .standard 640 := ram[
  Reg.side ← CallableFixedPrime.Reg.n; Reg.bound ← Reg.savedBound;
  Reg.ab ← CallableFixedPrime.Reg.ab; Reg.bc ← CallableFixedPrime.Reg.bc;
  Reg.ac ← CallableFixedPrime.Reg.ac; Reg.free ← CallableFixedPrime.Reg.base;
  Reg.result ← CallableFixedPrime.Reg.found ]

/-- One finite runtime program computes parameters/prime and decides original ExactTriangle.
The fast flag is read before the selected-prime delivery overwrites its initial zero argument. -/
@[expose] def program : Code .standard 640 :=
  let flag := parameterBank DyadicParameters.Reg.fast
  .seq save (.seq parameters
    (.seq (.branch (.lt CallableFixedPrime.Reg.prime flag) fast slow) restore))

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
