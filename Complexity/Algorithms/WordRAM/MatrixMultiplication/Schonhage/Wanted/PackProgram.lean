/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.QueryDigits

/-!
# Native output-digit packing

## Main definitions

* `Wanted.packCode`: fixed unsigned code for a binary mask and compressed row/column offsets.

The mask and both offsets are consumed in registers. No query string or dispatch table is
provided to this code, and no memory is read or written.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM

/-- Register containing the original depth. -/
abbrev depth : Fin 16 := 0
/-- Remaining binary subset mask. -/
abbrev mask : Fin 16 := 1
/-- Remaining compressed row offset. -/
abbrev row : Fin 16 := 2
/-- Remaining compressed column offset. -/
abbrev col : Fin 16 := 3
/-- Accumulated output code. -/
abbrev code : Fin 16 := 4
/-- Number of consumed coordinates. -/
abbrev level : Fin 16 := 5
/-- Next base-ten place. -/
abbrev power : Fin 16 := 6
/-- Current binary mask digit. -/
abbrev bit : Fin 16 := 7
/-- Current output digit. -/
abbrev digit : Fin 16 := 8
/-- Arithmetic scratch register. -/
abbrev temporary : Fin 16 := 9
/-- Constant one. -/
abbrev one : Fin 16 := 10
/-- Constant two. -/
abbrev two : Fin 16 := 11
/-- Constant three. -/
abbrev three : Fin 16 := 12
/-- Constant ten. -/
abbrev ten : Fin 16 := 13
/-- Constant nine. -/
abbrev nine : Fin 16 := 14

/-- Initialize loop counters and ordinary unsigned constants. -/
def packHead : Code .standard 16 := ram[
  one ← #1; two ← #2; three ← #3; ten ← #10; nine ← #9;
  code ← #0; level ← #0; power ← #1
]

/-- One actual digit decision, with row-major outer digits and inner digit nine. -/
def packBody : Code .standard 16 := ram[
  bit ← mask % two; mask ← mask / two;
  if bit < one then [
    digit ← row % three; digit ← digit * three;
    temporary ← col % three; digit ← digit + temporary;
    row ← row / three; col ← col / three
  ] else [ digit ← nine ];
  temporary ← digit * power; code ← code + temporary;
  power ← power * ten; level ← level + one
]

/-- A single finite program handles every runtime depth and both compressed offsets. -/
def packCode : Code .standard 16 :=
  .seq packHead (.loop (.lt level depth) packBody)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
