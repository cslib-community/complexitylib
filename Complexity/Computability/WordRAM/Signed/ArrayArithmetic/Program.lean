/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Native pointwise signed array addition and subtraction

These fixed loops perform the vector forms and accumulations needed by native Strassen.
The Boolean selects a fixed add or subtract block when constructing the code; every array
index, load, signed operation, store and loop instruction remains native and charged.
Parameters are ordinary absolute runtime pointers and a length.
-/

public section

namespace Cslib.WordRAM.Signed.ArrayArithmetic

namespace Reg

/-- First canonical signed array. -/
abbrev inputA : Fin 16 := 9
/-- Second canonical signed array. -/
abbrev inputB : Fin 16 := 10
/-- Output array, which may exactly alias an input. -/
abbrev output : Fin 16 := 11
/-- Runtime length of all three arrays. -/
abbrev length : Fin 16 := 12
/-- Current pointwise index. -/
abbrev index : Fin 16 := 13
/-- Load/store address temporary. -/
abbrev address : Fin 16 := 14
/-- Constant one. -/
abbrev one : Fin 16 := 15

end Reg

/-- Select a real native signed arithmetic block. -/
@[expose] def arithmetic (subtract : Bool) : Code .standard 16 :=
  if subtract then Signed.subtract else Signed.add

/-- Compute both operand addresses and read the actual words. -/
@[expose] def load : Code .standard 16 := ram[
  Reg.address ← Reg.inputA + Reg.index; Signed.left ← *Reg.address;
  Reg.address ← Reg.inputB + Reg.index; Signed.right ← *Reg.address ]

/-- Write the result and advance the index after both reads have completed. -/
@[expose] def finish : Code .standard 16 := ram[
  Reg.address ← Reg.output + Reg.index; *Reg.address ← Signed.result;
  Reg.index ← Reg.index + Reg.one ]

/-- One pointwise operation, including all array access work. -/
@[expose] def body (subtract : Bool) : Code .standard 16 :=
  .seq load (.seq (arithmetic subtract) finish)

/-- Fixed finite code for the entire array operation. -/
@[expose] def program (subtract : Bool) : Code .standard 16 :=
  .seq (ram[ Reg.index ← #0; Reg.one ← #1 ])
    (.loop (.lt Reg.index Reg.length) (body subtract))

end Cslib.WordRAM.Signed.ArrayArithmetic
