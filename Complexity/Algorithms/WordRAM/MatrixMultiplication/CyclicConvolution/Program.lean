/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Native cyclic convolution of signed coefficient arrays

The fixed program computes each coefficient by a loop over the first factor. Both arrays
contain canonical signed words; their addresses and length are unsigned. The partner index
is computed by an actual comparison and subtraction, including the wrap case. Multiplication
and addition use the existing signed kernels, without extending the instruction basis.

This is the coefficient kernel needed by the native cyclic-ring Strassen counter in #1701;
it is not matrix multiplication or modular triangle counting by itself.

The algorithm adapts the cyclic-convolution loop in the pinned Anthropic source,
Programs/Sec3/Theorem17/Hashing/RingOps.lean, lines 174–196, at
16a5ce41304fcdaea4e0be7c132e1c361dc26da5. The encoded native implementation is original.
-/

public section

namespace Cslib.Algorithms.WordRAM.CyclicConvolution

open Cslib.WordRAM

namespace Reg

/-- Base of the first canonical signed coefficient array. -/
abbrev inputA : Fin 32 := 9
/-- Base of the second canonical signed coefficient array. -/
abbrev inputB : Fin 32 := 10
/-- Base of the output coefficient array. -/
abbrev output : Fin 32 := 11
/-- Runtime number of coefficients. -/
abbrev length : Fin 32 := 12
/-- Current output coefficient. -/
abbrev coefficient : Fin 32 := 13
/-- Current summation index. -/
abbrev index : Fin 32 := 14
/-- Computed cyclic partner index. -/
abbrev partner : Fin 32 := 15
/-- Canonical signed partial sum. -/
abbrev accumulator : Fin 32 := 16
/-- Address-calculation scratch. -/
abbrev address : Fin 32 := 17
/-- Constant one, initialized by the program. -/
abbrev one : Fin 32 := 18

end Reg

/-- Compute the cyclic partner using unsigned arithmetic in the two disjoint cases. -/
@[expose] def selectPartner : Code .standard 32 :=
  .branch (.lt Reg.coefficient Reg.index)
    (ram[ Reg.partner ← Reg.coefficient + Reg.length;
      Reg.partner ← Reg.partner - Reg.index ])
    (ram[ Reg.partner ← Reg.coefficient - Reg.index ])

/-- Load the two actual signed coefficients at their computed addresses. -/
@[expose] def loadOperands : Code .standard 32 := ram[
  Reg.address ← Reg.inputA + Reg.index; Signed.left ← *Reg.address;
  Reg.address ← Reg.inputB + Reg.partner; Signed.right ← *Reg.address ]

/-- Compute one signed product from the actual input arrays. -/
@[expose] def productTerm : Code .standard 32 :=
  .seq selectPartner (.seq loadOperands Signed.multiply)

/-- Preserve the product as the right operand and load the partial sum as the left operand. -/
@[expose] def addArguments : Code .standard 32 := ram[
  Signed.right ← Signed.result; Signed.left ← Reg.accumulator ]

/-- Retain the new partial sum and advance the inner counter. -/
@[expose] def finishTerm : Code .standard 32 := ram[
  Reg.accumulator ← Signed.result; Reg.index ← Reg.index + Reg.one ]

/-- One real signed product followed by signed accumulation and index advancement. -/
@[expose] def term : Code .standard 32 :=
  .seq productTerm (.seq addArguments (.seq Signed.add finishTerm))

/-- Compute and store a complete coefficient, then advance the output index. -/
@[expose] def coefficient : Code .standard 32 :=
  .seq (ram[ Reg.index ← #0; Reg.accumulator ← #0 ])
    (.seq (.loop (.lt Reg.index Reg.length) term)
      (ram[ Reg.address ← Reg.output + Reg.coefficient; *Reg.address ← Reg.accumulator;
        Reg.coefficient ← Reg.coefficient + Reg.one ]))

/-- The entire coefficient multiplication uses a fixed register bank and actual nested loops. -/
@[expose] def program : Code .standard 32 :=
  .seq (ram[ Reg.coefficient ← #0; Reg.one ← #1 ])
    (.loop (.lt Reg.coefficient Reg.length) coefficient)

end Cslib.Algorithms.WordRAM.CyclicConvolution
