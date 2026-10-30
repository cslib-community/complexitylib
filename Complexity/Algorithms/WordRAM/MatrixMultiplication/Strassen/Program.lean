/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Program
public import Complexity.Computability.WordRAM.Signed.ArrayArithmetic.Program
public import Complexity.Computability.WordRAM.Copy
public import Complexity.Computability.WordRAM.Power

/-!
# Native cyclic-coefficient Strassen stack

The fixed controller traverses an explicit seven-word frame stack. Each nonleaf creates the
seven actual operand forms, calls the same controller on the child, and accumulates the
returned coefficient array into its output quadrants. Leaves execute the native quadratic
cyclic-convolution kernel. Every form, accumulation, copy, frame access and dispatch is code
on the standard unsigned machine, using the existing signed arithmetic kernels.

Inputs are runtime pointers to Morton-ordered coefficient arrays, the coefficient length,
a matrix depth, an output and a scratch base. The setup computes the actual array length.
The scratch layout uses three child-sized arrays at each level, followed by child scratch;
the explicit frames start after one root-array length of scratch. Output and scratch may
start dirty. This module defines code; its definition alone supplies neither correctness nor
a running-time theorem.

The seven products adapt the pinned Anthropic source Spec/Sec3/Theorem17/Strassen.lean and
Programs/Sec3/Theorem17/Hashing/Strassen.lean at revision
16a5ce41304fcdaea4e0be7c132e1c361dc26da5. The native iterative stack is original code.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

namespace Reg

/-- Low-bank result of the existing natural-power routine. -/
abbrev powerValue : Fin 64 := 0
/-- Low-bank base of the existing natural-power routine. -/
abbrev powerBase : Fin 64 := 2
/-- Low-bank exponent of the existing natural-power routine. -/
abbrev powerExponent : Fin 64 := 3

/-- Low-bank arguments of the native copying kernel. -/
abbrev copySource : Fin 64 := 0
/-- Low-bank destination of the native copying kernel. -/
abbrev copyTarget : Fin 64 := 1
/-- Low-bank word count of the native copying kernel. -/
abbrev copyLength : Fin 64 := 2
/-- Low-bank first operand of signed array kernels. -/
abbrev operandA : Fin 64 := 9
/-- Low-bank second operand of signed array kernels. -/
abbrev operandB : Fin 64 := 10
/-- Low-bank destination of signed array kernels. -/
abbrev target : Fin 64 := 11
/-- Low-bank coefficient count of signed array kernels. -/
abbrev length : Fin 64 := 12

/-- Current first matrix pointer. -/
abbrev inputA : Fin 64 := 32

/-- Current second matrix pointer. -/
abbrev inputB : Fin 64 := 33

/-- Current output pointer. -/
abbrev output : Fin 64 := 34

/-- Current scratch pointer. -/
abbrev scratch : Fin 64 := 35

/-- Current matrix depth. -/
abbrev depth : Fin 64 := 36

/-- Current matrix length in coefficient words. -/
abbrev size : Fin 64 := 37

/-- Zero on entry; one through seven after the corresponding child returns. -/
abbrev phase : Fin 64 := 38

/-- Current explicit frame pointer. -/
abbrev frame : Fin 64 := 39

/-- Root explicit frame pointer. -/
abbrev frames : Fin 64 := 40

/-- One until the root returns. -/
abbrev active : Fin 64 := 41

/-- Constant one. -/
abbrev one : Fin 64 := 42

/-- Constant four. -/
abbrev four : Fin 64 := 44

/-- Constant seven, the number of words per frame. -/
abbrev frameWidth : Fin 64 := 45

/-- Runtime cyclic coefficient length, preserved across all children. -/
abbrev modulus : Fin 64 := 46

/-- Initialization and clearing loop counter. -/
abbrev index : Fin 64 := 47

/-- Frame and output address temporary. -/
abbrev address : Fin 64 := 48

/-- Canonical signed zero and raw unsigned zero. -/
abbrev zero : Fin 64 := 49

/-- Coefficient length of a child quadrant. -/
abbrev quarter : Fin 64 := 50

/-- First child operand buffer. -/
abbrev formA : Fin 64 := 51

/-- Second child operand buffer. -/
abbrev formB : Fin 64 := 52

/-- Child product buffer. -/
abbrev product : Fin 64 := 53

/-- Start of scratch available to the child. -/
abbrev childScratch : Fin 64 := 54

/-- Computed child matrix depth. -/
abbrev childDepth : Fin 64 := 55

/-- Quarter-offset arithmetic temporary. -/
abbrev temporary : Fin 64 := 56

/-- Constant phase-dispatch temporary. -/
abbrev tag : Fin 64 := 57

end Reg

/-- Compute the address of a statically selected contiguous quadrant. -/
@[expose] def quadrant (base dst : Fin 64) (q : ℕ) : Code .standard 64 :=
  if q = 0 then ram[ dst ← base ] else
    ram[ Reg.temporary ← #q; Reg.temporary ← Reg.temporary * Reg.quarter;
      dst ← base + Reg.temporary ]

/-- Materialize an operand form, including a real copy in the single-quadrant case. -/
@[expose] def form (base dst : Fin 64) (q₁ q₂ : ℕ) (sign : ℤ) : Code .standard 64 :=
  if sign = 0 then
    .seq (quadrant base Reg.copySource q₁)
      (.seq (ram[ Reg.copyTarget ← dst; Reg.copyLength ← Reg.quarter ])
        (ArrayCopy.program.rename (Fin.castLE (by decide))))
  else
    .seq (quadrant base Reg.operandA q₁) (.seq (quadrant base Reg.operandB q₂)
      (.seq (ram[ Reg.target ← dst; Reg.length ← Reg.quarter ])
        ((Signed.ArrayArithmetic.program (sign < 0)).rename (Fin.castLE (by decide)))))

/-- Add or subtract the actual child product into one output quadrant. -/
@[expose] def accumulate (q : ℕ) (subtract : Bool) : Code .standard 64 :=
  .seq (quadrant Reg.output Reg.operandA q)
    (.seq (ram[ Reg.operandB ← Reg.product; Reg.target ← Reg.operandA;
      Reg.length ← Reg.quarter ])
      ((Signed.ArrayArithmetic.program subtract).rename (Fin.castLE (by decide))))

/-- Store the seven current frame fields at the computed frame address. -/
@[expose] def storeFrame : Code .standard 64 := ram[
  Reg.address ← Reg.frame; *Reg.address ← Reg.inputA;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.inputB;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.output;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.scratch;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.depth;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.size;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.phase ]

/-- Read every field of the actual current frame. -/
@[expose] def loadFrame : Code .standard 64 := ram[
  Reg.address ← Reg.frame; Reg.inputA ← *Reg.address;
  Reg.address ← Reg.address + Reg.one; Reg.inputB ← *Reg.address;
  Reg.address ← Reg.address + Reg.one; Reg.output ← *Reg.address;
  Reg.address ← Reg.address + Reg.one; Reg.scratch ← *Reg.address;
  Reg.address ← Reg.address + Reg.one; Reg.depth ← *Reg.address;
  Reg.address ← Reg.address + Reg.one; Reg.size ← *Reg.address;
  Reg.address ← Reg.address + Reg.one; Reg.phase ← *Reg.address ]

/-- Derive all child-buffer pointers from the loaded parent frame. -/
@[expose] def locateChild : Code .standard 64 := ram[
  Reg.quarter ← Reg.size / Reg.four;
  Reg.formA ← Reg.scratch; Reg.formB ← Reg.formA + Reg.quarter;
  Reg.product ← Reg.formB + Reg.quarter;
  Reg.childScratch ← Reg.product + Reg.quarter;
  Reg.childDepth ← Reg.depth - Reg.one ]

/-- One actual store per output coefficient; no global workspace clearing. -/
@[expose] def clear : Code .standard 64 :=
  .seq (ram[ Reg.address ← Reg.output; Reg.index ← Reg.output + Reg.size ])
    (zeroFill Reg.address Reg.index Reg.zero Reg.one)

/-- Save the parent's return phase and prepare the real child fields in registers. -/
@[expose] def pushArguments (phase : ℕ) : Code .standard 64 := ram[
  Reg.tag ← #6; Reg.address ← Reg.frame + Reg.tag;
  Reg.phase ← #phase; *Reg.address ← Reg.phase;
  Reg.frame ← Reg.frame + Reg.frameWidth;
  Reg.inputA ← Reg.formA; Reg.inputB ← Reg.formB; Reg.output ← Reg.product;
  Reg.scratch ← Reg.childScratch; Reg.depth ← Reg.childDepth; Reg.size ← Reg.quarter;
  Reg.phase ← #0 ]

/-- Save the parent's return phase, create a child frame, then let the controller enter it. -/
@[expose] def push (phase : ℕ) : Code .standard 64 := .seq (pushArguments phase) storeFrame

/-- Return to a real parent frame, or finish when the root has returned. -/
@[expose] def pop : Code .standard 64 := ram[
  if Reg.frames < Reg.frame then [ Reg.frame ← Reg.frame - Reg.frameWidth ]
  else [ Reg.active ← #0 ] ]

/-- A recursive child is dispatched only after both actual operand forms have been stored. -/
@[expose] def prepare (phase a₁ a₂ : ℕ) (asign : ℤ)
    (b₁ b₂ : ℕ) (bsign : ℤ) : Code .standard 64 :=
  .seq (form Reg.inputA Reg.formA a₁ a₂ asign)
    (.seq (form Reg.inputB Reg.formB b₁ b₂ bsign) (push phase))

/-- Execute the corresponding returned-child accumulation and prepare the next product. -/
@[expose] def stage : Fin 8 → Code .standard 64
  | 0 => .seq clear (prepare 1 0 3 1 0 3 1)
  | 1 => .seq (accumulate 0 false) (.seq (accumulate 3 false) (prepare 2 2 3 1 0 0 0))
  | 2 => .seq (accumulate 2 false) (.seq (accumulate 3 true) (prepare 3 0 0 0 1 3 (-1)))
  | 3 => .seq (accumulate 1 false) (.seq (accumulate 3 false) (prepare 4 3 3 0 2 0 (-1)))
  | 4 => .seq (accumulate 0 false) (.seq (accumulate 2 false) (prepare 5 0 1 1 3 3 0))
  | 5 => .seq (accumulate 0 true) (.seq (accumulate 1 false) (prepare 6 2 0 (-1) 0 1 1))
  | 6 => .seq (accumulate 3 false) (prepare 7 1 3 (-1) 2 3 1)
  | 7 => .seq (accumulate 0 false) pop

/-- Static seven-way branch chain reads the phase stored by the actual push. -/
@[expose] def dispatch : Code .standard 64 := ram[
  if Reg.phase = Reg.zero then [ ⟪stage 0⟫ ] else [
    Reg.tag ← #1; if Reg.phase = Reg.tag then [ ⟪stage 1⟫ ] else [
      Reg.tag ← #2; if Reg.phase = Reg.tag then [ ⟪stage 2⟫ ] else [
        Reg.tag ← #3; if Reg.phase = Reg.tag then [ ⟪stage 3⟫ ] else [
          Reg.tag ← #4; if Reg.phase = Reg.tag then [ ⟪stage 4⟫ ] else [
            Reg.tag ← #5; if Reg.phase = Reg.tag then [ ⟪stage 5⟫ ] else [
              Reg.tag ← #6; if Reg.phase = Reg.tag then [ ⟪stage 6⟫ ] else [
                ⟪stage 7⟫ ] ] ] ] ] ] ] ]

/-- A scalar leaf uses the real cyclic-convolution program, then returns through the stack. -/
@[expose] def leaf : Code .standard 64 :=
  .seq (ram[ Reg.operandA ← Reg.inputA; Reg.operandB ← Reg.inputB;
    Reg.target ← Reg.output; Reg.length ← Reg.modulus ])
    (.seq (CyclicConvolution.program.rename (Fin.castLE (by decide))) pop)

/-- One explicit stack iteration; it never invokes a recursive semantic evaluator. -/
@[expose] def step : Code .standard 64 := ram[
  ⟪loadFrame⟫;
  if Reg.depth = Reg.zero then [ ⟪leaf⟫ ] else [ ⟪locateChild⟫; ⟪dispatch⟫ ] ]

/-- Fixed controller constants and actual runtime arguments to the existing power routine. -/
@[expose] def powerArguments : Code .standard 64 := ram[
  Reg.zero ← #0; Reg.one ← #1; Reg.four ← #4; Reg.frameWidth ← #7;
  Reg.powerBase ← Reg.four; Reg.powerExponent ← Reg.depth ]

/-- Compute the coefficient-array length and actual root-frame address after the power call. -/
@[expose] def locateRoot : Code .standard 64 := ram[
  Reg.size ← Reg.powerValue * Reg.modulus;
  Reg.frames ← Reg.scratch + Reg.size; Reg.frame ← Reg.frames;
  Reg.phase ← #0; Reg.active ← #1 ]

/-- Actual runtime powers, stack placement and complete dirty-root frame initialization. -/
@[expose] def setup : Code .standard 64 :=
  .seq powerArguments (.seq (Power.program.rename (Fin.castLE (by decide)))
    (.seq locateRoot storeFrame))

/-- Fixed finite native code independent of coefficient length, depth and word size. -/
@[expose] def program : Code .standard 64 :=
  .seq setup (.loop (.lt Reg.zero Reg.active) step)

end Cslib.Algorithms.WordRAM.Strassen
