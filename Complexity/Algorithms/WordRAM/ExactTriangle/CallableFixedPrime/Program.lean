/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Parameters
public import Complexity.Computability.WordRAM.CopySum
public import Complexity.Computability.WordRAM.MemoryWindow
public import Complexity.Computability.WordRAM.Power
public import Complexity.Computability.WordRAM.RegisterFrame
public import Complexity.Algorithms.WordRAM.NatClog

/-!
# Caller-safe fixed-prime native code

The fixed 640-register standard program protects the selector's entire low 160-register bank.
Arguments 600–607 are raw n,D,g,p, signed AB/BC/AC pointers and workspace base. They survive.
Raw verdict/witness/scans return in 632–636. Registers 160–578 embed the complete translated
416-register fixed-prime solver and its three memory-window registers.

The adapter copies exactly the three original arrays into its workspace, accumulating their
actual raw words. It writes five original-input headers and computes its own source modulus
with native ceiling-logarithm and power loops. No caller catalogue or reserved window is
cleared or copied. The real one-time producer and all-record traversal remain unchanged.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

namespace Reg

/-- Original side length. -/
abbrev n : Fin 640 := 600
/-- Runtime inner dimension, required to be a power of four by the correctness theorem. -/
abbrev dimension : Fin 640 := 601
/-- Runtime piece parameter. -/
abbrev groups : Fin 640 := 602
/-- Runtime fixed prime. -/
abbrev prime : Fin 640 := 603
/-- Canonical signed AB source pointer. -/
abbrev ab : Fin 640 := 604
/-- Canonical signed BC source pointer. -/
abbrev bc : Fin 640 := 605
/-- Canonical signed AC source pointer. -/
abbrev ac : Fin 640 := 606
/-- Caller-owned base of the dirty working interval. -/
abbrev base : Fin 640 := 607
/-- Computed raw-word sum of all three original matrices. -/
abbrev total : Fin 640 := 608
/-- Computed square side length. -/
abbrev area : Fin 640 := 609
/-- Header word count. -/
abbrev length : Fin 640 := 611
/-- Header store address. -/
abbrev address : Fin 640 := 612
/-- Constant one used for the five header stores. -/
abbrev one : Fin 640 := 615
/-- Header constant, finally five. -/
abbrev constant : Fin 640 := 619
/-- Raw zero/one original ET verdict. -/
abbrev found : Fin 640 := 632
/-- Original AB-row coordinate on success. -/
abbrev witnessA : Fin 640 := 633
/-- Original middle coordinate on success. -/
abbrev witnessB : Fin 640 := 634
/-- Original AC-column coordinate on success. -/
abbrev witnessC : Fin 640 := 635
/-- Total actual original-weight scans over all visited records. -/
abbrev scans : Fin 640 := 636

end Reg

/-- The complete solver and its compiler registers move as one bank, above the selector. -/
@[expose] def sourceBank (i : Fin 419) : Fin 640 := ⟨160 + i.val, by omega⟩

/-- An unchanged source register in the high physical bank. -/
@[expose] def sourceReg (i : Fin 416) : Fin 640 := sourceBank (i.castAdd 3)

/-- The copy/sum loop uses eight disjoint setup registers. -/
@[expose] def copyBank (i : Fin 8) : Fin 640 := ⟨620 + i.val, by omega⟩

/-- Ceiling-logarithm setup uses the first four copy temporaries. -/
@[expose] def clogBank (i : Fin 4) : Fin 640 := ⟨620 + i.val, by omega⟩

/-- Power setup uses the first five copy temporaries. -/
@[expose] def powerBank (i : Fin 5) : Fin 640 := ⟨620 + i.val, by omega⟩

open Reg in
/-- Write the actual original-input length and four raw scalar headers. -/
@[expose] def header : Code .standard 640 := ram[
  one ← #1; area ← n * n; constant ← #3; length ← area * constant;
  constant ← #4; length ← length + constant; address ← base; *address ← length;
  address ← address + one; *address ← dimension;
  address ← address + one; *address ← groups;
  address ← address + one; *address ← n;
  address ← address + one; *address ← prime; constant ← #5 ]

/-- Prepare the first original matrix and initialize its actual raw-word accumulator. -/
@[expose] def firstCopy : Code .standard 640 :=
  let src := copyBank 0
  let dst := copyBank 1
  let len := copyBank 2
  let total := copyBank 7
  ram[ src ← Reg.ab; dst ← Reg.base + Reg.constant; len ← Reg.area; total ← #0 ]

/-- Advance the destination by one copied square, retaining the actual running word sum. -/
@[expose] def nextCopy (src : Fin 640) : Code .standard 640 :=
  let source := copyBank 0
  let dst := copyBank 1
  let len := copyBank 2
  ram[ source ← src; dst ← dst + len ]

/-- Only the original matrix spans are copied. Every loaded word also contributes to the
computed source-width argument; no external magnitude/exponent certificate is read. -/
@[expose] def adapt : Code .standard 640 :=
  .seq header <| .seq firstCopy <| .seq (ArrayCopySum.program.rename copyBank) <|
    .seq (nextCopy Reg.bc) <| .seq (ArrayCopySum.program.rename copyBank) <|
      .seq (nextCopy Reg.ac) <| .seq (ArrayCopySum.program.rename copyBank)
        (.op (.copy Reg.total (copyBank 7)))

/-- Form the actual argument of the ceiling logarithm. -/
@[expose] def sizeArgument : Code .standard 640 :=
  let arg := clogBank 0
  let constant := clogBank 2
  ram[ arg ← Reg.n; arg ← arg + Reg.dimension; arg ← arg + Reg.groups;
    arg ← arg + Reg.prime; arg ← arg + Reg.total; constant ← #4; arg ← arg + constant ]

/-- Deliver the computed exponent and base to the actual power routine. -/
@[expose] def powerArguments : Code .standard 640 :=
  let logarithm := clogBank 1
  let coefficient := powerBank 2
  let exponent := powerBank 3
  ram[ coefficient ← #6166; exponent ← logarithm * coefficient; coefficient ← #2 ]

/-- Deliver the computed power and runtime base to the memory-window compiler bank. -/
@[expose] def windowArguments : Code .standard 640 :=
  let base := sourceBank MemoryWindow.Reg.base
  let modulus := sourceBank MemoryWindow.Reg.modulus
  let value := powerBank 0
  ram[ base ← Reg.base; modulus ← value ]

/-- Compute the actual source modulus and normalize the fixed source register bank.
Neither the dirty memory window nor the caller's register bank is cleared. -/
@[expose] def setup : Code .standard 640 :=
  .seq sizeArgument <| .seq (NatClog.program.rename clogBank) <|
    .seq powerArguments <| .seq (Power.program.rename powerBank) <|
      .seq windowArguments ((MemoryWindow.normalizeRegisters 416).rename sourceBank)

/-- Every original solver load/store has actual runtime address translation and normalization. -/
@[expose] def solve : Code .standard 640 :=
  (MemoryWindow.compile FixedPrime.program).rename sourceBank

/-- Return raw verdict, original coordinates and the single accumulated scan counter. -/
@[expose] def receive : Code .standard 640 :=
  let found := sourceReg FixedPrime.Reg.found
  let a := sourceReg (FixedPrime.recordBank RecordWitness.Reg.witnessA)
  let b := sourceReg (FixedPrime.recordBank RecordWitness.Reg.witnessB)
  let c := sourceReg (FixedPrime.recordBank RecordWitness.Reg.witnessC)
  let scans := sourceReg FixedPrime.Reg.scans
  ram[ Reg.found ← found; Reg.witnessA ← a; Reg.witnessB ← b;
    Reg.witnessC ← c; Reg.scans ← scans ]

/-- One uniform callable solver; all copies, setup, invocation and return instructions are real. -/
@[expose] def program : Code .standard 640 := .seq adapt (.seq setup (.seq solve receive))

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
