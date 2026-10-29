/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.ThinWidth
public import Complexity.Algorithms.WordRAM.NatClog
public import Complexity.Computability.WordRAM.MemoryWindow
public import Complexity.Computability.WordRAM.ArrayNormalize
public import Complexity.Computability.WordRAM.Power

/-!
# Callable queried-product code

The source product is unchanged. Its translated memory accesses use a runtime base in register
160 and a source-word modulus computed from the original row and query counts. The 160 source
registers occupy the low bank; registers 161 and 162 are the modulus and address temporary.

Raw zero/one entries are still doubled by the original charged matrix-input loop. Setup and
final normalization touch only the original input and answer spans, never the whole reserved
window or caller catalogue. The code definitions here are internal implementation APIs.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM

namespace Reg

/-- Absolute result pointer returned to the caller. Also a setup argument register. -/
abbrev result : Fin 163 := 0
/-- Setup argument register. -/
abbrev second : Fin 163 := 1
/-- Setup constant or normalization modulus. -/
abbrev third : Fin 163 := 2
/-- Power exponent during setup. -/
abbrev fourth : Fin 163 := 3
/-- Runtime source-memory base supplied by the caller. -/
abbrev base : Fin 163 := 160
/-- Computed source-word modulus, preserved across the translated product. -/
abbrev modulus : Fin 163 := 161
/-- Temporary absolute address. -/
abbrev address : Fin 163 := 162
/-- Source register retaining the original input span length. -/
abbrev inputSize : Fin 163 := QueriedProduct.inputSize.castAdd 3
/-- Source register retaining the relative answer pointer. -/
abbrev output : Fin 163 := QueriedProduct.output.castAdd 3
/-- Source register retaining the query occurrence count. -/
abbrev queryCount : Fin 163 := QueriedProduct.queryCount.castAdd 3

end Reg

/-- The logarithm routine uses four low scratch registers. -/
@[expose] def clogBank (i : Fin 4) : Fin 163 := i.castAdd 159
/-- The power routine uses five low scratch registers. -/
@[expose] def powerBank (i : Fin 5) : Fin 163 := i.castAdd 158
/-- Array normalization uses seven low scratch registers. -/
@[expose] def normalizeBank (i : Fin 7) : Fin 163 := i.castAdd 156

/-- Read the actual row and occurrence-count headers, and form `N+Q+3`. -/
@[expose] def readSize : Code .standard 163 := ram[
  Reg.result ← #3; Reg.address ← Reg.base + Reg.result; Reg.result ← *Reg.address;
  Reg.second ← #4; Reg.address ← Reg.base + Reg.second; Reg.second ← *Reg.address;
  Reg.result ← Reg.result + Reg.second; Reg.second ← #3;
  Reg.result ← Reg.result + Reg.second ]

/-- Compute `2^(128*clog₂(N+Q+3))` with the existing logarithm and power programs. -/
@[expose] def setup : Code .standard 163 :=
  .seq readSize <| .seq (NatClog.program.rename clogBank) <|
    .seq (ram[ Reg.third ← #128; Reg.fourth ← Reg.second * Reg.third; Reg.third ← #2 ]) <|
      .seq (Power.program.rename powerBank) <|
        .seq (.op (.copy Reg.modulus Reg.result)) (MemoryWindow.normalizeRegisters 160)

/-- Normalize the restored local input, so its actual physical words equal their source words. -/
@[expose] def restoreInput : Code .standard 163 :=
  .seq (ram[ Reg.result ← Reg.base; Reg.second ← Reg.inputSize;
    Reg.third ← Reg.modulus ]) (ArrayNormalize.program.rename normalizeBank)

/-- Normalize the exact output span and return its absolute address. -/
@[expose] def returnOutput : Code .standard 163 :=
  .seq (ram[ Reg.result ← Reg.base + Reg.output;
    Reg.second ← Reg.queryCount; Reg.third ← Reg.modulus ])
      (ArrayNormalize.program.rename normalizeBank)

/-- One fixed native raw-input product callable above an arbitrary caller-supplied base.
Every memory translation, source instruction and normalization is part of this code. -/
@[expose] def program : Code .standard 163 :=
  .seq (.seq setup (MemoryWindow.compile (QueriedProduct.program true)))
    (.seq restoreInput returnOutput)

/-- Internal execution prefix through setup and the actual translated product. -/
@[expose] def core : Code .standard 163 :=
  .seq setup (MemoryWindow.compile (QueriedProduct.program true))

/-- The derived source width is independent of the physical machine width. -/
@[expose] def sourceWidth (N Q : ℕ) : ℕ := 128 * Nat.clog 2 (N + Q + 3)

/-- Polynomially bounded virtual address-space reservation; no bulk initialization is implied. -/
@[expose] def windowSize (N Q : ℕ) : ℕ := 2 ^ sourceWidth N Q

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
