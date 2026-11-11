/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Program
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput.Program
public import CslibFrontier.Computability.WordRAM.Copy

/-!
# Physical pointer entry to the callable box product

Source offsets remain in registers 0–159; base/modulus/compiler scratch remain in 160–162.
Three external physical pointers occupy 163–165, outside the normalized source bank. A disjoint
seven-register native copy bank gathers the scalar header, both raw matrices and every interleaved
query occurrence directly into the runtime-computed protected snapshot. The continuation starts at
`BoxProduct.programFromSnapshot` after the gather; `CallableBoxProduct.program` provides the
contiguous-input entry.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct

open Cslib.WordRAM

/-- Existing callable registers, without interpreting their values as external pointers. -/
@[expose] def callableBank (i : Fin 163) : Fin 173 := i.castAdd 10
/-- Original source register bank. -/
@[expose] def sourceBank (i : Fin 160) : Fin 173 := i.castAdd 13
/-- Separate native copying registers; never normalized or rebased by the source compiler. -/
@[expose] def copyBank (i : Fin 7) : Fin 173 := ⟨166 + i.val, by omega⟩

namespace Reg
/-- Absolute left raw-matrix pointer. -/
abbrev left : Fin 173 := 163
/-- Absolute right raw-matrix pointer. -/
abbrev right : Fin 173 := 164
/-- Absolute interleaved occurrence pointer. -/
abbrev queries : Fin 173 := 165
/-- Actual source-memory base. -/
abbrev base : Fin 173 := callableBank CallableProduct.Reg.base
/-- Native copy source, independent of the compiler address temporary. -/
abbrev source : Fin 173 := copyBank ArrayCopy.src
/-- Native copy destination. -/
abbrev destination : Fin 173 := copyBank ArrayCopy.dst
/-- Native copy word count. -/
abbrev length : Fin 173 := copyBank ArrayCopy.len
end Reg

/-- Gather the actual five scalar/header words before the three external arrays. -/
@[expose] def headerArguments : Code .standard 173 :=
  let snapshot := sourceBank QueriedProduct.Reg.snapshot
  let five := sourceBank QueriedProduct.Reg.five
  ram[
  Reg.source ← Reg.base;
  Reg.destination ← Reg.base + snapshot;
  Reg.length ← five ]

/-- First external matrix begins immediately after the snapshot header. -/
@[expose] def leftArguments : Code .standard 173 :=
  let five := sourceBank QueriedProduct.Reg.five
  let matrixWords := sourceBank QueriedProduct.Reg.matrixWords
  let two := sourceBank QueriedProduct.Reg.two
  ram[
  Reg.source ← Reg.left;
  Reg.destination ← Reg.destination + five;
  Reg.length ← matrixWords / two ]

/-- Second external matrix begins immediately after the first. -/
@[expose] def rightArguments : Code .standard 173 := ram[
  Reg.source ← Reg.right; Reg.destination ← Reg.destination + Reg.length ]

/-- Keep the caller's original interleaved query layout and occurrence order. -/
@[expose] def queryArguments : Code .standard 173 :=
  let queryCount := sourceBank QueriedProduct.Reg.queryCount
  let two := sourceBank QueriedProduct.Reg.two
  ram[
  Reg.source ← Reg.queries; Reg.destination ← Reg.destination + Reg.length;
  Reg.length ← queryCount * two ]

/-- All four physical copies are actual standard native code. -/
@[expose] def copy : Code .standard 173 := ArrayCopy.program.rename copyBank

/-- Gather straight into the protected snapshot, without a contiguous low payload staging pass. -/
@[expose] def gather : Code .standard 173 :=
  .seq headerArguments <| .seq copy <| .seq leftArguments <| .seq copy <|
    .seq rightArguments <| .seq copy <| .seq queryArguments copy

/-- Setup and source layout execute before the physical gather reads the computed offset. -/
@[expose] def setupLayout : Code .standard 173 :=
  .seq (CallableProduct.setup.rename callableBank)
    ((MemoryWindow.compile PointerInput.setupLayout).rename callableBank)

/-- Computed layout, physical gather and the unchanged source continuation. -/
@[expose] def core : Code .standard 173 :=
  .seq setupLayout <| .seq gather <|
    ((MemoryWindow.compile (BoxProduct.programFromSnapshot true)).rename callableBank)

/-- Complete pointer front with the existing exact physical input/answer normalization. -/
@[expose] def program : Code .standard 173 :=
  .seq core <| (Code.seq CallableBoxProduct.includeThreshold
    (.seq CallableProduct.restoreInput CallableProduct.returnOutput)).rename callableBank

/-- Four native copies plus all eleven actual argument/address instructions. -/
@[expose] def gatherTime (A Q : ℕ) : ℕ := 14 * A + 14 * Q + 62

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct
