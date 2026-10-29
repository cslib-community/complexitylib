/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationAdjacency
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Width
public import Complexity.Algorithms.WordRAM.NatLog
public import Complexity.Computability.WordRAM.Copy

/-!
# Calling a queried product from an actual prepared record

The low 64 producer registers are retained. Register 64 selects an actual record ordinal;
the native code computes its stride, reads its six words and places the original raw matrices
and interleaved query coordinates at the actual producer heap end. The complete callable
product occupies a separate 163-register bank. Its existing matrix-input code, not this adapter,
performs raw-zero/one to canonical-signed doubling.

The logarithm is computed by `NatLog.program`. Under `D=4^m`, dividing its binary result by two
recovers `m` exactly. No layout, logarithm, execution or solver certificate is a runtime input.
These definitions are internal stages of the complete record consumer.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

namespace Reg

/-- Actual record ordinal supplied by the outer caller. -/
abbrev ordinal : Fin 320 := 64
/-- Absolute result pointer. -/
abbrev result : Fin 320 := 65
/-- Actual producer heap end, and the callee's local-memory base. -/
abbrev base : Fin 320 := 66
/-- Original padded middle dimension. -/
abbrev dimension : Fin 320 := 67
/-- Original outer dimension. -/
abbrev size : Fin 320 := 68
/-- Computed selected record pointer. -/
abbrev record : Fin 320 := 69
/-- Loaded residue and piece metadata, retained without reinterpreting them. -/
abbrev rho : Fin 320 := 70
/-- Loaded piece index. -/
abbrev piece : Fin 320 := 71
/-- Loaded interleaved query pointer. -/
abbrev queries : Fin 320 := 72
/-- Loaded number of query occurrences. -/
abbrev count : Fin 320 := 73
/-- Loaded left-matrix pointer. -/
abbrev left : Fin 320 := 74
/-- Loaded right-matrix pointer. -/
abbrev right : Fin 320 := 75
/-- Computed size of either matrix block. -/
abbrev area : Fin 320 := 76
/-- Computed combined matrix-block length. -/
abbrev twiceArea : Fin 320 := 77
/-- Recovered inner depth. -/
abbrev depth : Fin 320 := 78
/-- Computed tensor level, nineteen times the inner depth. -/
abbrev level : Fin 320 := 79
/-- Computed original callee payload length. -/
abbrev payloadLength : Fin 320 := 80
/-- Constant one. -/
abbrev one : Fin 320 := 81
/-- Constant two. -/
abbrev two : Fin 320 := 82
/-- Record header length. -/
abbrev six : Fin 320 := 83
/-- Tensor-level multiplier. -/
abbrev nineteen : Fin 320 := 84
/-- Original callee scalar header length. -/
abbrev four : Fin 320 := 85
/-- Adapter address scratch. -/
abbrev address : Fin 320 := 86
/-- Temporary source pointer, also the logarithm input. -/
abbrev source : Fin 320 := 96
/-- Temporary destination pointer, also the logarithm result. -/
abbrev destination : Fin 320 := 97
/-- Temporary copy length. -/
abbrev length : Fin 320 := 98

end Reg

/-- The logarithm and copy routines share an adapter-local temporary register bank. -/
@[expose] def logBank (i : Fin 4) : Fin 320 := ⟨96 + i.val, by omega⟩
/-- All seven registers of the real array-copy routine are relocated together. -/
@[expose] def copyBank (i : Fin 7) : Fin 320 := ⟨96 + i.val, by omega⟩
/-- The complete callable product bank is disjoint from producer and adapter registers. -/
@[expose] def calleeBank (i : Fin 163) : Fin 320 := ⟨128 + i.val, by omega⟩

/-- Compute the record pointer and read every actual descriptor field. -/
@[expose] def readRecord : Code .standard 320 :=
  let output : Fin 320 := 39
  let heap : Fin 320 := 42
  ram[ Reg.one ← #1; Reg.two ← #2; Reg.six ← #6; Reg.nineteen ← #19; Reg.four ← #4;
    Reg.address ← #1; Reg.dimension ← *Reg.address;
    Reg.address ← #3; Reg.size ← *Reg.address;
    Reg.area ← Reg.size * Reg.dimension; Reg.twiceArea ← Reg.area + Reg.area;
    Reg.address ← Reg.twiceArea + Reg.six; Reg.address ← Reg.ordinal * Reg.address;
    Reg.record ← output + Reg.address; Reg.base ← heap;
    Reg.address ← Reg.record; Reg.rho ← *Reg.address;
    Reg.address ← Reg.address + Reg.one; Reg.piece ← *Reg.address;
    Reg.address ← Reg.address + Reg.one; Reg.queries ← *Reg.address;
    Reg.address ← Reg.address + Reg.one; Reg.count ← *Reg.address;
    Reg.address ← Reg.address + Reg.one; Reg.left ← *Reg.address;
    Reg.address ← Reg.address + Reg.one; Reg.right ← *Reg.address;
    Reg.source ← Reg.dimension ]

/-- Recover the exact power-of-four exponent with the existing charged binary logarithm. -/
@[expose] def logarithm : Code .standard 320 := NatLog.program.rename logBank

/-- Write the complete original local input header, including its length word. -/
@[expose] def writeHeader : Code .standard 320 := ram[
  Reg.depth ← Reg.destination / Reg.two;
  Reg.level ← Reg.depth * Reg.nineteen;
  Reg.payloadLength ← Reg.twiceArea + Reg.count;
  Reg.payloadLength ← Reg.payloadLength + Reg.count;
  Reg.payloadLength ← Reg.payloadLength + Reg.four;
  Reg.address ← Reg.base; *Reg.address ← Reg.payloadLength;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.level;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.depth;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.size;
  Reg.address ← Reg.address + Reg.one; *Reg.address ← Reg.count ]

/-- Deliver real source and destination pointers for the left-matrix copy. -/
@[expose] def deliverLeft : Code .standard 320 := ram[
  Reg.source ← Reg.left; Reg.address ← #5;
  Reg.destination ← Reg.base + Reg.address; Reg.length ← Reg.area ]

/-- The right block follows the left destination block. -/
@[expose] def deliverRight : Code .standard 320 := ram[
  Reg.source ← Reg.right; Reg.destination ← Reg.destination + Reg.area ]

/-- Preserve each query occurrence's two original raw coordinates, in its original order. -/
@[expose] def deliverQueries : Code .standard 320 := ram[
  Reg.source ← Reg.queries; Reg.destination ← Reg.destination + Reg.area;
  Reg.length ← Reg.count + Reg.count ]

/-- Real copying, with every address calculation, load/store and loop instruction charged. -/
@[expose] def copy : Code .standard 320 := ArrayCopy.program.rename copyBank

/-- Three actual copies; no catalogue or virtual-window snapshot is made. -/
@[expose] def copyInputs : Code .standard 320 :=
  .seq deliverLeft <| .seq copy <| .seq deliverRight <| .seq copy <|
    .seq deliverQueries copy

/-- Runtime memory rebasing is provided by the callee; renaming moves only its registers. -/
@[expose] def invoke : Code .standard 320 :=
  .seq (.op (.copy (calleeBank CallableProduct.Reg.base) Reg.base)) <|
    .seq (CallableProduct.program.rename calleeBank)
      (.op (.copy Reg.result (calleeBank CallableProduct.Reg.result)))

/-- Runtime preparation prefix, useful for admitted decoder/copy tests without the full solver. -/
@[expose] def prepare : Code .standard 320 :=
  .seq readRecord <| .seq logarithm <| .seq writeHeader copyInputs

/-- One selected actual producer record, including all copying and the complete native callee. -/
@[expose] def program : Code .standard 320 := .seq prepare invoke

-- The closed syntactic traversal includes the complete existing large callee.
set_option maxRecDepth 4096 in
/-- One fixed finite native program, independent of dimensions, record ordinal and word width. -/
theorem program_fixed : program.size ≤ 131584 ∧ ¬program.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
