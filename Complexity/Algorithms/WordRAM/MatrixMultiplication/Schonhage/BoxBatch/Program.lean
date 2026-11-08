/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Kernel

/-!
# Native batches of sparse queries against one retained tile

Three registers unused by the sparse query retain the next wanted-code address, its
exclusive end, and the next answer address. Each iteration loads one ordinary code,
runs the actual sparse kernel, and stores its signed answer. Order and duplicates are
preserved. Geometry and retained values are prepared outside this loop.

This controller is original; it reuses the existing finite box-query semantics and
native kernel without assuming a trace, enumeration or time law from another machine.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM

/-- The same fixed register bank as the actual table and query kernels. -/
abbrev registers : ℕ := BoxQuery.registers

namespace Reg

/-- Address of the next wanted output code. -/
abbrev next : Fin registers := 43
/-- Exclusive end of the original wanted-code array. -/
abbrev stop : Fin registers := 44
/-- Address of the next signed result. -/
abbrev output : Fin registers := 45

end Reg

/-- Load exactly one original wanted code. -/
@[expose] def loadQuery : Code .standard registers := ram[
  BoxQuery.Reg.query ← *Reg.next ]

/-- Store one actual signed result and advance both physical cursors. -/
@[expose] def finishQuery : Code .standard registers := ram[
  *Reg.output ← BoxQuery.Reg.answer;
  Reg.next ← Reg.next + BoxTable.Reg.one;
  Reg.output ← Reg.output + BoxTable.Reg.one ]

/-- One wanted query, with no repeated preparation. -/
@[expose] def body : Code .standard registers :=
  .seq loadQuery (.seq BoxQuery.queryProgram finishQuery)

/-- Reuse one real table for every wanted code in its original order. -/
@[expose] def queryProgram : Code .standard registers :=
  .loop (.lt Reg.next Reg.stop) body

/-- Every query preserves the batch cursors until the explicit finish instructions. -/
theorem query_preserves :
    BoxQuery.queryProgram.Preserves Reg.next ∧
      BoxQuery.queryProgram.Preserves Reg.stop ∧
      BoxQuery.queryProgram.Preserves Reg.output := by decide

/-- The reusable batch has a fixed code size, independently of the batch length. -/
theorem queryProgram_size_le : queryProgram.size + 1 ≤ 2048 := by decide

/-- Neither the batch loop nor its sparse query kernel reads physical width. -/
theorem not_readsWidth : ¬queryProgram.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
