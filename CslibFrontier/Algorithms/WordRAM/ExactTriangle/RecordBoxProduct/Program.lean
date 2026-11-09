/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.PointerPrepare
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Width
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Exec

/-!
# Native prepared-record calls to the pointer-gather box product

`prepare` decodes the selected record and writes the five scalar header words and box threshold.
`invoke` delivers physical pointers to `PointerBoxProduct.program`, which gathers the external raw
matrices and interleaved query occurrences directly into the computed protected snapshot; source
offsets and physical pointers occupy distinct banks within the 320-register budget.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open RecordProduct

/-- Source bank plus separate physical-pointer/copy registers fit the existing outer budget. -/
@[expose] def pointerBank (i : Fin 173) : Fin 320 := ⟨128 + i.val, by omega⟩

/-- Deliver physical pointers once, invoke the gather front and copy its absolute result. -/
@[expose] def invoke : Code .standard 320 :=
  .seq (ram[
    ⟪Code.op (.copy (pointerBank PointerBoxProduct.Reg.base) Reg.base)⟫;
    ⟪Code.op (.copy (pointerBank PointerBoxProduct.Reg.left) Reg.left)⟫;
    ⟪Code.op (.copy (pointerBank PointerBoxProduct.Reg.right) Reg.right)⟫;
    ⟪Code.op (.copy (pointerBank PointerBoxProduct.Reg.queries) Reg.queries)⟫ ])
    (.seq (PointerBoxProduct.program.rename pointerBank)
      (.op (.copy Reg.result (pointerBank
        (PointerBoxProduct.callableBank CallableProduct.Reg.result)))))

/-- One actual selected record, including all preparation, patch and native product work. -/
@[expose] def program : Code .standard 320 := .seq prepare invoke

-- Traverse the fixed source compiler and relocated native copy banks.
set_option maxRecDepth 4096 in
/-- Constant native record-consumer size and physical-width independence. -/
theorem program_fixed : program.size ≤ 131584 ∧ ¬program.ReadsWidth := by decide

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
