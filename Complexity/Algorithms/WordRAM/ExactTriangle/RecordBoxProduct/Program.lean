/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Patch
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Width

/-!
# Native prepared-record calls to the improved box product

The actual existing record decoder and three original-input copies are followed by
the threshold-aware patch and the compiled box-product call. Register renaming uses
the existing disjoint callee bank; actual memory rebasing occurs inside the callee.
The outer Exact Triangle controller is not switched to this consumer here.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open RecordProduct

/-- Real preparation retains the existing raw matrix and coordinate copies. -/
@[expose] def prepare : Code .standard 320 := .seq RecordProduct.prepare patchInput

/-- Copy the runtime base, invoke the translated product and copy its absolute result. -/
@[expose] def invoke : Code .standard 320 :=
  .seq (.op (.copy (calleeBank CallableProduct.Reg.base) Reg.base)) <|
    .seq (CallableBoxProduct.program.rename calleeBank)
      (.op (.copy Reg.result (calleeBank CallableProduct.Reg.result)))

/-- One actual selected record, including all preparation, patch and native product work. -/
@[expose] def program : Code .standard 320 := .seq prepare invoke

/-- Constant native record-consumer size and physical-width independence. -/
theorem program_fixed : program.size ≤ 131584 ∧ ¬program.ReadsWidth := by
  have hc := CallableBoxProduct.program_length_le
  simp only [CallableBoxProduct.entryProgram, Code.program, List.length_append,
    Code.length_assemble, List.length_singleton, Code.size] at hc
  have hp : RecordProduct.prepare.size ≤ 256 := by decide +kernel
  have hs : patchInput.size = 16 := by decide +kernel
  have hprep : ¬RecordProduct.prepare.ReadsWidth := by decide +kernel
  have hpatch : ¬patchInput.ReadsWidth := by decide +kernel
  have hcall : ¬CallableBoxProduct.program.ReadsWidth := by
    simpa only [CallableBoxProduct.entryProgram, Code.ReadsWidth, Op.ReadsWidth, false_or] using
      CallableBoxProduct.not_readsWidth
  constructor
  · simp only [program, prepare, invoke, Code.size, Code.size_rename]
    omega
  · simp only [program, prepare, invoke, Code.ReadsWidth, Code.readsWidth_rename,
      Op.ReadsWidth, hprep, hpatch, hcall, not_false_eq_true, or_self]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
