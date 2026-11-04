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

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
