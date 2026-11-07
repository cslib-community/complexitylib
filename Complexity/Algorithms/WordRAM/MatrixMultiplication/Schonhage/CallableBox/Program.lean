/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Setup
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Return

/-!
# Callable routed box-product code

The actual memory-window compiler translates every access of the 160-register box
product above a caller-supplied base. Existing native setup computes a virtual modulus
from the row and occurrence counts and normalizes the source register bank. The two
extra counted instructions extend the restored-input span to include the appended
ordinary threshold word. Existing native span normalization then restores exact
physical input and answer words, without clearing the whole virtual window.

The source level is `21*m`; the threshold is original input data. This is a callable
product prerequisite for the Exact Triangle adapter, not a complete ET/3SUM solver.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct

open Cslib.WordRAM

/-- Include the appended threshold in the actual final input-normalization span. -/
@[expose] def includeThreshold : Code .standard 163 := ram[
  CallableProduct.Reg.third ← #1;
  CallableProduct.Reg.inputSize ← CallableProduct.Reg.inputSize + CallableProduct.Reg.third ]

/-- Computed setup, actual translated product, and the charged input-span adjustment. -/
@[expose] def core : Code .standard 163 :=
  .seq CallableProduct.setup <|
    .seq (MemoryWindow.compile (BoxProduct.program true)) includeThreshold

/-- The complete native callable product, including exact physical input/answer normalization. -/
@[expose] def program : Code .standard 163 :=
  .seq core (.seq CallableProduct.restoreInput CallableProduct.returnOutput)

/-- Load an ordinary runtime base word before invoking the actual callable program. -/
@[expose] def entryProgram : Code .standard 163 :=
  .seq (ram[ CallableProduct.Reg.address ← #1; CallableProduct.Reg.base ←
    *CallableProduct.Reg.address ]) program

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBoxProduct
