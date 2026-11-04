/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Catalogue
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Routing
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Reconstruct

/-!
# Allocation and original-input bounds for routed box products

Existing native routing, shared band encodings and original-order answer buffers are
reused unchanged. One box directory and compact catalogue follow that caller's allocation.
The retained values and sparse work stack are reused by all tiles; a temporary answer
array follows the stack. Actual native copies deliver each tile's answers to the protected
grouped buffer before the next tile overwrites the retained values.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- First shared box-directory word, above every existing producer/caller buffer. -/
@[expose] def directoryBase (L m N Q : ℕ) : ℕ := QueriedProduct.memoryEnd L m N Q

/-- Compact geometry follows all shared directory slots. -/
@[expose] def recordBase (L m t N Q : ℕ) : ℕ :=
  directoryBase L m N Q + (m - t + 1) * 10 ^ L

/-- Each tile's retained signed values follow the compact three-word geometry. -/
@[expose] def valueBase (L m t N Q : ℕ) : ℕ :=
  recordBase L m t N Q + 3 * (boxes L m t).card

/-- Reusable sparse-query stack, beyond all retained values. -/
@[expose] def stackBase (L m t N Q : ℕ) : ℕ :=
  valueBase L m t N Q + (boxes L m t).card

/-- Reusable temporary answers, copied into the actual grouped span after each tile. -/
@[expose] def resultBase (L m t N Q : ℕ) : ℕ :=
  stackBase L m t N Q + 5 * BoxQuery.stackCapacity L

/-- One past every possible write, including the largest temporary answer span. -/
@[expose] def memoryEnd (L m t N Q : ℕ) : ℕ := resultBase L m t N Q + Q

/-- Original matrix entries bound all shared encoding operands. -/
@[expose] def encodedBound (L A : ℕ) : ℕ := 7 ^ L * A

/-- One original-entry magnitude envelope covers both the existing producer and sparse boxes. -/
@[expose] def magnitudeBound (L A : ℕ) : ℕ :=
  QueriedProduct.magnitudeBound L A +
    BoxQuery.magnitudeBound L (encodedBound L A) (encodedBound L A)

/-- Original scalar/allocation envelope; no intermediate-state fit certificate is an input. -/
@[expose] def wordBudget (L m t N Q : ℕ) : ℕ :=
  10000 * (QueriedProduct.wordBudget L m N Q + memoryEnd L m t N Q +
    directoryBase L m N Q + recordBase L m t N Q + valueBase L m t N Q +
    (m - t + 1) * 10 ^ L + (L + 1) * 10 ^ L + L + m + t + N + Q + 64)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
