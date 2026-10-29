/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Memory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Bounds

/-!
# Protected buffers for native queried products

## Main definitions

* `QueriedProduct.inputEnd`: four original headers, both matrices and all coordinate pairs.
* `QueriedProduct.snapshotBase`: protected original input above both producers' work areas.
* `QueriedProduct.offsetBase`, `QueriedProduct.codeBase`, `QueriedProduct.originalBase`:
  protected copies of the actual computed routing arrays.
* `QueriedProduct.outputBase`: answers in original request order.
* `QueriedProduct.scratchBase`: reusable pruned-kernel workspace after every protected array.

These numeric specifications describe the addresses computed by the native header.
Neither a layout nor an execution/cost certificate is supplied to the program.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- One past the original initialized input, including the native length word. -/
@[expose] public def inputEnd (m N Q : ℕ) : ℕ := 5 + 2 * (N * D m) + 2 * Q

/-- Original coordinate pairs follow both row-major input matrices. -/
@[expose] public def queryInputBase (m N : ℕ) : ℕ := 5 + 2 * (N * D m)

/-- The sum reserves disjoint space above the input and both low producer allocations.
Using a sum permits direct arithmetic without a hidden maximum/layout operation. -/
@[expose] public def snapshotBase (L m N Q : ℕ) : ℕ :=
  BandPreparation.memoryEnd L m N + Wanted.memoryLimit L m N Q + inputEnd m N Q

/-- Actual prefix offsets are saved here before the band producer reuses low memory. -/
@[expose] public def offsetBase (L m N Q : ℕ) : ℕ :=
  snapshotBase L m N Q + inputEnd m N Q

/-- The grouped numerical codes follow all offsets, including their terminal word. -/
@[expose] public def codeBase (L m N Q : ℕ) : ℕ :=
  offsetBase L m N Q + numBands L m N ^ 2 + 1

/-- The actual original-index permutation follows the grouped codes. -/
@[expose] public def originalBase (L m N Q : ℕ) : ℕ := codeBase L m N Q + Q

/-- Kernel reporting writes answers in grouped order into this separate array. -/
@[expose] public def groupedBase (L m N Q : ℕ) : ℕ := originalBase L m N Q + Q

/-- Reconstructed answers in original list order; repeated requests have separate cells. -/
@[expose] public def outputBase (L m N Q : ℕ) : ℕ := groupedBase L m N Q + Q

/-- Every source, saved routing array and answer block precedes reusable kernel scratch. -/
@[expose] public def scratchBase (L m N Q : ℕ) : ℕ := outputBase L m N Q + Q

/-- The shared timestamp directory follows the kernel's actual frames and depth rows. -/
@[expose] public def stampBase (L m N Q : ℕ) : ℕ :=
  scratchBase L m N Q + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L

/-- One past the explicit whole-program allocation. -/
@[expose] public def memoryEnd (L m N Q : ℕ) : ℕ := stampBase L m N Q + 10 ^ L

/-- Every tile call increases its actual returned epoch by at most this total envelope. -/
@[expose] public def epochBound (L m N : ℕ) : ℕ :=
  numBands L m N ^ 2 * (1 + PrunedQuery.epochAllowance L)

/-- Ordinary scalar bound covering all producer, caller and kernel address arithmetic.
Signed arithmetic has its separate original-entry magnitude envelope. -/
@[expose] public def wordBudget (L m N Q : ℕ) : ℕ :=
  1024 * (BandPreparation.wordBudget L m N + Wanted.wordBudget L m N Q +
    PrunedQuery.kernelBudget L (scratchBase L m N Q) (BandPreparation.memoryEnd L m N)
      (BandPreparation.memoryEnd L m N) (codeBase L m N Q) (outputBase L m N Q) Q
      (epochBound L m N) + memoryEnd L m N Q + inputEnd m N Q + L + N + Q + 16)

/-- The source's magnitude bounds on shared encodings derive the kernel's operand bounds. -/
@[expose] public def magnitudeBound (L A : ℕ) : ℕ :=
  PrunedQuery.magnitudeBound L (7 ^ L * A) (7 ^ L * A) + A

/-- Both low producer work areas and the complete original input precede its snapshot. -/
public theorem producers_le_snapshot (L m N Q : ℕ) :
    BandPreparation.memoryEnd L m N ≤ snapshotBase L m N Q ∧
      Wanted.memoryLimit L m N Q ≤ snapshotBase L m N Q ∧
      inputEnd m N Q ≤ snapshotBase L m N Q := by
  unfold snapshotBase
  omega

/-- The high buffers are adjacent and ordered, including zero-length answer arrays. -/
public theorem buffer_order (L m N Q : ℕ) :
    snapshotBase L m N Q + inputEnd m N Q = offsetBase L m N Q ∧
      offsetBase L m N Q + numBands L m N ^ 2 + 1 = codeBase L m N Q ∧
      codeBase L m N Q + Q = originalBase L m N Q ∧
      originalBase L m N Q + Q = groupedBase L m N Q ∧
      groupedBase L m N Q + Q = outputBase L m N Q ∧
      outputBase L m N Q + Q = scratchBase L m N Q := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Real original query addresses lie strictly inside the original input prefix. -/
public theorem query_address_lt {m N Q i s : ℕ} (hi : i < Q) (hs : s < 2) :
    queryInputBase m N + 2 * i + s < inputEnd m N Q := by
  unfold queryInputBase inputEnd
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
