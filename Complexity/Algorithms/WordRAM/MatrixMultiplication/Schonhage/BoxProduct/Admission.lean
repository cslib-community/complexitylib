/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Layout
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Admission

/-!
# Original scalar and magnitude admission for routed box products

The same original allocation envelope covers the existing router/producer/copy routines.
The original matrix-entry magnitude covers both their signed arithmetic and the new
box-table and sparse-query arithmetic on actual shared band encodings.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM

/-- The old router, producer and reconstruction use a smaller original scalar envelope. -/
theorem old_fits {W L m t N Q : ℕ} (h : Fits W (wordBudget L m t N Q)) :
    Fits W (QueriedProduct.wordBudget L m N Q) :=
  h.of_le (by unfold wordBudget; omega)

/-- Every old signed producer admission follows from the common original-entry envelope. -/
theorem old_magnitude {w L A : ℕ} (h : magnitudeBound L A < 2 ^ (w - 1)) :
    QueriedProduct.magnitudeBound L A < 2 ^ (w - 1) := by
  unfold magnitudeBound at h
  omega

/-- Original matrix entries admit the new sparse-query envelope for both shared encodings. -/
theorem box_magnitude {w L A : ℕ} (hw : 0 < w)
    (h : magnitudeBound L A < 2 ^ (w - 1)) :
    GenericRAM.Signed.Fits w
      (BoxQuery.magnitudeBound L (encodedBound L A) (encodedBound L A) : ℕ) := by
  have hb : BoxQuery.magnitudeBound L (encodedBound L A) (encodedBound L A) <
      2 ^ (w - 1) := by unfold magnitudeBound at h; omega
  refine ⟨hw, ?_, by exact_mod_cast hb⟩
  have hnonneg : 0 ≤
      (BoxQuery.magnitudeBound L (encodedBound L A) (encodedBound L A) : ℤ) := by positivity
  have hpow : 0 ≤ (2 : ℤ) ^ (w - 1) := by positivity
  omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
