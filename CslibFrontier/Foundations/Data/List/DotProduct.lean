/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Tactic.Matrix.OfLists
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Public padded list dot-product identities

Mathlib's `ListMatrix.dotProduct` is a pure public operation, despite living under the
matrix-tactic path. It sums exactly the requested number of products, with missing entries
zero-padded. These identities reuse that operation instead of defining a second list product.

## Main results

* `dotProduct_eq_sum_map_range`: the finite range formulation used by native certificates.
* `dotProduct_ofFn`: agreement with the ordinary finite-vector sum.
-/

public section

namespace Mathlib.Tactic.Matrix.ListMatrix

/-- The public recursive dot product equals the corresponding sum of padded list lookups. -/
theorem dotProduct_eq_sum_map_range {R : Type*} [Mul R] [AddCommMonoid R]
    (n : ℕ) (a b : List R) :
    dotProduct n a b = ((List.range n).map fun i => a.getD i 0 * b.getD i 0).sum := by
  rw [List.sum_map_range, dotProduct_eq]
  simp only [_root_.dotProduct, ofList_apply]

/-- Canonical finite-vector lists give the ordinary dot-product sum. -/
theorem dotProduct_ofFn {R : Type*} [Mul R] [AddCommMonoid R]
    {n : ℕ} (a b : Fin n → R) :
    dotProduct n (List.ofFn a) (List.ofFn b) = ∑ i : Fin n, a i * b i := by
  simp only [dotProduct_eq, _root_.dotProduct, ofList_apply, List.getD_ofFn]

end Mathlib.Tactic.Matrix.ListMatrix
