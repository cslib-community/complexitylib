/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Matrix.Mul

/-!
# Matrix powers on a closed set of indices

An injectively indexed submatrix preserves matrix-vector products and their iterates when rows
in the image have zero entries outside it. The ambient vector may take arbitrary values outside
the image. This is the restriction principle used to compare reachable configuration matrices
with an explicitly enumerated ambient box.

## Main results

* `Matrix.submatrix_mulVec_of_closed`: one multiplication commutes with restriction.
* `Matrix.submatrix_pow_mulVec_of_closed`: so do all matrix powers.
-/

public section

namespace Matrix

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [Semiring R]

/-- Restricting to an injectively indexed set of rows commutes with matrix-vector multiplication
if those rows have no nonzero entries outside the indexed set. -/
theorem submatrix_mulVec_of_closed (M : Matrix κ κ R) (e : ι ↪ κ)
    (hclosed : ∀ i j, j ∉ Set.range e → M (e i) j = 0) (v : κ → R) :
    M.submatrix e e *ᵥ (v ∘ e) = (M *ᵥ v) ∘ e := by
  ext i
  exact Fintype.sum_of_injective e e.injective
    (fun j => M (e i) (e j) * v (e j)) (fun j => M (e i) j * v j)
    (fun j hj => by rw [hclosed i j hj, zero_mul]) (fun _ => rfl)

/-- Every power preserves restriction to a set with no outgoing nonzero matrix entries. -/
theorem submatrix_pow_mulVec_of_closed [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ κ R) (e : ι ↪ κ)
    (hclosed : ∀ i j, j ∉ Set.range e → M (e i) j = 0) (v : κ → R) (t : ℕ) :
    M.submatrix e e ^ t *ᵥ (v ∘ e) = (M ^ t *ᵥ v) ∘ e := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [pow_succ', ← mulVec_mulVec, ih, submatrix_mulVec_of_closed M e hclosed]

end Matrix
