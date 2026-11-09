/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/Defs.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Basic

/-!
# Matrix reindexing by permutations

Identities for `Matrix.reindex` when acting symmetrically on rows and columns by permutations:
composition with respect to permutation multiplication, identity action, and pointwise
characterization.

## Main results

* `Matrix.reindex_perm_mul`: `reindex (σ * τ) (σ * τ) M = reindex σ σ (reindex τ τ M)`.
* `Matrix.reindex_perm_one`: `reindex 1 1 M = M`.
* `Matrix.reindex_eq_iff`: `reindex eₘ eₙ A = M ↔ ∀ i j, M (eₘ i) (eₙ j) = A i j`.
-/

@[expose] public section

namespace Matrix

variable {m n l o α : Type*}

/-- Relabelling a square matrix by a product of permutations is relabelling twice. -/
theorem reindex_perm_mul (σ τ : Equiv.Perm m) (M : Matrix m m α) :
    Matrix.reindex (σ * τ) (σ * τ) M = Matrix.reindex σ σ (Matrix.reindex τ τ M) :=
  (DFunLike.congr_fun (Matrix.reindex_trans τ τ σ σ) M).symm

/-- Relabelling by the identity permutation does nothing. -/
theorem reindex_perm_one (M : Matrix m m α) : Matrix.reindex 1 1 M = M :=
  Matrix.reindex_refl_refl M

/-- `Matrix.reindex eₘ eₙ A = M` says that `(eₘ, eₙ)` carries `A` to `M`. -/
theorem reindex_eq_iff {eₘ : m ≃ l} {eₙ : n ≃ o} {A : Matrix m n α} {M : Matrix l o α} :
    Matrix.reindex eₘ eₙ A = M ↔ ∀ i j, M (eₘ i) (eₙ j) = A i j := by
  constructor
  · rintro rfl i j
    simp
  · intro h
    ext i j
    simpa using (h (eₘ.symm i) (eₙ.symm j)).symm

end Matrix
