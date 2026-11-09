/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/Determinant/CauchyBinet.lean`)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Hom.PowersetCard
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The Cauchy–Binet formula

For a commutative ring `R`, a matrix `A` with `n` rows and a finite linearly ordered column type
`ι`, and a matrix `B` with rows `ι` and `n` columns, the determinant of the `n × n` product is the
sum, over the `n`-element subsets `s` of `ι`, of the product of the `n × n` minors of `A` and `B`
on `s`:

`det (A * B) = ∑ s, det (A.submatrix id s) * det (B.submatrix s id)`.

The subsets are the elements of `Set.powersetCard ι n`. Each subset `s` is enumerated in
increasing order by `Set.powersetCard.ofFinEmbEquiv.symm s : Fin n ↪o ι`. The sum is empty, and
so the determinant vanishes, when `ι` has fewer than `n` elements.

The proof writes `det (A * B)` as the canonical pairing `exteriorPower.pairingDual` of the
`n`-fold exterior products of the rows of `B`, viewed as linear forms, and of the rows of `A`.
It then expands the second argument in the basis `Module.Basis.exteriorPower` of the exterior
power of `ι → R`. The statement, the declaration names and this proof route are taken from
Michel Hua's (@mycaule) closed Mathlib pull request mathlib4#44757; that pull request credits the
exterior-power route to the review of mathlib4#40473 and of its own square case. The proof script
here is rewritten. Neither that pull request nor the earlier closed pull requests mathlib4#40473
and mathlib4#44209 is part of Mathlib at the pinned revision.

## Main results

* `Matrix.det_mul_eq_sum_powersetCard`: the Cauchy–Binet formula for `n × ι` and `ι × n`
  matrices.
* `Matrix.det_mul_eq_sum_powersetCard_of_equiv`: the same formula for rows indexed by any finite
  type `κ` with an enumeration `κ ≃ Fin n`.
-/

public section

open Set.powersetCard exteriorPower Module

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [LinearOrder ι] {n : ℕ}

/-- **The Cauchy–Binet formula.** The determinant of the product of an `n × ι` matrix and an
`ι × n` matrix is the sum, over the `n`-element subsets `s` of `ι`, of the products of the
`n × n` minors on the columns `s` of `A` and the rows `s` of `B`. -/
theorem det_mul_eq_sum_powersetCard (A : Matrix (Fin n) ι R) (B : Matrix ι (Fin n) R) :
    (A * B).det = ∑ s : Set.powersetCard ι n,
      (A.submatrix id (ofFinEmbEquiv.symm s)).det *
        (B.submatrix (ofFinEmbEquiv.symm s) id).det := by
  classical
  set b := Pi.basisFun R ι
  set f : Fin n → Dual R (ι → R) := fun j => ∑ k, B k j • LinearMap.proj k
  have hAB : (A * B).det =
      pairingDual R (ι → R) n (ιMulti R n f) (ιMulti R n fun i => A i) := by
    rw [pairingDual_ιMulti_ιMulti]
    congr 1
    ext i j
    simp [f, Matrix.mul_apply, mul_comm]
  rw [hAB, ← (b.exteriorPower n).sum_repr (ιMulti R n fun i => A i), map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, basis_repr_apply, ιMultiDual_apply_ιMulti, basis_apply, ιMulti_family,
    pairingDual_ιMulti_ιMulti, smul_eq_mul]
  congr 2
  ext i j
  simp [f, b, LinearMap.sum_apply, Pi.single_apply]

/-- **The Cauchy–Binet formula** for square products indexed by a finite type `κ` enumerated by
`e : κ ≃ Fin n`. The `n`-element subsets `s` of `ι` are enumerated as functions `κ → ι` by
composing `e` with the increasing enumeration of `s`. -/
theorem det_mul_eq_sum_powersetCard_of_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ Fin n) (A : Matrix κ ι R) (B : Matrix ι κ R) :
    (A * B).det = ∑ s : Set.powersetCard ι n,
      (A.submatrix id (ofFinEmbEquiv.symm s ∘ e)).det *
        (B.submatrix (ofFinEmbEquiv.symm s ∘ e) id).det := by
  have h := det_mul_eq_sum_powersetCard (A.submatrix e.symm id) (B.submatrix id e.symm)
  rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, det_submatrix_equiv_self] at h
  rw [h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← det_submatrix_equiv_self e.symm, ← det_submatrix_equiv_self e.symm
    (B.submatrix (ofFinEmbEquiv.symm s ∘ e) id)]
  simp [submatrix_submatrix, Function.comp_def]

end Matrix
