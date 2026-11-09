/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.LaplaceExchange

/-!
# A masked determinant as a signed product of complementary minors

The exchange argument is most convenient when a Laplace product is represented
by a masked determinant.  This file supplies the exact bridge back to a product
of two minors.  We deliberately retain the sign of the column permutation
instead of expanding it into a formula involving sums of indices: its value is
a unit over every commutative ring, which is precisely what straightening needs.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SignedLaplaceProduct.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its placement exception is recorded in `UPSTREAM.md`.
-/

public section

namespace Cslib

noncomputable section

namespace GenericMaximalMinor

open scoped BigOperators

variable {N : ℕ} {R : Type*} [CommRing R]

/-- The minor with row subtype `p` and column subtype `q`, after identifying
the two subtype index sets by `e`. -/
@[expose] def minorAlongEquiv (Y : Matrix (Fin N) (Fin N) R)
    {p q : Fin N → Prop} [DecidablePred p]
    (e : {i // p i} ≃ {j // q j}) : R :=
  Matrix.det fun (i : {i // p i}) (j : {i // p i}) ↦ Y i (e j)

/-- The order-preserving identification of two equally large subsets, obtained
by enumerating both in increasing order. -/
@[expose] def orderedFinsetEquiv (A B : Finset (Fin N)) (h : A.card = B.card) : A ≃ B :=
  (A.orderIsoOfFin rfl).symm.toEquiv.trans (B.orderIsoOfFin h.symm).toEquiv

/-- The canonical minor selected by two finite subsets.  It is zero when the
row and column cardinalities differ. -/
@[expose] def finsetMinor (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) : R :=
  if h : A.card = B.card then minorAlongEquiv Y (orderedFinsetEquiv A B h) else 0

@[simp] lemma finsetMinor_of_card_ne (Y : Matrix (Fin N) (Fin N) R)
    (A B : Finset (Fin N)) (h : A.card ≠ B.card) :
    finsetMinor Y A B = 0 := by
  simp [finsetMinor, h]

lemma minorAlongEquiv_eq_sign_mul_finsetMinor
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card = B.card) (e : A ≃ B) :
    minorAlongEquiv Y e =
      (@Equiv.Perm.sign A _ (Subtype.fintype (fun i : Fin N ↦ i ∈ A))
          (e.trans (orderedFinsetEquiv A B hcard).symm) : R) *
        finsetMinor Y A B := by
  classical
  let : Fintype A := Subtype.fintype (fun i : Fin N ↦ i ∈ A)
  let eo : A ≃ B := orderedFinsetEquiv A B hcard
  let s : Equiv.Perm A := e.trans eo.symm
  have hmatrix :
      (fun (i : A) (j : A) ↦ Y i (e j)) =
        (fun (i : A) (j : A) ↦ Y i (eo (s j))) := by
    funext i j
    simp [s, eo]
  rw [finsetMinor, dite_eq_left hcard]
  unfold minorAlongEquiv
  rw [hmatrix]
  change Matrix.det
    (Matrix.submatrix ((fun (i : A) (j : A) ↦ Y i (eo j)) : Matrix A A R) id s) = _
  exact Matrix.det_permute' s (Matrix.of (fun (i : A) (j : A) => Y i (eo j)))

lemma maskedMatrix_apply_extendSubtype_of_mem
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (e : {i // i ∈ A} ≃ {j // j ∈ B}) (i j : {i // i ∈ A}) :
    maskedMatrix Y A B i (e.extendSubtype j) = Y i (e j) := by
  rw [Equiv.extendSubtype_apply_of_mem e j j.property]
  simp [maskedMatrix, i.property, (e j).property]

lemma maskedMatrix_apply_extendSubtype_of_not_mem
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (e : {i // i ∈ A} ≃ {j // j ∈ B})
    (i j : {i // ¬i ∈ A}) :
    maskedMatrix Y A B i (e.extendSubtype j) = Y i (e.toCompl j) := by
  rw [Equiv.extendSubtype_apply_of_not_mem e j j.property]
  change
    (if ((i : Fin N) ∈ A ↔ (e.toCompl j : Fin N) ∈ B)
      then Y i (e.toCompl j) else 0) = Y i (e.toCompl j)
  rw [ite_eq_left]
  exact ⟨fun hi ↦ (i.property hi).elim, fun hj ↦ ((e.toCompl j).property hj).elim⟩

/-- Exact block-determinant form of the Laplace-product expansion.  The sign
is the sign of the permutation extending the chosen equivalence `A ≃ B`.
No ordering formula for that sign is needed later. -/
theorem sign_mul_det_maskedMatrix_eq_mul_minors
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (e : {i // i ∈ A} ≃ {j // j ∈ B}) :
    (Equiv.Perm.sign e.extendSubtype : R) * Matrix.det (maskedMatrix Y A B) =
      minorAlongEquiv Y e * minorAlongEquiv Y e.toCompl := by
  classical
  let M : Matrix (Fin N) (Fin N) R :=
    (maskedMatrix Y A B).submatrix id e.extendSubtype
  have hzero : ∀ i, i ∈ A → ∀ j, ¬j ∈ A → M i j = 0 := by
    intro i hi j hj
    simp only [M, Matrix.submatrix_apply, id_eq]
    have hnotB := Equiv.extendSubtype_not_mem e j hj
    simp [maskedMatrix, hi, hnotB]
  have hblocks := Matrix.twoBlockTriangular_det' M (fun i ↦ i ∈ A) hzero
  have hleft :
      @Matrix.det _ _ (Subtype.fintype (fun i : Fin N ↦ i ∈ A)) R _
          (Matrix.toSquareBlockProp M (fun i ↦ i ∈ A)) =
        minorAlongEquiv Y e := by
    unfold minorAlongEquiv
    refine congrArg
      (fun X : Matrix {i : Fin N // i ∈ A} {i : Fin N // i ∈ A} R ↦
        @Matrix.det _ _ (Subtype.fintype (fun i : Fin N ↦ i ∈ A)) R _ X) ?_
    funext i j
    exact maskedMatrix_apply_extendSubtype_of_mem Y A B e i j
  have hright :
      @Matrix.det _ _ (Subtype.fintype (fun i : Fin N ↦ ¬i ∈ A)) R _
          (Matrix.toSquareBlockProp M (fun i ↦ ¬i ∈ A)) =
        minorAlongEquiv Y e.toCompl := by
    unfold minorAlongEquiv
    refine congrArg
      (fun X : Matrix {i : Fin N // ¬i ∈ A} {i : Fin N // ¬i ∈ A} R ↦
        @Matrix.det _ _ (Subtype.fintype (fun i : Fin N ↦ ¬i ∈ A)) R _ X) ?_
    funext i j
    exact maskedMatrix_apply_extendSubtype_of_not_mem Y A B e i j
  have hblockprod :
      Matrix.det M = minorAlongEquiv Y e * minorAlongEquiv Y e.toCompl :=
    hblocks.trans (congrArg₂ (· * ·) hleft hright)
  calc
    (Equiv.Perm.sign e.extendSubtype : R) * Matrix.det (maskedMatrix Y A B) =
        Matrix.det M := by
      exact (Matrix.det_permute' e.extendSubtype (maskedMatrix Y A B)).symm
    _ = minorAlongEquiv Y e * minorAlongEquiv Y e.toCompl := hblockprod

/-- A cardinality-only version, choosing an equivalence between the two finite
subsets noncomputably. -/
theorem exists_sign_mul_det_maskedMatrix_eq_mul_minors
    (Y : Matrix (Fin N) (Fin N) R) (A B : Finset (Fin N))
    (hcard : A.card = B.card) :
    ∃ e : {i // i ∈ A} ≃ {j // j ∈ B},
      (Equiv.Perm.sign e.extendSubtype : R) * Matrix.det (maskedMatrix Y A B) =
        minorAlongEquiv Y e * minorAlongEquiv Y e.toCompl := by
  let e : A ≃ B := Finset.equivOfCardEq hcard
  exact ⟨e, sign_mul_det_maskedMatrix_eq_mul_minors Y A B e⟩

end GenericMaximalMinor

end

end Cslib
