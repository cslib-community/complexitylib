/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact Kronecker product rank and flat Kronecker powers

Every matrix `A` over a field contains a nonsingular `A.rank × A.rank` submatrix
(`Matrix.exists_submatrix_det_ne_zero`). Combining that nonsingular minor witness with the
Kronecker rank upper bound (`Matrix.rank_kronecker_le`) and `Matrix.det_kronecker` upgrades
Kronecker rank submultiplicativity to an exact equality `(A ⊗ₖ B).rank = A.rank * B.rank`
(`Matrix.rank_kronecker`).

This module also defines the flat `k`-fold Kronecker power
`Matrix.kroneckerPow A k : Matrix (Fin k → m) (Fin k → n) R` indexed directly by `Fin k → m`
rather than nested binary products, proves its algebraic laws, action on product vectors and
eigenvectors (`Matrix.kroneckerPow_mulVec_prod`, `Matrix.kroneckerPow_mulVec_smul`), and deduces
`(Matrix.kroneckerPow A k).rank = A.rank ^ k` (`Matrix.rank_kroneckerPow`).

## Main definitions

* `Matrix.kroneckerPow`: the `k`-fold Kronecker power on `Fin k → m` by `Fin k → n`.

## Main results

* `Matrix.exists_submatrix_det_ne_zero`: existence of a nonsingular `A.rank × A.rank` minor.
* `Matrix.mulVec_map_eq_smul`: eigenvector/eigenvalue transfer along a ring homomorphism.
* `Matrix.rank_kronecker`: `(A ⊗ₖ B).rank = A.rank * B.rank` over any field.
* `Matrix.kroneckerPow_succ_eq_submatrix`, `Matrix.kroneckerPow_mul`,
  `Matrix.kroneckerPow_mulVec_prod`, `Matrix.kroneckerPow_mulVec_smul`,
  `Matrix.rank_kroneckerPow`: structure, action, eigenpairs, and rank of Kronecker powers.
-/

public section

namespace Matrix

open Kronecker
open scoped BigOperators

/-! ### Nonsingular `rank × rank` minors and scalar-homomorphism eigenvector transfer -/

section Minors

/-- Every finite matrix `A` over a field contains an injective `A.rank × A.rank` submatrix with
nonzero determinant. -/
theorem exists_submatrix_det_ne_zero {m n K : Type*} [Field K] [Finite m] [Fintype n]
    (A : Matrix m n K) :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n),
      Function.Injective r ∧ Function.Injective c ∧ (A.submatrix r c).det ≠ 0 := by
  classical
  cases nonempty_fintype m
  obtain ⟨κ, c, hc, hspan_c, hli_c⟩ := exists_linearIndependent' K A.col
  have : Finite κ := Finite.of_injective c hc
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcard_c : Fintype.card κ = A.rank := by
    rw [rank_eq_finrank_span_cols, ← hspan_c, finrank_span_eq_card hli_c]
  have hcol_eq : Set.range (A.submatrix id c).col = Set.range (A.col ∘ c) := by
    ext v
    simp only [Set.mem_range, Function.comp_apply]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, hi⟩⟩
  have hrank_sub : (A.submatrix id c).rank = Fintype.card κ := by
    rw [rank_eq_finrank_span_cols, hcol_eq, finrank_span_eq_card hli_c]
  obtain ⟨μ, r, hr, hspan_r, hli_r⟩ := exists_linearIndependent' K (A.submatrix id c).row
  have : Finite μ := Finite.of_injective r hr
  let _ : Fintype μ := Fintype.ofFinite μ
  have hcard_r : Fintype.card μ = Fintype.card κ := by
    rw [← hrank_sub, rank_eq_finrank_span_row, ← hspan_r, finrank_span_eq_card hli_r]
  let ec : Fin A.rank ≃ κ := (Fintype.equivFinOfCardEq hcard_c).symm
  let er : Fin A.rank ≃ μ := (Fintype.equivFinOfCardEq (hcard_r.trans hcard_c)).symm
  refine ⟨r ∘ er, c ∘ ec, hr.comp er.injective, hc.comp ec.injective, ?_⟩
  let S : Matrix (Fin A.rank) (Fin A.rank) K := A.submatrix (r ∘ er) (c ∘ ec)
  have hS_li : LinearIndependent K S.row := by
    have h1 : LinearIndependent K (((A.submatrix id c).row ∘ r) ∘ er) :=
      hli_r.comp er er.injective
    have h2 : S.row = (LinearEquiv.funCongrLeft K K ec) ∘
        (((A.submatrix id c).row ∘ r) ∘ er) := by
      ext i j
      rfl
    rw [h2]
    exact h1.map' (LinearEquiv.funCongrLeft K K ec).toLinearMap
      (LinearEquiv.ker _)
  exact IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp hS_li))

/-- Eigenvector and eigenvalue equations transfer along any ring homomorphism. -/
theorem mulVec_map_eq_smul {m R S : Type*} [Semiring R] [Semiring S] [Fintype m]
    (f : R →+* S) (A : Matrix m m R) (v : m → R) (μ : R) (h : A *ᵥ v = μ • v) :
    A.map f *ᵥ (f ∘ v) = f μ • (f ∘ v) := by
  ext i
  rw [← f.map_mulVec A v, h]
  simp [map_mul]

end Minors

/-! ### Exact rank of a Kronecker product -/

section KroneckerRank

/-- **Multiplicativity of rank under Kronecker product** over a field:
`(A ⊗ₖ B).rank = A.rank * B.rank`. -/
@[simp]
theorem rank_kronecker {l m n p K : Type*} [Field K] [Finite l] [Fintype m] [Finite n] [Fintype p]
    (A : Matrix l m K) (B : Matrix n p K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  refine le_antisymm (rank_kronecker_le A B) ?_
  obtain ⟨rA, cA, _, _, hdetA⟩ := exists_submatrix_det_ne_zero A
  obtain ⟨rB, cB, _, _, hdetB⟩ := exists_submatrix_det_ne_zero B
  let SA : Matrix (Fin A.rank) (Fin A.rank) K := A.submatrix rA cA
  let SB : Matrix (Fin B.rank) (Fin B.rank) K := B.submatrix rB cB
  have hsub : SA ⊗ₖ SB = (A ⊗ₖ B).submatrix (Prod.map rA rB) (Prod.map cA cB) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rfl
  have hdet : (SA ⊗ₖ SB).det ≠ 0 := by
    rw [det_kronecker]
    exact mul_ne_zero (pow_ne_zero _ hdetA) (pow_ne_zero _ hdetB)
  have hunit : IsUnit (SA ⊗ₖ SB) :=
    (isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ hdet)
  have hrank : (SA ⊗ₖ SB).rank = A.rank * B.rank := by
    simpa using rank_of_isUnit (SA ⊗ₖ SB) hunit
  rw [← hrank, hsub]
  exact rank_submatrix_le (A ⊗ₖ B) (Prod.map rA rB) (Prod.map cA cB)

end KroneckerRank

/-! ### Flat `k`-fold Kronecker powers -/

section KroneckerPow

/-- The `k`-fold Kronecker power of `A : Matrix m n R`, indexed directly by `Fin k → m` and
`Fin k → n`, with `(x, y)`-entry `∏ i : Fin k, A (x i) (y i)`. -/
@[expose] def kroneckerPow {m n R : Type*} [CommMonoid R] (A : Matrix m n R) (k : ℕ) :
    Matrix (Fin k → m) (Fin k → n) R :=
  of fun x y => ∏ i : Fin k, A (x i) (y i)

@[simp]
theorem kroneckerPow_apply {m n R : Type*} [CommMonoid R] (A : Matrix m n R) (k : ℕ)
    (x : Fin k → m) (y : Fin k → n) :
    kroneckerPow A k x y = ∏ i : Fin k, A (x i) (y i) :=
  rfl

/-- The `0`-th Kronecker power is the `1 × 1` identity matrix on `Fin 0 → m`. -/
@[simp]
theorem kroneckerPow_zero {m R : Type*} [CommSemiring R] [DecidableEq m] (A : Matrix m m R) :
    kroneckerPow A 0 = 1 := by
  ext x y
  have hxy : x = y := Subsingleton.elim x y
  subst hxy
  simp

/-- Reindexing `kroneckerPow A 1` along `Equiv.funUnique` recovers `A`. -/
theorem kroneckerPow_one_submatrix {m n R : Type*} [CommMonoid R] (A : Matrix m n R) :
    (kroneckerPow A 1).submatrix (Equiv.funUnique (Fin 1) m).symm
      (Equiv.funUnique (Fin 1) n).symm = A := by
  ext i j
  simp [kroneckerPow]

/-- `kroneckerPow A (k + 1)` is `A ⊗ₖ kroneckerPow A k` reindexed along `Fin.consEquiv`. -/
theorem kroneckerPow_succ_eq_submatrix {m n R : Type*} [CommSemiring R] (A : Matrix m n R)
    (k : ℕ) :
    kroneckerPow A (k + 1) =
      (A ⊗ₖ kroneckerPow A k).submatrix (Fin.consEquiv fun _ => m).symm
        (Fin.consEquiv fun _ => n).symm := by
  ext x y
  simp only [kroneckerPow_apply, submatrix_apply, kroneckerMap_apply, Fin.prod_univ_succ,
    Fin.consEquiv_symm_apply]
  rfl

/-- Kronecker power distributes over matrix multiplication. -/
theorem kroneckerPow_mul {l m n R : Type*} [CommSemiring R] [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) (k : ℕ) :
    kroneckerPow (A * B) k = kroneckerPow A k * kroneckerPow B k := by
  ext x z
  simp only [kroneckerPow_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib

/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem kroneckerPow_one_matrix {m R : Type*} [CommSemiring R] [DecidableEq m] (k : ℕ) :
    kroneckerPow (1 : Matrix m m R) k = 1 := by
  ext x y
  simp only [kroneckerPow_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Transpose commutes with `kroneckerPow`. -/
@[simp]
theorem transpose_kroneckerPow {m n R : Type*} [CommMonoid R] (A : Matrix m n R) (k : ℕ) :
    (kroneckerPow A k)ᵀ = kroneckerPow Aᵀ k :=
  rfl

/-- Mapping along a monoid homomorphism commutes with `kroneckerPow`. -/
theorem map_kroneckerPow {m n R S : Type*} [CommMonoid R] [CommMonoid S]
    (f : R →* S) (A : Matrix m n R) (k : ℕ) :
    (kroneckerPow A k).map f = kroneckerPow (A.map f) k := by
  ext x y
  simp [map_prod]

/-- `kroneckerPow A k` acts coordinatewise on product vectors `y ↦ ∏ i, v i (y i)`. -/
theorem kroneckerPow_mulVec_prod {m n R : Type*} [CommSemiring R] [Fintype n]
    (A : Matrix m n R) (k : ℕ) (v : Fin k → n → R) :
    kroneckerPow A k *ᵥ (fun y => ∏ i, v i (y i)) = fun x => ∏ i, (A *ᵥ v i) (x i) := by
  funext x
  simp only [mulVec, dotProduct, kroneckerPow_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib.symm

/-- Tensor products of eigenvectors of `A` are eigenvectors of `kroneckerPow A k` with eigenvalue
equal to the product of the individual eigenvalues. -/
theorem kroneckerPow_mulVec_smul {m R : Type*} [CommSemiring R] [Fintype m]
    (A : Matrix m m R) (k : ℕ) (v : Fin k → m → R) (μ : Fin k → R)
    (h : ∀ i, A *ᵥ v i = μ i • v i) :
    kroneckerPow A k *ᵥ (fun y => ∏ i, v i (y i)) =
      (∏ i, μ i) • (fun y => ∏ i, v i (y i)) := by
  rw [kroneckerPow_mulVec_prod]
  funext x
  simp only [h, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- **Rank of a Kronecker power** over a field: `(kroneckerPow A k).rank = A.rank ^ k`. -/
@[simp]
theorem rank_kroneckerPow {m n K : Type*} [Field K] [Finite m] [Fintype n]
    (A : Matrix m n K) (k : ℕ) :
    (kroneckerPow A k).rank = A.rank ^ k := by
  cases nonempty_fintype m
  induction k with
  | zero =>
      let B : Matrix (Fin 0 → m) (Fin 0 → n) K := kroneckerPow A 0
      have hli : LinearIndependent K B.row := by
        refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
        have hi : i = default := Subsingleton.elim i default
        subst hi
        have h0 := congrFun hg default
        simpa [B, kroneckerPow] using h0
      simpa [B] using hli.rank_matrix
  | succ k ih =>
      rw [kroneckerPow_succ_eq_submatrix, rank_submatrix, rank_kronecker, ih, pow_succ']

end KroneckerPow

end Matrix
