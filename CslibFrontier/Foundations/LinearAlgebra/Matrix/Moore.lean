/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.FieldTheory.Finite.LinearizedPolynomial
public import CslibFrontier.Foundations.LinearAlgebra.CubeSum
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic

/-!
# Moore determinants in characteristic two

The *Moore matrix* of `u : Fin k → F` is `(u l ^ 2 ^ m)_{l, m}`; its determinant is the Moore
determinant of `u` over `𝔽₂`. In characteristic two determinants and permanents agree.

The Moore determinant is the `k`-th finite difference of `x ↦ x ^ (2 ^ k - 1)`: since
`x ^ (2 ^ k - 1) = ∏_{m < k} x ^ 2 ^ m` is a product of `k` additive functions,
`∑_{c ∈ 𝔽₂ᵏ} (a + ∑ cₗ uₗ) ^ (2 ^ k - 1) = det (u l ^ 2 ^ m)` for every base point `a`.

For a linearized function `Q x = ∑_{j ∈ ℤ/n} a j * x ^ 2 ^ j` on a field with `2 ^ n` elements,
the Moore permanent of `Q ∘ w` expands in the monomials `∏ₗ wₗ ^ 2 ^ τₗ`, `τ : Fin k → ℤ/n`,
with coefficient the permanent of `(a (τ l - m) ^ 2 ^ m)_{l, m}`
[BenSassonKopparty2012, Lemma 3.13].

## Main definitions

* `Cslib.mooreMatrix`: the matrix `(u l ^ 2 ^ m)`.

## Main results

* `Matrix.det_eq_permanent_of_charTwo`: determinant and permanent agree in characteristic two.
* `Cslib.sum_cube_pow_eq_det_mooreMatrix`: the Moore determinant as a finite difference.
* `Cslib.permanent_mooreMatrix_linearizedEval`: the monomial expansion of the Moore permanent of a
  composition with a linearized function.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib

open Module

variable {F : Type*} [Field F]

/-- The Moore matrix `(u l ^ 2 ^ m)_{l, m}` of a family `u : Fin k → F`. -/
def mooreMatrix {k : ℕ} (u : Fin k → F) : Matrix (Fin k) (Fin k) F :=
  Matrix.of fun l m => u l ^ 2 ^ (m : ℕ)

/-- Entry `(l, m)` of the Moore matrix is `u l ^ 2 ^ m`. -/
@[simp]
theorem mooreMatrix_apply {k : ℕ} (u : Fin k → F) (l m : Fin k) :
    mooreMatrix u l m = u l ^ 2 ^ (m : ℕ) :=
  rfl

/-- In characteristic two the determinant of a matrix is its permanent. -/
theorem _root_.Matrix.det_eq_permanent_of_charTwo {R ι : Type*} [CommRing R] [CharP R 2]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) : M.det = M.permanent := by
  rw [Matrix.det_apply, Matrix.permanent]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, CharTwo.neg_eq]

/-- `x ^ (2 ^ k - 1)` is the product of the `k` additive powers `x ^ 2 ^ m`, `m < k`. -/
theorem pow_two_pow_sub_one_eq_prod {R : Type*} [CommMonoid R] (x : R) (k : ℕ) :
    x ^ (2 ^ k - 1) = ∏ m : Fin k, x ^ 2 ^ (m : ℕ) := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun m => 2 ^ m) k,
    Nat.geomSum_eq le_rfl]
  simp

variable [Algebra (ZMod 2) F]

/-- **The Moore determinant is a finite difference**: for every base point `a`,
`∑_{c ∈ 𝔽₂ᵏ} (a + ∑ cₗ uₗ) ^ (2 ^ k - 1)` is the Moore determinant of `u`. -/
theorem sum_cube_pow_eq_det_mooreMatrix {k : ℕ} (a : F) (u : Fin k → F) :
    ∑ c : Fin k → ZMod 2, (a + ∑ l, c l • u l) ^ (2 ^ k - 1) = (mooreMatrix u).det := by
  have hfrob : ∀ (c : Fin k → ZMod 2) (m : Fin k), (a + ∑ l, c l • u l) ^ 2 ^ (m : ℕ) =
      a ^ 2 ^ (m : ℕ) + ∑ l, c l • (u l ^ 2 ^ (m : ℕ)) := fun c m => by
    rw [add_pow_char_pow, sum_pow_char_pow]
    simp_rw [smul_pow, ZMod.pow_card_pow]
  simp_rw [pow_two_pow_sub_one_eq_prod, hfrob]
  rw [sum_cube_prod_affine_eq_permanent, Matrix.det_eq_permanent_of_charTwo,
    ← Matrix.permanent_transpose]
  rfl

/-- **Monomial expansion of a Moore permanent**, an analogue of [BenSassonKopparty2012,
Lemma 3.13]: for the
linearized function `Q = linearizedEval a` on a field with `2 ^ n` elements,
`per (Q (w l) ^ 2 ^ m) = ∑_τ per (a (τ l - m) ^ 2 ^ m) * ∏ₗ w l ^ 2 ^ τ l`, the sum ranging over
all `τ : Fin k → ZMod n`. -/
theorem permanent_mooreMatrix_linearizedEval [Finite F] {n : ℕ} [NeZero n]
    (hn : finrank (ZMod 2) F = n) (a : ZMod n → F) {k : ℕ} (w : Fin k → F) :
    (mooreMatrix fun l => linearizedEval a (w l)).permanent =
      ∑ τ : Fin k → ZMod n,
        (Matrix.of fun l m : Fin k => a (τ l - (m : ℕ)) ^ 2 ^ (m : ℕ)).permanent *
          ∏ l, w l ^ 2 ^ (τ l).val := by
  classical
  simp only [Matrix.permanent, mooreMatrix_apply]
  simp_rw [linearizedEval_pow_two_pow hn, linearizedEval, Fintype.prod_sum]
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (ZMod n)))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm,
    Finset.prod_mul_distrib, Matrix.of_apply, id]
  congr 1
  exact Equiv.prod_comp σ fun l => w l ^ 2 ^ (τ l).val

end Cslib
