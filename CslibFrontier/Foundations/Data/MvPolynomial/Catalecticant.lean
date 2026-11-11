/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, normalized coefficient matrices of polynomials)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Data.Matrix.Mul

/-!
# Normalized coefficient matrices

The entry indexed by exponent vectors `r` and `c` is the coefficient of `r + c`, divided by
its multinomial coefficient. Over a characteristic-zero field, when all queried exponents have
degree `d`, a `d`-th power of a linear form gives an outer product. Row and column families may be
arbitrary restrictions of the homogeneous exponent layers; no enumeration of all monomials is
required.

## Main definitions

* `MvPolynomial.catalecticant`: the normalized coefficient matrix, linear in the polynomial.

## Main results

* `MvPolynomial.catalecticant_linearCombination_pow`: linear-form powers give outer products
  over a characteristic-zero field.

## References

* The coefficient argument is adapted from LowerBound/Fusion/SumOfTerms/Waring.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
* [J. M. Landsberg and Z. Teitler, *On the ranks and border ranks of symmetric
  tensors*][LandsbergTeitler2009], equation (1) and Remark 6.5, describe the catalecticant bound.
-/

@[expose] public section

/-- Multinomial coefficients remain nonzero in characteristic zero. -/
theorem Finsupp.cast_multinomial_ne_zero {σ K : Type*} [AddMonoidWithOne K] [CharZero K]
    (s : σ →₀ ℕ) : (s.multinomial : K) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (by
    rw [Finsupp.multinomial_eq]
    exact Nat.multinomial_pos _ _))

namespace MvPolynomial

variable {σ K m n : Type*} [Field K]

/-- Coefficients indexed by sums of row and column exponents, normalized by multinomials. -/
noncomputable def catalecticant (rows : m → σ →₀ ℕ) (columns : n → σ →₀ ℕ) :
    MvPolynomial σ K →ₗ[K] Matrix m n K where
  toFun p i j := p.coeff (rows i + columns j) / ((rows i + columns j).multinomial : K)
  map_add' p q := by
    ext i j
    change (p + q).coeff _ / _ = p.coeff _ / _ + q.coeff _ / _
    simp [add_div]
  map_smul' a p := by
    ext i j
    change (a • p).coeff _ / _ = a * (p.coeff _ / _)
    simp [smul_eq_mul, mul_div_assoc]

/-- The entry of the catalecticant of `p` at `(i, j)` is the coefficient of `p` at the exponent
`rows i + columns j`, divided by the multinomial coefficient of that exponent. -/
@[simp] theorem catalecticant_apply (rows : m → σ →₀ ℕ) (columns : n → σ →₀ ℕ)
    (p : MvPolynomial σ K) (i : m) (j : n) :
    catalecticant rows columns p i j =
      p.coeff (rows i + columns j) / ((rows i + columns j).multinomial : K) := rfl

/-- A power of a linear form gives an outer product on any pair of exponent families whose
combined degree is the power. The normalization is invertible in characteristic zero. -/
theorem catalecticant_linearCombination_pow [Fintype σ] [CharZero K]
    (rows : m → σ →₀ ℕ) (columns : n → σ →₀ ℕ) (a : σ → K) (d : ℕ)
    (hdegree : ∀ i j, (rows i + columns j).sum (fun _ e => e) = d) :
    catalecticant rows columns ((∑ i, a i • X i) ^ d) =
      Matrix.vecMulVec (fun i => (rows i).prod (fun v e => a v ^ e))
        (fun j => (columns j).prod (fun v e => a v ^ e)) := by
  classical
  ext i j
  rw [catalecticant_apply, coeff_linearCombination_X_pow_of_fintype, ite_eq_left (hdegree i j),
    Finsupp.prod_add_index' (by simp) (by simp [pow_add]), Matrix.vecMulVec_apply]
  exact mul_div_cancel_left₀ _ ((rows i + columns j).cast_multinomial_ne_zero (K := K))

end MvPolynomial
