/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, bilinear complexity: the polynomial multiplication tensor)

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Basic
public import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Lagrange

/-!
# The polynomial multiplication tensors

`Tensor.full a b` is the tensor of multiplying a polynomial of length `a` (degree below `a`) by
one of length `b`, returning all `a + b - 1` coefficients of the product: the full product
`Full_{a,b}` of [Pass][Pass2026], §2.1. All three legs are indexed by `Fin (a + b - 1)`: the
input legs are padded by zero rows, so that every polynomial tensor of the same output length
has the same index types and the leg exchanges act on one type. The middle product
`Tensor.mid a b = swap23 (full a b)` is the dual `Mid_{a,b} = Full_{a,b}^{23}`
of [Pass][Pass2026], equation (2): from `A` of length `a` and the coefficients of a product
`A Q`, recover `b` coefficients of `Q`.

Exchanging the two inputs exchanges the lengths (`Tensor.swap12_full`,
[Pass][Pass2026], equation (9)), and `full 1 1` is the unit tensor.

**Rank** ([Pass][Pass2026], Lemma 2.3, for the full product): `full a b` has rank at most
`a + b - 1` over a field of characteristic zero, by evaluation at `a + b - 1` integer points and
Lagrange interpolation (`Tensor.rank_full`). The bound transfers to `mid a b` and to the other
leg exchanges, since rank is invariant under them.

## Main definitions

* `Cslib.Tensor.full`, `Cslib.Tensor.mid`: the full and middle polynomial products.

## Main results

* `Cslib.Tensor.bil_full`: the bilinear map of `full a b` is polynomial multiplication.
* `Cslib.Tensor.swap12_full`, `Cslib.Tensor.full_one_one`: symmetry and the base case.
* `Cslib.Tensor.rank_full`, `Cslib.Tensor.rank_mid`: the interpolation rank bound.

## References

* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], §2.1, Lemma 2.3 and
  equation (9)
-/

@[expose] public section

namespace Cslib.Tensor

open Finset Polynomial

variable {K : Type*}

/-- **The full polynomial product** `Full_{a,b}`: the coefficient `k` of the product of a
polynomial with coefficients `i < a` and one with coefficients `j < b`, with all legs padded to
`Fin (a + b - 1)`. -/
def full [Zero K] [One K] (a b : ℕ) :
    Tensor K (Fin (a + b - 1)) (Fin (a + b - 1)) (Fin (a + b - 1)) :=
  fun i j k => if i.val < a ∧ j.val < b ∧ i.val + j.val = k.val then 1 else 0

/-- **The middle product** `Mid_{a,b}`, the dual of the full product: exchange the right input
and the output legs. -/
def mid [Zero K] [One K] (a b : ℕ) :
    Tensor K (Fin (a + b - 1)) (Fin (a + b - 1)) (Fin (a + b - 1)) :=
  swap23 (full a b)

@[simp] theorem full_apply [Zero K] [One K] (a b : ℕ) (i j k : Fin (a + b - 1)) :
    full a b i j k = (if i.val < a ∧ j.val < b ∧ i.val + j.val = k.val then 1 else 0 : K) :=
  rfl

@[simp] theorem mid_apply [Zero K] [One K] (a b : ℕ) (i k j : Fin (a + b - 1)) :
    mid a b i k j = (if i.val < a ∧ j.val < b ∧ i.val + j.val = k.val then 1 else 0 : K) :=
  rfl

/-- The polynomial with the coefficient list `A`, truncated to the coefficients below `a`. -/
noncomputable def toPoly [Semiring K] {s : ℕ} (a : ℕ) (A : Fin s → K) : K[X] :=
  ∑ i : Fin s with i.val < a, C (A i) * X ^ i.val

/-- The bilinear map of `full a b` is the coefficient list of the product of the two input
polynomials. -/
theorem bil_full [CommSemiring K] (a b : ℕ) (A B : Fin (a + b - 1) → K) (k : Fin (a + b - 1)) :
    (full a b).bil A B k = (toPoly a A * toPoly b B).coeff k := by
  simp only [bil, toPoly, Finset.sum_mul_sum, Polynomial.finsetSum_coeff, Finset.sum_filter,
    full_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.val < a
  · simp only [hi, ↓reduceIte, true_and]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j.val < b
    · simp only [hj, ↓reduceIte, true_and]
      rw [mul_mul_mul_comm, ← C_mul, ← pow_add, coeff_C_mul_X_pow]
      by_cases hk : i.val + j.val = k.val
      · simp [hk]
      · simp [hk, Ne.symm hk]
    · simp [hj]
  · simp [hi]

/-- Exchanging the two inputs of `Full_{a,b}` gives `Full_{b,a}` ([Pass][Pass2026], eq. (9)). -/
theorem swap12_full [Zero K] [One K] (a b : ℕ) :
    swap12 (full a b : Tensor K _ _ _) =
      reindex (finCongr (by omega)) (finCongr (by omega)) (finCongr (by omega)) (full b a) := by
  funext j i k
  simp only [swap12_apply, reindex_apply, full_apply, finCongr_symm_apply, Fin.val_cast]
  exact if_congr (by omega) rfl rfl

/-- `Full_{1,1}` is the unit tensor. -/
theorem full_one_one [Zero K] [One K] : (full 1 1 : Tensor K _ _ _) = unit 1 := by
  funext i j k
  simp only [full_apply, unit_apply, Fin.ext_iff]
  exact if_congr (by omega) rfl rfl

/-- **Interpolation bound** ([Pass][Pass2026], Lemma 2.3): `Full_{a,b}` has rank at most
`a + b - 1` over a field of characteristic zero. Evaluate both inputs at the integer points
`0, …, a + b - 2`, multiply the values, and recover the coefficients of the product by Lagrange
interpolation. -/
theorem rank_full [Field K] [CharZero K] (a b : ℕ) :
    Rank (a + b - 1) (full a b : Tensor K _ _ _) := by
  let v : Fin (a + b - 1) → K := fun t => (t.val : K)
  have hv : Set.InjOn v (univ : Finset (Fin (a + b - 1))) :=
    Set.injOn_of_injective (Nat.cast_injective.comp Fin.val_injective)
  refine ⟨Matrix.of fun t i => if i.val < a then v t ^ i.val else 0,
    Matrix.of fun t j => if j.val < b then v t ^ j.val else 0,
    Matrix.of fun k t => (Lagrange.basis univ v t).coeff k.val, ?_⟩
  funext i j k
  rw [restrict_unit, full_apply]
  simp only [Matrix.of_apply]
  by_cases hi : i.val < a
  · by_cases hj : j.val < b
    · simp only [hi, hj, ↓reduceIte, true_and]
      have hdeg : ((X : K[X]) ^ (i.val + j.val)).degree <
          (#(univ : Finset (Fin (a + b - 1))) : WithBot ℕ) := by
        rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
        exact_mod_cast (by omega : i.val + j.val < a + b - 1)
      calc ∑ t, v t ^ i.val * v t ^ j.val * (Lagrange.basis univ v t).coeff k.val
          = (∑ t, C (((X : K[X]) ^ (i.val + j.val)).eval (v t)) *
              Lagrange.basis univ v t).coeff k.val := by
            simp only [Polynomial.eval_pow, Polynomial.eval_X]
            simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, pow_add]
        _ = ((X : K[X]) ^ (i.val + j.val)).coeff k.val := by
            rw [← Lagrange.interpolate_apply, ← Lagrange.eq_interpolate hv hdeg]
        _ = _ := by
            rw [Polynomial.coeff_X_pow]
            exact if_congr eq_comm rfl rfl
    · simp [hj]
  · simp [hi]

theorem rank_mid [Field K] [CharZero K] (a b : ℕ) :
    Rank (a + b - 1) (mid a b : Tensor K _ _ _) :=
  (rank_full a b).swap23

end Cslib.Tensor
