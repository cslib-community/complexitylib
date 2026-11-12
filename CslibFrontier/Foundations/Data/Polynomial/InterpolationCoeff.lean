/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Lagrange.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Coefficients of a polynomial from its values, over an algebra

Over a field `K`, a polynomial of degree less than the number of nodes is the Lagrange interpolant
of its values (`Lagrange.eq_interpolate`), so each of its coefficients is a fixed linear
combination of its values, with the coefficients of the Lagrange basis polynomials as weights. The
same weights recover the coefficients of a polynomial over any commutative `K`-algebra `R` from
its values at the images of the nodes, although `R` need not be a field: the identity is linear in
the polynomial, and holds for the monomials `X ^ k` because it holds over `K`.

This is how a coefficient of a multivariate polynomial in one of its variables is obtained from
substitutions of constants for that variable, with `R` a polynomial ring over `K`.

## Main results

* `Lagrange.coeff_eq_sum_coeff_basis_smul_eval`: for a polynomial `q` over a `K`-algebra of
  degree less than `#s`, and nodes `v` injective on `s`,
  `q.coeff i = ∑ j ∈ s, (Lagrange.basis s v j).coeff i • q.eval (algebraMap K R (v j))`.
-/

public section

namespace Lagrange

open Polynomial Finset

variable {K R ι : Type*} [Field K] [CommSemiring R] [Algebra K R] [DecidableEq ι] {s : Finset ι}
  {v : ι → K}

/-- **The coefficients of a polynomial over a `K`-algebra are linear combinations of its values
at nodes of `K`**, with the coefficients of the Lagrange basis polynomials as weights: for nodes
`v` injective on `s` and a polynomial `q` of degree less than `#s` over a commutative
`K`-algebra, `q.coeff i = ∑ j ∈ s, (Lagrange.basis s v j).coeff i • q.eval (algebraMap K R (v j))`.
-/
theorem coeff_eq_sum_coeff_basis_smul_eval (hv : Set.InjOn v s) {q : R[X]}
    (hq : q.natDegree < #s) (i : ℕ) :
    q.coeff i = ∑ j ∈ s, (Lagrange.basis s v j).coeff i • q.eval (algebraMap K R (v j)) := by
  -- The identity for the monomial `X ^ k` over `K`.
  have key (k : ℕ) (hk : k < #s) :
      ∑ j ∈ s, (Lagrange.basis s v j).coeff i * v j ^ k = if i = k then 1 else 0 := by
    have h := congrArg (fun p : K[X] => p.coeff i) (eq_interpolate (f := (X : K[X]) ^ k) hv
      (by rw [degree_X_pow]; exact_mod_cast hk))
    simp only [interpolate_apply, eval_pow, eval_X, finsetSum_coeff, coeff_C_mul,
      coeff_X_pow] at h
    exact (sum_congr rfl fun j _ => mul_comm _ _).trans h.symm
  have hterm (k : ℕ) (hk : k ∈ range (q.natDegree + 1)) :
      ∑ j ∈ s, (Lagrange.basis s v j).coeff i • (q.coeff k * algebraMap K R (v j) ^ k) =
        if i = k then q.coeff k else 0 := by
    calc _ = q.coeff k * algebraMap K R (∑ j ∈ s, (Lagrange.basis s v j).coeff i * v j ^ k) := by
          simp only [map_sum, map_mul, map_pow, mul_sum, Algebra.smul_def]
          exact sum_congr rfl fun j _ => by ring
      _ = _ := by
          rw [key k ((mem_range_succ_iff.1 hk).trans_lt hq)]
          split_ifs <;> simp
  simp only [eval_eq_sum_range, smul_sum]
  rw [sum_comm, sum_congr rfl hterm, sum_ite_eq]
  split_ifs with h
  · rfl
  · exact coeff_eq_zero_of_natDegree_lt (by simpa using h)

end Lagrange
