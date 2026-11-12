/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.FormulaOps
public import CslibFrontier.Foundations.Data.Polynomial.InterpolationCoeff

/-!
# Interpolation of arithmetic formulas of unbounded fan-in

Over a field of characteristic zero, a coefficient of a polynomial of degree at most `r` in one
variable is a fixed linear combination of its values at the nodes `0, 1, …, r`
(`Lagrange.coeff_eq_sum_coeff_basis_smul_eval`). For a formula
`Cslib.Circuits.Arithmetic.SPFormula`, a value at a node is a substitution of a constant, or of a
multiple of an input, for an input, which changes neither the product-depth nor the shape of the
formula, and the linear combination is one sum gate on top. So the coefficients of a formula in
one of its variables, and its homogeneous components, have formulas of the same product-depth and
of `r + 1` times the size [ChouKumarSolomon2019, Lemmas 4.10 and 4.11].

* `SPFormula.coeffLast i r F` computes the coefficient of `y ^ i` of the polynomial of `F`, viewed
  as a polynomial in its last variable `y` with coefficients in the other variables, when its
  degree in `y` is at most `r`. The view is stated through the substitutions of constants for
  `y`: `SPFormula.polynomial_coeffLast` holds for every `P : Polynomial (MvPolynomial (Fin n) K)`
  of degree at most `r` whose value at each constant `α` is the polynomial of `F` with `α`
  substituted for the last variable. The polynomial
  `MvPolynomial.aeval (Fin.lastCases Polynomial.X fun k => Polynomial.C (MvPolynomial.X k))` of
  the polynomial of `F` is such a `P`, and so is its image under any other identification of
  `MvPolynomial (Fin (n + 1)) K` with `Polynomial (MvPolynomial (Fin n) K)` that sends the last
  variable to `Polynomial.X`.
* `SPFormula.lowPartFormula d r F` computes the sum of the homogeneous components of degree at
  most `d` of the polynomial of `F`, when its total degree is at most `r`: scaling every input by
  `c` multiplies the component of degree `k` by `c ^ k`, and the components are the coefficients
  in `c`.

The explicit size bounds, with the nodes `0, 1, …, r`, are original.

## Main definitions

* `Cslib.Circuits.Arithmetic.SPFormula.coeffLast`: a coefficient in the last variable.
* `Cslib.Circuits.Arithmetic.SPFormula.lowPartFormula`: the homogeneous components of low degree.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_coeffLast`,
  `Cslib.Circuits.Arithmetic.SPFormula.productDepth_coeffLast_le`,
  `Cslib.Circuits.Arithmetic.SPFormula.nodeCount_coeffLast_le`: the coefficient, with the same
  product-depth and at most `(r + 1) * F.nodeCount + 1` nodes.
* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_lowPartFormula`,
  `Cslib.Circuits.Arithmetic.SPFormula.productDepth_lowPartFormula_le`,
  `Cslib.Circuits.Arithmetic.SPFormula.nodeCount_lowPartFormula_le`: the low-degree part, with the
  same product-depth and at most `(r + 1) * (3 * F.nodeCount) + 1` nodes.

## References

* [C.-N. Chou, M. Kumar, N. Solomon, *Closure Results for Polynomial
  Factorization*][ChouKumarSolomon2019], Lemma 4.10 (Interpolation) and Lemma 4.11 (Interpolation
  for Formulas), in the numbering of arXiv:1803.05933v1, §4.6
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.SPFormula

open Finset MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-! ### A coefficient in the last variable -/

/-- The coefficient of `y ^ i` of a formula of degree at most `r` in its last variable `y`: the
linear combination, with the coefficients of degree `i` of the Lagrange basis polynomials at the
nodes `0, 1, …, r`, of the formulas `F` with the constant `j` substituted for `y`. -/
noncomputable def coeffLast (i r : ℕ) (F : SPFormula K (n + 1)) : SPFormula K n :=
  sumOn (range (r + 1))
    (fun j => (Lagrange.basis (range (r + 1)) (fun j : ℕ => (j : K)) j).coeff i) fun j =>
      substFormula (constInput (Fin.lastCases (.inr (j : K)) .inl)) F

/-- **`coeffLast i r F` computes the coefficient of degree `i` in the last variable**
[ChouKumarSolomon2019, Lemma 4.11]: if `P`, a polynomial in one variable of degree at most `r`
over the polynomials in the other variables, takes at every constant `α` the value of the
polynomial of `F` with `α` substituted for its last variable, then `coeffLast i r F` computes
`P.coeff i`. -/
theorem polynomial_coeffLast [CharZero K] {F : SPFormula K (n + 1)}
    {P : Polynomial (MvPolynomial (Fin n) K)}
    (hP : ∀ α : K, aeval (Fin.lastCases (C α) X : Fin (n + 1) → MvPolynomial (Fin n) K)
      F.polynomial = P.eval (C α))
    {r : ℕ} (hr : P.natDegree ≤ r) (i : ℕ) : (coeffLast i r F).polynomial = P.coeff i := by
  rw [coeffLast, polynomial_sumOn, Lagrange.coeff_eq_sum_coeff_basis_smul_eval
    (v := fun j : ℕ => (j : K)) (s := range (r + 1)) Nat.cast_injective.injOn
    (by simpa using Nat.lt_succ_of_le hr) i]
  refine sum_congr rfl fun j _ => ?_
  rw [polynomial_substFormula, smul_eq_C_mul, algebraMap_eq, ← hP]
  congr 3
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k <;> simp

/-- Taking a coefficient in the last variable does not increase the product-depth. -/
theorem productDepth_coeffLast_le (i r : ℕ) (F : SPFormula K (n + 1)) :
    (coeffLast i r F).productDepth ≤ F.productDepth :=
  productDepth_sumOn_le _ fun _ _ =>
    productDepth_substFormula_le (B := 0) (fun k => (productDepth_constInput _ k).le) F

/-- The formula of a coefficient in the last variable has at most `(r + 1) * F.nodeCount + 1`
nodes: `r + 1` copies of `F` and a sum gate. -/
theorem nodeCount_coeffLast_le (i r : ℕ) (F : SPFormula K (n + 1)) :
    (coeffLast i r F).nodeCount ≤ (r + 1) * F.nodeCount + 1 := by
  rw [coeffLast, nodeCount_sumOn]
  refine Nat.add_le_add_right ((sum_le_sum fun j _ => nodeCount_substFormula_le (S := 1)
    (fun k => (nodeCount_constInput _ k).le) le_rfl F).trans_eq ?_) 1
  rw [sum_const, card_range, smul_eq_mul, mul_one]

/-! ### The homogeneous components of low degree -/

/-- Scaling the variables by `c` multiplies the homogeneous component of degree `k` by `c ^ k`. -/
private theorem aeval_C_mul_X_eq_sum {p : MvPolynomial (Fin n) K} {r : ℕ}
    (hr : p.totalDegree ≤ r) (c : K) :
    aeval (fun i => C c * X i) p = ∑ k ∈ range (r + 1), C c ^ k * homogeneousComponent k p := by
  have hmon (s : Fin n →₀ ℕ) (a : K) :
      aeval (fun i => C c * X i) (monomial s a) = C c ^ s.degree * monomial s a := by
    rw [aeval_monomial, algebraMap_eq, monomial_eq, Finsupp.prod, Finsupp.prod]
    simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, Finsupp.degree_apply]
    ring
  have hdeg (s : Fin n →₀ ℕ) (hs : s ∈ p.support) : s.degree ∈ range (r + 1) :=
    mem_range_succ_iff.2 ((le_totalDegree hs).trans hr)
  calc aeval (fun i => C c * X i) p
      = ∑ s ∈ p.support, C c ^ s.degree * monomial s (p.coeff s) := by
        conv_lhs => rw [← p.support_sum_monomial_coeff]
        rw [map_sum]
        exact sum_congr rfl fun s _ => hmon s _
    _ = _ := by
        rw [← sum_fiberwise_of_maps_to hdeg]
        refine sum_congr rfl fun k _ => ?_
        rw [homogeneousComponent_apply, mul_sum]
        exact sum_congr rfl fun s hs => by rw [(mem_filter.1 hs).2]

/-- The sum of the homogeneous components of degree at most `d` of a formula of total degree at
most `r`: the linear combination of the formulas `F` with every input scaled by the node `j`, for
the nodes `0, 1, …, r`, that extracts the coefficients of degree at most `d` in the scaling
parameter. -/
noncomputable def lowPartFormula (d r : ℕ) (F : SPFormula K n) : SPFormula K n :=
  sumOn (range (r + 1))
    (fun j => ∑ i ∈ range (d + 1),
      (Lagrange.basis (range (r + 1)) (fun j : ℕ => (j : K)) j).coeff i) fun j =>
      substFormula (affineInput id (fun _ => (j : K)) 0) F

/-- **`lowPartFormula d r F` computes the homogeneous components of degree at most `d`**
[ChouKumarSolomon2019, Lemma 4.11] of the polynomial of a formula `F` of total degree at most
`r`. -/
theorem polynomial_lowPartFormula [CharZero K] {F : SPFormula K n} {r : ℕ}
    (hr : F.polynomial.totalDegree ≤ r) (d : ℕ) :
    (lowPartFormula d r F).polynomial =
      ∑ k ∈ range (d + 1), homogeneousComponent k F.polynomial := by
  -- The polynomial of `F` with its inputs scaled by `c`, as a polynomial in `c`.
  let Q : Polynomial (MvPolynomial (Fin n) K) :=
    ∑ k ∈ range (r + 1), Polynomial.C (homogeneousComponent k F.polynomial) * Polynomial.X ^ k
  have hQdeg : Q.natDegree < #(range (r + 1)) := by
    rw [card_range]
    exact Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (mem_range_succ_iff.1 hk))
  have hQcoeff (k : ℕ) : Q.coeff k = homogeneousComponent k F.polynomial := by
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range]
    split_ifs with h
    · rfl
    · exact (homogeneousComponent_eq_zero _ _ (by omega)).symm
  have hQeval (c : K) : Q.eval (C c) = aeval (fun i => C c * X i) F.polynomial := by
    rw [aeval_C_mul_X_eq_sum hr, Polynomial.eval_finsetSum]
    exact sum_congr rfl fun k _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  rw [lowPartFormula, polynomial_sumOn]
  simp only [← hQcoeff, Lagrange.coeff_eq_sum_coeff_basis_smul_eval (v := fun j : ℕ => (j : K))
    Nat.cast_injective.injOn hQdeg, algebraMap_eq, hQeval, smul_eq_C_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [map_sum, sum_mul, polynomial_substFormula]
  simp only [polynomial_affineInput, id, Pi.zero_apply, C_0, add_zero]

/-- Taking the homogeneous components of low degree does not increase the product-depth. -/
theorem productDepth_lowPartFormula_le (d r : ℕ) (F : SPFormula K n) :
    (lowPartFormula d r F).productDepth ≤ F.productDepth :=
  productDepth_sumOn_le _ fun _ _ =>
    productDepth_substFormula_le (B := 0) (fun k => (productDepth_affineInput _ _ _ k).le) F

/-- The formula of the homogeneous components of low degree has at most
`(r + 1) * (3 * F.nodeCount) + 1` nodes: `r + 1` copies of `F` with every input replaced by the
three nodes of a scaled input, and a sum gate. -/
theorem nodeCount_lowPartFormula_le (d r : ℕ) (F : SPFormula K n) :
    (lowPartFormula d r F).nodeCount ≤ (r + 1) * (3 * F.nodeCount) + 1 := by
  rw [lowPartFormula, nodeCount_sumOn]
  refine Nat.add_le_add_right ((sum_le_sum fun j _ => nodeCount_substFormula_le (S := 3)
    (fun k => (nodeCount_affineInput _ _ _ k).le) (by norm_num) F).trans_eq ?_) 1
  rw [sum_const, card_range, smul_eq_mul, mul_comm 3]

end Cslib.Circuits.Arithmetic.SPFormula
