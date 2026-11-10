/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Lagrange

/-!
# The polynomial `k`-wise independent hash family

For a finite field `F`, the polynomials of degree less than `k`, evaluated as maps `F → F` and
indexed by their coefficient vectors `c : Fin k → F` (`Cslib.Probability.polynomialHash`), form a
`k`-wise independent hash family (`Cslib.Probability.isKWiseIndependentHash_polynomialHash`)
[Vadhan, Section 3.5.5][Vadhan2012]: by Lagrange interpolation, every
assignment of values to at most `k` points is attained by a polynomial of degree less than `k`,
and evaluation depends additively on the coefficients, so the surjectivity criterion
`Cslib.Probability.isKWiseIndependentHash_of_surjective` applies. The seed consists of `k` field
elements. For `k = 2` these are the affine maps `x ↦ c₀ + c₁ x` of
`Cslib.Probability.isPairwiseIndependentHash_affineHash` in dimension one.

## Main definitions

* `Cslib.Probability.polynomialHash`: evaluation of the polynomial with coefficients `c`.

## Main results

* `Cslib.Probability.isKWiseIndependentHash_polynomialHash`: the polynomials of degree less than
  `k` form a `k`-wise independent hash family.

## References

* [S. P. Vadhan, *Pseudorandomness*, Section 3.5.5][Vadhan2012]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

@[expose] public section

namespace Cslib.Probability

open Finset Polynomial

section Def

variable {F : Type*} [Semiring F]

/-- The polynomial hash with coefficient vector `c : Fin k → F`: the value at `x` of the
polynomial `∑ j < k, c j X ^ j`, of degree less than `k`. -/
def polynomialHash {k : ℕ} (c : Fin k → F) (x : F) : F :=
  ∑ j, c j * x ^ (j : ℕ)

/-- The polynomial hash is additive in its coefficient vector. -/
theorem polynomialHash_add {k : ℕ} (c d : Fin k → F) :
    polynomialHash (c + d) = polynomialHash c + polynomialHash d := by
  funext x
  simp only [polynomialHash, Pi.add_apply, add_mul, sum_add_distrib]

/-- The polynomial hash with coefficients `c` evaluates any polynomial of degree less than `k`
whose coefficients are `c`. -/
theorem polynomialHash_eq_eval {k : ℕ} (P : F[X]) (hP : P.natDegree < k) (x : F) :
    polynomialHash (fun j : Fin k => P.coeff j) x = P.eval x := by
  rw [eval_eq_sum_range' hP, polynomialHash]
  exact Fin.sum_univ_eq_sum_range (fun j => P.coeff j * x ^ j) k

end Def

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The polynomial hash family is `k`-wise independent** [Vadhan, Section 3.5.5][Vadhan2012]:
over a finite field `F`, the polynomials of degree less than `k` with uniformly
random coefficients take independent uniform values at any `k` distinct points. -/
theorem isKWiseIndependentHash_polynomialHash (k : ℕ) :
    IsKWiseIndependentHash k (polynomialHash : (Fin k → F) → F → F) := by
  let g : (Fin k → F) →+ F → F :=
    { toFun := polynomialHash
      map_zero' := by
        funext x
        simp [polynomialHash]
      map_add' := polynomialHash_add }
  refine isKWiseIndependentHash_of_surjective g fun T hT y => ?_
  let r (x : F) : F := if hx : x ∈ T then y ⟨x, hx⟩ else 0
  let P := Lagrange.interpolate T id r
  refine ⟨fun j => P.coeff j, funext fun x => ?_⟩
  have hnode : P.eval (x : F) = y x := by
    rw [show P.eval (x : F) = P.eval (id x.1) from rfl,
      Lagrange.eval_interpolate_at_node r (Set.injOn_id _) x.2]
    simp only [r, x.2, ↓reduceDIte]
  change polynomialHash (fun j : Fin k => P.coeff j) x = y x
  by_cases hP : P = 0
  · rw [← hnode, hP]
    simp [polynomialHash]
  · have hdeg : P.natDegree < k := by
      rw [natDegree_lt_iff_degree_lt hP]
      exact (Lagrange.degree_interpolate_lt r (Set.injOn_id _)).trans_le (by exact_mod_cast hT)
    rw [polynomialHash_eq_eval P hdeg, hnode]

end Cslib.Probability
