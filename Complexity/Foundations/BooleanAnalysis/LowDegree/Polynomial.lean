/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Univariate polynomials of low-degree functions on the Boolean cube

Substituting a function of degree at most `a` on the Boolean cube into a univariate polynomial of
degree at most `e` gives a function of degree at most `e * a`
(`BitString.polynomial_eval_mem_lowDegree`). This is the degree count behind composing the
modulus-amplifying polynomials of Toda and Beigel–Tarui with modular polynomials
[Toda1991], [BeigelTarui1994].

## Main results

* `Cslib.BitString.polynomial_eval_mem_lowDegree`: degrees multiply under substitution into a
  univariate polynomial.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
-/

public section

namespace Cslib.BitString

open Finset

variable {R : Type*} [CommRing R] {ι : Type*}

/-- Substituting a function of degree at most `a` into a univariate polynomial of degree at most
`e` gives a function of degree at most `e * a`. -/
theorem polynomial_eval_mem_lowDegree {a e : ℕ} {f : (ι → Bool) → R}
    (hf : f ∈ lowDegree R ι a) {P : Polynomial R} (hP : P.natDegree ≤ e) :
    (fun x => P.eval (f x)) ∈ lowDegree R ι (e * a) := by
  have h : (fun x => P.eval (f x)) = ∑ i ∈ range (P.natDegree + 1), P.coeff i • f ^ i := by
    funext x
    rw [Polynomial.eval_eq_sum_range]
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
  rw [h]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ≤ e := (Nat.lt_succ_iff.1 (mem_range.1 hi)).trans hP
  exact lowDegree_mono (Nat.mul_le_mul_right a hi') (pow_mem_lowDegree hf i)

end Cslib.BitString
