/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.ReplacementCounting.AffineTaylor
public import Complexity.Foundations.Data.Polynomial.StreamingHermite

/-!
# Boolean counting from untruncated finite-field evaluations

For polynomial replacement rows `P`, let `H` be the sum over Boolean assignments of the product
of the substituted constraint polynomials. At a node `t`, form a second polynomial by summing
over marked supports `U ⊆ E`, with `|E| ≤ q`, and assignments forced to be one on `E`.
The sign of a marked support is `(-1) ^ (|E| - |U|)`. Its correction to a replacement row is
the sum, over `i ∈ U`, of `P i (t + z) - P i t`.

The existing affine-Taylor identity proves that this polynomial and `H(t + z)` agree through
degree `q`. We retain the entire polynomial: every summand has the same degree bound as `H`,
so the finite-field recovery kernel can recover `H(0)` directly from its scalar evaluations.
No table of Taylor coefficients appears in the resulting identity.

This is the algebraic counting step of the argument communicated by Charlie Cruz
[Cruz2026SublinearSpace]. The definitions and proofs here are self-contained. They apply to
arbitrary polynomial factors over a finite field; Boolean-valued constraint extensions give
the corresponding count in that field. A native machine implementing these sums, bounds on its
live workspace, and the resulting complexity-class containment are separate obligations.

## Main definitions

* `Cslib.AffineTaylor.markedTaylorSum`: the untruncated signed marked-support polynomial.

## Main results

* `Cslib.AffineTaylor.coeff_markedTaylorSum`: agreement with the requisite Taylor coefficients.
* `Cslib.AffineTaylor.natDegree_markedTaylorSum_le`: a degree bound independent of the support
  cutoff and of the number of summands.
* `Cslib.AffineTaylor.eval_replacedSum_eq_sum_markedTaylorSum`: finite-field evaluation of `H`.
* `Cslib.ReplacementCounting.targetSum_eq_sum_markedTaylorSum`: recovery of the original
  Boolean sum when replacement rows restore the original variables at zero.

## References

* Charlie Cruz, personal communication, 2026 [Cruz2026SublinearSpace].
-/

public noncomputable section

open Finset Polynomial Cslib.BitString
open scoped BigOperators

namespace Cslib.AffineTaylor

variable {A ι F : Type*} [CommRing A] [Fintype ι] {κ : F → Type*}

open Classical in
/-- The entire marked-support polynomial, without truncation in the Taylor variable.
The two signs are encoded by `U ⊆ E`; variables in `E` are forced to one in the inner cube. -/
@[expose] def markedTaylorSum (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) (q : ℕ) (t : A) : Polynomial A :=
  ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
    ∑ U ∈ E.powerset, C ((-1 : A) ^ (#E - #U)) *
      ∑ x ∈ (univ : Finset (ι → Bool)).filter (fun x => ∀ i ∈ E, x i = true),
        (factorProduct s Φ P t x).map (MvPolynomial.eval fun i => bitVal A (decide (i ∈ U)))

/-- Marked-support cancellation preserves the Taylor coefficients through the support cutoff.
The coefficients above this cutoff need not agree. -/
theorem coeff_markedTaylorSum (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) (t : A) {j q : ℕ} (hj : j ≤ q) :
    (markedTaylorSum s Φ P q t).coeff j = (taylor t (replacedSum s Φ P)).coeff j := by
  classical
  simp only [markedTaylorSum, finsetSum_coeff, coeff_C_mul, coeff_map]
  exact (coeff_taylor_replacedSum_eq_restricted_subsets s Φ P t hj).symm

private theorem natDegree_map_eval_affineInput_le (row : ι → Polynomial A) {d : ℕ}
    (hrow : ∀ i, (row i).natDegree ≤ d) (t : A) (x : ι → Bool) (y : ι → A) :
    ((affineInput row t x).map (MvPolynomial.eval y)).natDegree ≤ d := by
  classical
  rw [map_eval_affineInput]
  refine natDegree_add_le_of_degree_le (by simp only [natDegree_C, Nat.zero_le]) ?_
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  simpa only [natDegree_sub_C, natDegree_taylor] using hrow i

private theorem natDegree_map_eval_factorProduct_le (s : Finset F)
    (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A) {d : ℕ}
    (hP : ∀ f ∈ s, ∀ v i, (P f v i).natDegree ≤ d) (t : A) (x : ι → Bool) (y : ι → A) :
    ((factorProduct s Φ P t x).map (MvPolynomial.eval y)).natDegree ≤
      (∑ f ∈ s, (Φ f).totalDegree) * d := by
  rw [map_eval_factorProduct]
  refine (natDegree_prod_le _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun f hf => ?_
  rw [map_eval_affineFactor]
  exact ReplacementCounting.natDegree_eval₂_polynomial_le (Φ f) _
    (fun v => natDegree_map_eval_affineInput_le (P f v) (hP f hf v) t x y)

/-- Keeping higher Taylor terms does not increase the row-substitution degree bound. -/
theorem natDegree_markedTaylorSum_le (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) {d : ℕ}
    (hP : ∀ f ∈ s, ∀ v i, (P f v i).natDegree ≤ d) (q : ℕ) (t : A) :
    (markedTaylorSum s Φ P q t).natDegree ≤ (∑ f ∈ s, (Φ f).totalDegree) * d := by
  classical
  unfold markedTaylorSum
  refine natDegree_sum_le_of_forall_le _ _ fun E _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun U _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact natDegree_map_eval_factorProduct_le s Φ P hP t x _

section FiniteField

variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K] [DecidableEq I]

/-- Recover the Boolean replacement sum by scalar evaluations of the entire marked-support
polynomials. The explicit row bound ensures that no higher term aliases a required coefficient
in the multiplicative finite-field sum. -/
theorem eval_replacedSum_eq_sum_markedTaylorSum (s : Finset F)
    (Φ : ∀ f, MvPolynomial (κ f) K) (P : ∀ f, κ f → ι → Polynomial K)
    (nodes : Finset I) (t : I → K) (q : ℕ) {d : ℕ}
    (ht : (nodes : Set I).Pairwise fun i j => IsUnit (t i - t j))
    (hq : q + 1 < Fintype.card K)
    (hP : ∀ f ∈ s, ∀ v i, (P f v i).natDegree ≤ d)
    (hinterp : (∑ f ∈ s, (Φ f).totalDegree) * d < #nodes * (q + 1))
    (hfield : (∑ f ∈ s, (Φ f).totalDegree) * d < Fintype.card K - 1) (a : K) :
    (replacedSum s Φ P).eval a = ∑ i ∈ nodes, ∑ u : Kˣ,
      hermiteEvalKernel nodes t (fun _ => q + 1) a i (u : K) *
        (markedTaylorSum s Φ P q (t i)).eval (u : K) := by
  classical
  apply eval_eq_sum_hermiteEvalKernel_mul_eval ht (fun _ _ => hq)
  · have hdeg := ReplacementCounting.natDegree_targetPolynomial_le s Φ P hP
    rw [ReplacementCounting.targetPolynomial_eq_replacedSum] at hdeg
    have hlt : (replacedSum s Φ P).natDegree < ∑ _i ∈ nodes, (q + 1) := by
      simpa only [sum_const, nsmul_eq_mul, Nat.cast_id] using hdeg.trans_lt hinterp
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hlt)
  · intro i _ j hj
    exact coeff_markedTaylorSum s Φ P (t i) (by omega)
  · intro i _
    exact (natDegree_markedTaylorSum_le s Φ P hP q (t i)).trans_lt hfield

end FiniteField

end Cslib.AffineTaylor

namespace Cslib.ReplacementCounting

variable {K ι F I : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [DecidableEq ι]
  [DecidableEq I] {κ : F → Type*}

/-- The original Boolean sum is recovered without a Taylor table when the replacement rows
restore each original variable at zero. All hypotheses concern the supplied rows and finite
field; no recovery or counting oracle is assumed. -/
theorem targetSum_eq_sum_markedTaylorSum (s : Finset F) (scope : ∀ f, κ f → ι)
    (Φ : ∀ f, MvPolynomial (κ f) K) (P : ∀ f, κ f → ι → Polynomial K)
    (nodes : Finset I) (t : I → K) (q : ℕ) {d : ℕ}
    (ht : (nodes : Set I).Pairwise fun i j => IsUnit (t i - t j))
    (hq : q + 1 < Fintype.card K)
    (hzero : ∀ f ∈ s, ∀ v i, (P f v i).eval 0 = if i = scope f v then 1 else 0)
    (hP : ∀ f ∈ s, ∀ v i, (P f v i).natDegree ≤ d)
    (hinterp : (∑ f ∈ s, (Φ f).totalDegree) * d < #nodes * (q + 1))
    (hfield : (∑ f ∈ s, (Φ f).totalDegree) * d < Fintype.card K - 1) :
    targetSum s scope Φ = ∑ i ∈ nodes, ∑ u : Kˣ,
      hermiteEvalKernel nodes t (fun _ => q + 1) 0 i (u : K) *
        (AffineTaylor.markedTaylorSum s Φ P q (t i)).eval (u : K) := by
  rw [← eval_zero_targetPolynomial s scope Φ P hzero, targetPolynomial_eq_replacedSum]
  exact AffineTaylor.eval_replacedSum_eq_sum_markedTaylorSum s Φ P nodes t q
    ht hq hP hinterp hfield 0

end Cslib.ReplacementCounting
