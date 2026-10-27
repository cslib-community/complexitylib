/-
Copyright (c) 2026 Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The `ℓ₁` coefficient norm of an integer polynomial

This module defines the `ℓ₁` coefficient norm `Polynomial.coeffNorm1` of a univariate integer
polynomial `p : ℤ[X]`:
$$\|p\|_1 = \sum_{i \in \mathrm{supp}(p)} |p_i|,$$
together with its basic triangle, scaling, shift, linear-factor, submultiplicative, and
integer-cast inequalities used in Lemma 4.6, Lemma 5.1, and Appendix B of `[OpenAI2026ETH]`.

## Main definitions

* `Polynomial.coeffNorm1`: the `ℓ₁` coefficient norm `∑ i ∈ p.support, (p.coeff i).natAbs`.

## Main results

* `Polynomial.natAbs_coeff_le_coeffNorm1`, `Polynomial.sum_natAbs_coeff_le_coeffNorm1`:
  individual and finite-subset coefficient bounds by `coeffNorm1`.
* `Polynomial.coeffNorm1_add_le`, `Polynomial.coeffNorm1_sub_le`, `Polynomial.coeffNorm1_sum_le`:
  triangle inequalities for binary sums, differences, and finite sums.
* `Polynomial.coeffNorm1_C_mul_le`, `Polynomial.coeffNorm1_X_mul`,
  `Polynomial.coeffNorm1_mul_X_pow_le`, `Polynomial.coeffNorm1_C_sub_X_mul_le`,
  `Polynomial.coeffNorm1_one_sub_X_mul_le`, `Polynomial.coeffNorm1_one_sub_X_pow_mul_le`:
  norm bounds under scalar multiplication, monomial shifts, and linear factors.
* `Polynomial.coeffNorm1_mul_le`, `Polynomial.coeffNorm1_pow_le`, `Polynomial.coeffNorm1_prod_le`:
  submultiplicativity for binary products, powers, and finite products.
* `Polynomial.natCast_coeffNorm1`: integer cast identity
  `(p.coeffNorm1 : ℤ) = ∑ i ∈ p.support, |p.coeff i|`.
* `Polynomial.coeffNorm1_ofCoeffList`: `coeffNorm1 (ofCoeffList l) = (l.map Int.natAbs).sum`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Lemma 4.6, Appendix B.1, and Appendix B.2)
-/

@[expose] public noncomputable section

namespace Polynomial

open Finset

/-- The `ℓ₁` coefficient norm `∑ i ∈ p.support, (p.coeff i).natAbs` of an integer polynomial. -/
def coeffNorm1 (p : ℤ[X]) : ℕ :=
  ∑ i ∈ p.support, (p.coeff i).natAbs

/-- The `ℓ₁` norm of `0` is `0`. -/
@[simp]
theorem coeffNorm1_zero : coeffNorm1 0 = 0 := by
  simp only [coeffNorm1, support_zero, sum_empty]

/-- Sum expression for `coeffNorm1` over any superset `S ⊇ p.support`. -/
theorem coeffNorm1_eq_sum_of_support_subset {p : ℤ[X]} {S : Finset ℕ} (hS : p.support ⊆ S) :
    coeffNorm1 p = ∑ i ∈ S, (p.coeff i).natAbs := by
  unfold coeffNorm1
  refine sum_subset hS fun i _ hi => ?_
  rw [notMem_support_iff.mp hi, Int.natAbs_zero]

/-- Every individual coefficient of `p` has absolute value at most `coeffNorm1 p`. -/
theorem natAbs_coeff_le_coeffNorm1 (p : ℤ[X]) (k : ℕ) :
    (p.coeff k).natAbs ≤ coeffNorm1 p := by
  by_cases hk : k ∈ p.support
  · exact single_le_sum (f := fun i => (p.coeff i).natAbs) (fun _ _ => Nat.zero_le _) hk
  · rw [notMem_support_iff.mp hk, Int.natAbs_zero]
    exact Nat.zero_le _

/-- The sum of `(p.coeff i).natAbs` over any finite set of indices is at most `coeffNorm1 p`. -/
theorem sum_natAbs_coeff_le_coeffNorm1 (p : ℤ[X]) (s : Finset ℕ) :
    ∑ i ∈ s, (p.coeff i).natAbs ≤ coeffNorm1 p := by
  have hsub : ∑ i ∈ s, (p.coeff i).natAbs = ∑ i ∈ s ∩ p.support, (p.coeff i).natAbs := by
    refine (sum_subset inter_subset_left ?_).symm
    intro i hi his
    rw [mem_inter, not_and_or, notMem_support_iff] at his
    rcases his with hns | hp0
    · exact absurd hi hns
    · simp only [hp0, Int.natAbs_zero]
  rw [hsub, coeffNorm1]
  exact sum_le_sum_of_subset inter_subset_right

/-- The `ℓ₁` norm of a constant polynomial `C a` is `a.natAbs`. -/
theorem coeffNorm1_C (a : ℤ) : coeffNorm1 (C a) = a.natAbs := by
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, coeffNorm1_zero, Int.natAbs_zero]
  · rw [coeffNorm1, support_C ha, sum_singleton, coeff_C_zero]

/-- The `ℓ₁` norm of `1` is `1`. -/
@[simp]
theorem coeffNorm1_one : coeffNorm1 1 = 1 := by
  rw [← C_1, coeffNorm1_C, Int.natAbs_one]

/-- Negating a polynomial preserves `coeffNorm1`. -/
@[simp]
theorem coeffNorm1_neg (p : ℤ[X]) : coeffNorm1 (-p) = coeffNorm1 p := by
  rw [coeffNorm1_eq_sum_of_support_subset (S := p.support) (by simp), coeffNorm1]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_neg, Int.natAbs_neg]

/-- Triangle inequality for `coeffNorm1`. -/
theorem coeffNorm1_add_le (p q : ℤ[X]) :
    coeffNorm1 (p + q) ≤ coeffNorm1 p + coeffNorm1 q := by
  have hsub : (p + q).support ⊆ p.support ∪ q.support := support_add
  calc
    coeffNorm1 (p + q)
      ≤ ∑ i ∈ p.support ∪ q.support, ((p + q).coeff i).natAbs :=
        sum_le_sum_of_subset hsub
    _ ≤ ∑ i ∈ p.support ∪ q.support, ((p.coeff i).natAbs + (q.coeff i).natAbs) := by
        refine sum_le_sum fun i _ => ?_
        rw [coeff_add]
        exact Int.natAbs_add_le _ _
    _ = (∑ i ∈ p.support ∪ q.support, (p.coeff i).natAbs) +
          ∑ i ∈ p.support ∪ q.support, (q.coeff i).natAbs := sum_add_distrib
    _ ≤ coeffNorm1 p + coeffNorm1 q :=
        add_le_add (sum_natAbs_coeff_le_coeffNorm1 p _) (sum_natAbs_coeff_le_coeffNorm1 q _)

/-- Difference triangle inequality for `coeffNorm1`. -/
theorem coeffNorm1_sub_le (p q : ℤ[X]) :
    coeffNorm1 (p - q) ≤ coeffNorm1 p + coeffNorm1 q := by
  rw [sub_eq_add_neg, ← coeffNorm1_neg q]
  exact coeffNorm1_add_le p (-q)

/-- Finite-sum triangle inequality for `coeffNorm1`. -/
theorem coeffNorm1_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    coeffNorm1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffNorm1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, coeffNorm1_zero, le_refl]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (coeffNorm1_add_le (f a) (∑ i ∈ s, f i)).trans (Nat.add_le_add_left ih _)

/-- Scaling by `C a` scales `coeffNorm1` by at most `a.natAbs`. -/
theorem coeffNorm1_C_mul_le (a : ℤ) (p : ℤ[X]) :
    coeffNorm1 (C a * p) ≤ a.natAbs * coeffNorm1 p := by
  have hsub : (C a * p).support ⊆ p.support := by
    intro i hi
    rw [mem_support_iff, coeff_C_mul] at hi
    exact mem_support_iff.mpr (right_ne_zero_of_mul hi)
  calc
    coeffNorm1 (C a * p) ≤ ∑ i ∈ p.support, ((C a * p).coeff i).natAbs :=
      sum_le_sum_of_subset hsub
    _ = a.natAbs * coeffNorm1 p := by
      rw [coeffNorm1, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [coeff_C_mul, Int.natAbs_mul]

/-- Multiplying by `X` preserves `coeffNorm1`. -/
theorem coeffNorm1_X_mul (p : ℤ[X]) : coeffNorm1 (X * p) = coeffNorm1 p := by
  let S := p.support.map ⟨Nat.succ, Nat.succ_injective⟩
  have hsub : (X * p).support ⊆ S := by
    intro i hi
    rw [mem_support_iff] at hi
    rcases i with _ | i
    · rw [mul_comm, coeff_mul_X_zero] at hi
      exact (hi rfl).elim
    · rw [mul_comm, coeff_mul_X] at hi
      exact mem_map.mpr ⟨i, mem_support_iff.mpr hi, rfl⟩
  rw [coeffNorm1_eq_sum_of_support_subset hsub, sum_map, coeffNorm1]
  refine sum_congr rfl fun i _ => ?_
  change ((X * p).coeff (i + 1)).natAbs = (p.coeff i).natAbs
  rw [mul_comm, coeff_mul_X]

/-- Multiplying by `X ^ k` does not increase `coeffNorm1`. -/
theorem coeffNorm1_mul_X_pow_le (p : ℤ[X]) (k : ℕ) :
    coeffNorm1 (p * X ^ k) ≤ coeffNorm1 p := by
  rw [coeffNorm1]
  have hsub : (p * X ^ k).support ⊆ p.support.map ⟨fun i => i + k, add_left_injective k⟩ := by
    intro i hi
    rw [mem_support_iff] at hi
    rw [mem_map]
    by_cases hik : k ≤ i
    · refine ⟨i - k, ?_, by simp only [Function.Embedding.coeFn_mk]; omega⟩
      rw [mem_support_iff]
      intro h0
      apply hi
      have hi_eq : i = i - k + k := (Nat.sub_add_cancel hik).symm
      rw [hi_eq, coeff_mul_X_pow, h0]
    · exfalso
      apply hi
      rw [mul_comm, coeff_X_pow_mul']
      simp only [hik, ↓reduceIte]
  refine (sum_le_sum_of_subset hsub).trans ?_
  rw [sum_map]
  refine le_of_eq (sum_congr rfl fun i _ => ?_)
  simp only [Function.Embedding.coeFn_mk, coeff_mul_X_pow]

/-- Multiplying by `C a - X` scales `coeffNorm1` by at most `a.natAbs + 1`. -/
theorem coeffNorm1_C_sub_X_mul_le (a : ℤ) (p : ℤ[X]) :
    coeffNorm1 ((C a - X) * p) ≤ (a.natAbs + 1) * coeffNorm1 p := by
  rw [sub_mul, add_one_mul]
  have h1 := coeffNorm1_sub_le (C a * p) (X * p)
  rw [coeffNorm1_X_mul] at h1
  exact h1.trans (Nat.add_le_add_right (coeffNorm1_C_mul_le a p) _)

/-- Multiplying by `1 - X` increases `coeffNorm1` by at most a factor of `2`. -/
theorem coeffNorm1_one_sub_X_mul_le (p : ℤ[X]) :
    coeffNorm1 ((1 - X) * p) ≤ 2 * coeffNorm1 p := by
  simpa only [C_1, Int.natAbs_one, Nat.reduceAdd] using coeffNorm1_C_sub_X_mul_le 1 p

/-- Multiplying by `(1 - X) ^ ℓ` increases `coeffNorm1` by at most a factor of `2 ^ ℓ`. -/
theorem coeffNorm1_one_sub_X_pow_mul_le (ℓ : ℕ) (p : ℤ[X]) :
    coeffNorm1 ((1 - X) ^ ℓ * p) ≤ 2 ^ ℓ * coeffNorm1 p := by
  induction ℓ with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ ℓ ih =>
    have hEq : (1 - X) ^ (ℓ + 1) * p = (1 - X) * ((1 - X) ^ ℓ * p) := by ring
    rw [hEq, pow_succ', mul_assoc]
    exact (coeffNorm1_one_sub_X_mul_le _).trans (Nat.mul_le_mul_left 2 ih)

/-- `coeffNorm1` is submultiplicative on `ℤ[X]`. -/
theorem coeffNorm1_mul_le (p q : ℤ[X]) :
    coeffNorm1 (p * q) ≤ coeffNorm1 p * coeffNorm1 q := by
  have hdecomp : p * q = ∑ i ∈ p.support, C (p.coeff i) * (q * X ^ i) := by
    conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
    rw [sum_mul]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hdecomp]
  calc
    coeffNorm1 (∑ i ∈ p.support, C (p.coeff i) * (q * X ^ i))
      ≤ ∑ i ∈ p.support, coeffNorm1 (C (p.coeff i) * (q * X ^ i)) :=
        coeffNorm1_sum_le _ _
    _ ≤ ∑ i ∈ p.support, (p.coeff i).natAbs * coeffNorm1 q := by
        refine sum_le_sum fun i _ => ?_
        exact (coeffNorm1_C_mul_le (p.coeff i) _).trans
          (Nat.mul_le_mul_left _ (coeffNorm1_mul_X_pow_le q i))
    _ = coeffNorm1 p * coeffNorm1 q := by
        rw [← sum_mul, ← coeffNorm1]

/-- `coeffNorm1 (p ^ k) ≤ coeffNorm1 p ^ k`. -/
theorem coeffNorm1_pow_le (p : ℤ[X]) (k : ℕ) :
    coeffNorm1 (p ^ k) ≤ coeffNorm1 p ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, coeffNorm1_one, le_refl]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (coeffNorm1_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- `coeffNorm1` of a finite product is at most the product of the `coeffNorm1`s. -/
theorem coeffNorm1_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    coeffNorm1 (∏ a ∈ s, f a) ≤ ∏ a ∈ s, coeffNorm1 (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, coeffNorm1_one, le_refl]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (coeffNorm1_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

/-- Casting `coeffNorm1 p` to `ℤ` gives the sum of integer absolute values `|p.coeff i|`. -/
theorem natCast_coeffNorm1 (p : ℤ[X]) :
    (coeffNorm1 p : ℤ) = ∑ i ∈ p.support, |p.coeff i| := by
  unfold coeffNorm1
  rw [Nat.cast_sum]
  refine sum_congr rfl fun i _ => Int.natCast_natAbs (p.coeff i)

/-- Integer-cast constant norm `(coeffNorm1 (C a) : ℤ) = |a|`. -/
theorem natCast_coeffNorm1_C (a : ℤ) : (coeffNorm1 (C a) : ℤ) = |a| := by
  rw [coeffNorm1_C, Int.natCast_natAbs]

/-- Integer-cast triangle inequality for `coeffNorm1`. -/
theorem natCast_coeffNorm1_add_le (p q : ℤ[X]) :
    (coeffNorm1 (p + q) : ℤ) ≤ (coeffNorm1 p : ℤ) + (coeffNorm1 q : ℤ) := by
  exact_mod_cast coeffNorm1_add_le p q

/-- Integer-cast finite-sum triangle inequality for `coeffNorm1`. -/
theorem natCast_coeffNorm1_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) :
    (coeffNorm1 (∑ i ∈ s, f i) : ℤ) ≤ ∑ i ∈ s, (coeffNorm1 (f i) : ℤ) := by
  rw [← Nat.cast_sum]
  exact_mod_cast coeffNorm1_sum_le s f

/-- Integer-cast scalar multiplication bound for `coeffNorm1`. -/
theorem natCast_coeffNorm1_C_mul_le (a : ℤ) (p : ℤ[X]) :
    (coeffNorm1 (C a * p) : ℤ) ≤ |a| * (coeffNorm1 p : ℤ) := by
  rw [← Int.natCast_natAbs, ← Nat.cast_mul]
  exact_mod_cast coeffNorm1_C_mul_le a p

/-- The `ℓ₁` coefficient norm of `ofCoeffList l` equals the sum of `Int.natAbs` of `l`. -/
@[simp]
theorem coeffNorm1_ofCoeffList (l : List ℤ) :
    coeffNorm1 (ofCoeffList l) = (l.map Int.natAbs).sum := by
  have hsub : (ofCoeffList l).support ⊆ range l.length := fun i hi =>
    mem_range.2 <| by
      by_contra hge
      exact (mem_support_iff.1 hi)
        (by rw [coeff_ofCoeffList, List.getD_eq_default l 0 (by omega)])
  rw [coeffNorm1_eq_sum_of_support_subset hsub,
    ← Fin.sum_univ_eq_sum_range (fun i => ((ofCoeffList l).coeff i).natAbs),
    ← List.sum_map_range l.length (fun i => ((ofCoeffList l).coeff i).natAbs)]
  congr 1; apply List.ext_getElem (by simp only [List.length_map, List.length_range])
  intro i hi₁ _
  have hi : i < l.length := by simpa only [List.length_map, List.length_range] using hi₁
  simp only [List.getElem_map, List.getElem_range, coeff_ofCoeffList, List.getD_eq_getElem l 0 hi]

end Polynomial
