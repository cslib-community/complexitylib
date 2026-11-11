/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, moments of products of linear forms over weak compositions)

public import CslibFrontier.Foundations.Combinatorics.CompositionMoment

/-!
# Moments of products of linear forms over weak compositions

The comparisons of `CompositionMoment` between the factorial moments of a uniform weak
composition `M` of `t` into the parts `S` and those of independent geometric variables of mean
`G = t / r`, `r` the number of parts, extend from one product of falling factorials to every
product over the parts `i` of polynomials in `M i` with nonnegative coefficients in the basis of
falling factorials [OpenAI, §4][OpenAI2026DepthFive]. A polynomial `∑ d, γ d * (z)_d` is
compared with its geometric moment `∑ d, γ d * d! * G ^ d`.

The two cases used for the trace moments of iterated matrix multiplication are a linear form
`a * z + b` in every part, with geometric moment `a * G + b`, and a product of two linear forms
`(a₁ * z + b₁) * (a₂ * z + b₂)`, with geometric moment
`(a₁ * G + b₁) * (a₂ * G + b₂) + a₁ * a₂ * (G ^ 2 + G)`.

## Main results

* `Finset.sum_finsuppAntidiag_prod_sum_descFactorial_le`: the upper comparison.
* `Finset.le_sum_finsuppAntidiag_prod_sum_descFactorial`: the lower comparison.
* `Finset.le_sum_finsuppAntidiag_prod_linear`: the lower comparison for linear forms.
* `Finset.sum_finsuppAntidiag_prod_linear_mul_linear_le`: the upper comparison for products of
  two linear forms.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4, occupation-moment lemma (unrefereed preprint)
-/

public section

open Nat

namespace Finset

variable {ι : Type*} [DecidableEq ι] {S : Finset ι}

/-- A product of sums over `range D` is a sum over the choices of one index for every factor. -/
private theorem prod_sum_range {R : Type*} [CommSemiring R] (D : ℕ) (γ φ : ι → ℕ → R) :
    ∏ i ∈ S, ∑ d ∈ range D, γ i d * φ i d =
      ∑ q ∈ S.pi fun _ => range D, (∏ i ∈ S, γ i (if h : i ∈ S then q i h else 0)) *
        ∏ i ∈ S, φ i (if h : i ∈ S then q i h else 0) := by
  rw [prod_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [← prod_mul_distrib,
    ← prod_attach S fun i => γ i (if h : i ∈ S then q i h else 0) *
      φ i (if h : i ∈ S then q i h else 0)]
  exact prod_congr rfl fun i _ => by simp only [i.2, ↓reduceDIte]

/-- **Upper comparison.** For polynomials with nonnegative coefficients `γ i` in the basis of
falling factorials, the sum over the weak compositions `M` of `t` of the product of their values
at `M i` is at most the number of compositions times the product of their geometric moments. -/
theorem sum_finsuppAntidiag_prod_sum_descFactorial_le (hS : S.Nonempty) (t D : ℕ)
    (γ : ι → ℕ → ℕ) :
    ((∑ M ∈ S.finsuppAntidiag t, ∏ i ∈ S, ∑ d ∈ range D, γ i d * (M i).descFactorial d : ℕ) : ℝ) ≤
      (S.card).multichoose t *
        ∏ i ∈ S, ∑ d ∈ range D, (γ i d : ℝ) * ((d ! : ℝ) * ((t : ℝ) / S.card) ^ d) := by
  simp_rw [prod_sum_range]
  rw [sum_comm, mul_sum, Nat.cast_sum]
  refine sum_le_sum fun q _ => ?_
  rw [← mul_sum, Nat.cast_mul, Nat.cast_prod, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (sum_finsuppAntidiag_prod_descFactorial_le hS t _)
    (prod_nonneg fun i _ => Nat.cast_nonneg _)

/-- **Lower comparison.** If the polynomial of the part `i` has degree at most `e i` in the basis
of falling factorials and `H = ∑ i ∈ S, e i` is at most `t / 2`, then the sum of the upper
comparison is at least `exp (-(H ^ 2 / t) - H ^ 2 / (2 * r))` times its bound. -/
theorem le_sum_finsuppAntidiag_prod_sum_descFactorial (hS : S.Nonempty) (t D : ℕ)
    (γ : ι → ℕ → ℕ) (e : ι → ℕ) (hγ : ∀ i ∈ S, ∀ d, e i < d → γ i d = 0)
    (h : 2 * ∑ i ∈ S, e i ≤ t) :
    Real.exp (-(((∑ i ∈ S, e i : ℕ) : ℝ) ^ 2 / t) -
        ((∑ i ∈ S, e i : ℕ) : ℝ) ^ 2 / (2 * S.card)) *
      ((S.card).multichoose t *
        ∏ i ∈ S, ∑ d ∈ range D, (γ i d : ℝ) * ((d ! : ℝ) * ((t : ℝ) / S.card) ^ d)) ≤
      ((∑ M ∈ S.finsuppAntidiag t, ∏ i ∈ S, ∑ d ∈ range D, γ i d * (M i).descFactorial d : ℕ) :
        ℝ) := by
  simp_rw [prod_sum_range]
  rw [sum_comm, mul_sum, mul_sum, Nat.cast_sum (S.pi fun _ => range D)]
  refine sum_le_sum fun q _ => ?_
  rw [← mul_sum, Nat.cast_mul, Nat.cast_prod, mul_left_comm _ (∏ i ∈ S, (γ i _ : ℝ)),
    mul_left_comm _ (∏ i ∈ S, (γ i _ : ℝ))]
  by_cases hq : ∀ i ∈ S, (if h : i ∈ S then q i h else 0) ≤ e i
  · have hH : ∑ i ∈ S, (if h : i ∈ S then q i h else (0 : ℕ)) ≤ ∑ i ∈ S, e i :=
      sum_le_sum (N := ℕ) hq
    have hH' : ((∑ i ∈ S, (if h : i ∈ S then q i h else (0 : ℕ)) : ℕ) : ℝ) ≤
        (∑ i ∈ S, e i : ℕ) := Nat.cast_le.2 hH
    refine mul_le_mul_of_nonneg_left (le_trans ?_
      (le_sum_finsuppAntidiag_prod_descFactorial hS t _ (by omega)))
      (prod_nonneg fun i _ => Nat.cast_nonneg _)
    gcongr
  · push Not at hq
    obtain ⟨i, hi, hlt⟩ := hq
    rw [prod_eq_zero hi (by exact_mod_cast hγ i hi _ hlt), zero_mul, zero_mul]

/-- **Lower comparison for linear forms.** If at most `t / 2` of the linear forms `a i * z + b i`
are not constant, the sum over the weak compositions `M` of `t` of `∏ i ∈ S, (a i * M i + b i)`
is at least `exp (-(c ^ 2 / t) - c ^ 2 / (2 * r))` times the number of compositions times
`∏ i ∈ S, (a i * (t / r) + b i)`, where `c` is the number of nonconstant forms. -/
theorem le_sum_finsuppAntidiag_prod_linear (hS : S.Nonempty) (t : ℕ) (a b : ι → ℕ)
    (h : 2 * (S.filter fun i => a i ≠ 0).card ≤ t) :
    Real.exp (-(((S.filter fun i => a i ≠ 0).card : ℝ) ^ 2 / t) -
        ((S.filter fun i => a i ≠ 0).card : ℝ) ^ 2 / (2 * S.card)) *
      ((S.card).multichoose t * ∏ i ∈ S, ((a i : ℝ) * ((t : ℝ) / S.card) + b i)) ≤
      ((∑ M ∈ S.finsuppAntidiag t, ∏ i ∈ S, (a i * M i + b i) : ℕ) : ℝ) := by
  have he : ∑ i ∈ S, (if a i ≠ 0 then 1 else 0) = (S.filter fun i => a i ≠ 0).card :=
    (card_filter _ _).symm
  have key := le_sum_finsuppAntidiag_prod_sum_descFactorial hS t 2
    (fun i d => if d = 0 then b i else if d = 1 then a i else 0)
    (fun i => if a i ≠ 0 then 1 else 0)
    (fun i _ d hd => by
      by_cases ha : a i = 0 <;> simp only [ha, ne_eq, not_true_eq_false, not_false_eq_true,
        ite_true, ite_false] at hd <;> split_ifs <;> first | rfl | omega)
    (by rw [he]; exact h)
  rw [he] at key
  simpa [sum_range_succ, add_comm, mul_comm] using key

/-- **Upper comparison for products of two linear forms.** The sum over the weak compositions
`M` of `t` of `∏ i ∈ S, (a₁ i * M i + b₁ i) * (a₂ i * M i + b₂ i)` is at most the number of
compositions times the product of the geometric moments
`(a₁ i * G + b₁ i) * (a₂ i * G + b₂ i) + a₁ i * a₂ i * (G ^ 2 + G)`, where `G = t / r`. -/
theorem sum_finsuppAntidiag_prod_linear_mul_linear_le (hS : S.Nonempty) (t : ℕ)
    (a₁ b₁ a₂ b₂ : ι → ℕ) :
    ((∑ M ∈ S.finsuppAntidiag t, ∏ i ∈ S, (a₁ i * M i + b₁ i) * (a₂ i * M i + b₂ i) : ℕ) : ℝ) ≤
      (S.card).multichoose t * ∏ i ∈ S,
        (((a₁ i : ℝ) * ((t : ℝ) / S.card) + b₁ i) * ((a₂ i : ℝ) * ((t : ℝ) / S.card) + b₂ i) +
          a₁ i * a₂ i * (((t : ℝ) / S.card) ^ 2 + (t : ℝ) / S.card)) := by
  have key := sum_finsuppAntidiag_prod_sum_descFactorial_le hS t 3 fun i d =>
    if d = 0 then b₁ i * b₂ i else if d = 1 then a₁ i * a₂ i + a₁ i * b₂ i + a₂ i * b₁ i
    else a₁ i * a₂ i
  have hz (i : ι) (z : ℕ) : (a₁ i * z + b₁ i) * (a₂ i * z + b₂ i) =
      ∑ d ∈ range 3, (if d = 0 then b₁ i * b₂ i else
        if d = 1 then a₁ i * a₂ i + a₁ i * b₂ i + a₂ i * b₁ i else a₁ i * a₂ i) *
          z.descFactorial d := by
    rcases z with _ | z
    · simp [sum_range_succ]
    · simp [sum_range_succ, Nat.descFactorial_succ]
      ring
  simp only [hz]
  refine key.trans (le_of_eq ?_)
  congr 1
  refine prod_congr rfl fun i _ => ?_
  simp [sum_range_succ]
  ring

end Finset
