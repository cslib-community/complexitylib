/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Influence
public import Mathlib.Analysis.Real.Sqrt
import Complexity.Foundations.BooleanAnalysis.Decomposition
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.NormNum

/-!
# Influences of monotone Boolean functions

The derivative in `i` of a Boolean function read as signs takes the values `0` and `±1`, so its
square is its absolute value (`BitString.sq_derivative_signVal`). The coefficient of a function on
`{i}` is the average of its derivative in `i`, so for every Boolean function it is at most the
influence of `i` in absolute value (`BitString.abs_fourierCoeff_singleton_le_influence`). With the
order `false < true` on bits and the signs `signVal false = 1`, `signVal true = -1`, the derivative
of a monotone function is nonnegative, so its influences are its degree-one coefficients
(`BitString.influence_eq_fourierCoeff_singleton_of_monotone`)
[O'Donnell, Section 2.2][ODonnell2014]; for an antitone function they are their negatives.

The degree-one coefficients carry at most the variance
(`BitString.sum_fourierCoeff_singleton_sq_le`), so by the Cauchy–Schwarz inequality a monotone
or antitone Boolean function on `n` coordinates with variance `σ²` has total influence at most
`√(n σ²)` (`BitString.totalInfluence_le_sqrt_card_mul_of_monotone`), in particular at most `√n`
(`BitString.totalInfluence_le_sqrt_card_of_monotone`) [O'Donnell, Exercise 2.23][ODonnell2014].

## Main results

* `Cslib.BitString.derivative_signVal_nonneg_of_monotone`,
  `Cslib.BitString.derivative_signVal_nonpos_of_antitone`: the sign of the derivatives of a
  monotone or antitone function.
* `Cslib.BitString.abs_fourierCoeff_singleton_le_influence`: a degree-one coefficient is at most
  the influence in absolute value.
* `Cslib.BitString.influence_eq_fourierCoeff_singleton_of_monotone`,
  `Cslib.BitString.influence_eq_neg_fourierCoeff_singleton_of_antitone`: the influences of a
  monotone or antitone function are its degree-one coefficients, up to sign.
* `Cslib.BitString.fourierCoeff_singleton_nonneg_of_monotone`,
  `Cslib.BitString.fourierCoeff_singleton_nonpos_of_antitone`: the sign of the degree-one
  coefficients of a monotone or antitone function.
* `Cslib.BitString.sum_fourierCoeff_singleton_sq_le`: the degree-one weight is at most the
  variance.
* `Cslib.BitString.sum_influence_sq_le_of_monotone`: the squared influences of a monotone function
  sum to at most its variance.
* `Cslib.BitString.totalInfluence_le_sqrt_card_mul_of_monotone`,
  `Cslib.BitString.totalInfluence_le_sqrt_card_of_monotone`,
  `Cslib.BitString.totalInfluence_le_sqrt_card_mul_of_antitone`,
  `Cslib.BitString.totalInfluence_le_sqrt_card_of_antitone`: monotone and antitone functions have
  total influence at most `√(n σ²) ≤ √n`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι] {f : (ι → Bool) → Bool}

/-- The derivative of a monotone Boolean function read as signs is nonnegative: raising bit `i`
from `false` (sign `1`) to `true` (sign `-1`) can only raise the value. -/
theorem derivative_signVal_nonneg_of_monotone (hf : Monotone f) (i : ι) (x : ι → Bool) :
    0 ≤ derivative i (fun x => signVal (f x)) x := by
  have h := hf (update_le_update_iff'.2 (Bool.false_le true) : update x i false ≤ update x i true)
  simp only [derivative]
  revert h
  cases f (update x i false) <;> cases f (update x i true) <;> norm_num

/-- The derivative of an antitone Boolean function read as signs is nonpositive. -/
theorem derivative_signVal_nonpos_of_antitone (hf : Antitone f) (i : ι) (x : ι → Bool) :
    derivative i (fun x => signVal (f x)) x ≤ 0 := by
  have h := hf (update_le_update_iff'.2 (Bool.false_le true) : update x i false ≤ update x i true)
  simp only [derivative]
  revert h
  cases f (update x i false) <;> cases f (update x i true) <;> norm_num

variable [Fintype ι]

/-- The coefficient of a Boolean function, read as signs, on `{i}` is at most the influence of `i`
in absolute value. -/
theorem abs_fourierCoeff_singleton_le_influence (f : (ι → Bool) → Bool) (i : ι) :
    |fourierCoeff (fun x => signVal (f x)) {i}| ≤ influence i (fun x => signVal (f x)) := by
  rw [fourierCoeff_singleton_eq_expect_derivative, influence]
  simp only [sq_derivative_signVal]
  exact abs_expect_le _ _

/-- **The influences of a monotone Boolean function are its degree-one coefficients**: for a
monotone function read as signs, the influence of `i` is the coefficient on `{i}`
[O'Donnell, Section 2.2][ODonnell2014]. -/
theorem influence_eq_fourierCoeff_singleton_of_monotone (hf : Monotone f) (i : ι) :
    influence i (fun x => signVal (f x)) = fourierCoeff (fun x => signVal (f x)) {i} := by
  rw [fourierCoeff_singleton_eq_expect_derivative, influence]
  exact expect_congr rfl fun x _ => by
    rw [sq_derivative_signVal, abs_of_nonneg (derivative_signVal_nonneg_of_monotone hf i x)]

/-- The influences of an antitone Boolean function read as signs are the negatives of its
degree-one coefficients. -/
theorem influence_eq_neg_fourierCoeff_singleton_of_antitone (hf : Antitone f) (i : ι) :
    influence i (fun x => signVal (f x)) = -fourierCoeff (fun x => signVal (f x)) {i} := by
  rw [fourierCoeff_singleton_eq_expect_derivative, influence, ← expect_neg_distrib]
  exact expect_congr rfl fun x _ => by
    rw [sq_derivative_signVal, abs_of_nonpos (derivative_signVal_nonpos_of_antitone hf i x)]

/-- A monotone Boolean function read as signs has nonnegative degree-one coefficients. -/
theorem fourierCoeff_singleton_nonneg_of_monotone (hf : Monotone f) (i : ι) :
    0 ≤ fourierCoeff (fun x => signVal (f x)) {i} :=
  influence_eq_fourierCoeff_singleton_of_monotone hf i ▸ influence_nonneg i _

/-- An antitone Boolean function read as signs has nonpositive degree-one coefficients. -/
theorem fourierCoeff_singleton_nonpos_of_antitone (hf : Antitone f) (i : ι) :
    fourierCoeff (fun x => signVal (f x)) {i} ≤ 0 := by
  have h := influence_nonneg i fun x => signVal (f x)
  rw [influence_eq_neg_fourierCoeff_singleton_of_antitone hf i] at h
  linarith

/-- **The degree-one weight is at most the variance**: the squared coefficients on the singletons
sum to at most the variance. -/
theorem sum_fourierCoeff_singleton_sq_le (g : (ι → Bool) → ℝ) :
    ∑ i, fourierCoeff g {i} ^ 2 ≤ 𝔼 x, (g x - 𝔼 y, g y) ^ 2 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
  calc ∑ i, fourierCoeff g {i} ^ 2 = ∑ S ∈ univ.image (fun i : ι => {i}), fourierCoeff g S ^ 2 :=
        by rw [sum_image fun _ _ _ _ hab => singleton_injective hab]
    _ ≤ ∑ S with S ≠ ∅, fourierCoeff g S ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg (fun S hS => ?_) fun _ _ _ => sq_nonneg _
        obtain ⟨i, -, rfl⟩ := mem_image.1 hS
        exact mem_filter.2 ⟨mem_univ _, singleton_ne_empty i⟩

/-- By Cauchy–Schwarz, the degree-one coefficients sum to at most `√(n σ²)` in absolute value. -/
private theorem abs_sum_fourierCoeff_singleton_le (g : (ι → Bool) → ℝ) :
    |∑ i, fourierCoeff g {i}| ≤ √(Fintype.card ι * 𝔼 x, (g x - 𝔼 y, g y) ^ 2) := by
  refine Real.abs_le_sqrt ?_
  calc (∑ i, fourierCoeff g {i}) ^ 2 ≤ #(univ : Finset ι) * ∑ i, fourierCoeff g {i} ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ Fintype.card ι * 𝔼 x, (g x - 𝔼 y, g y) ^ 2 := by
        rw [card_univ]
        exact mul_le_mul_of_nonneg_left (sum_fourierCoeff_singleton_sq_le g) (Nat.cast_nonneg _)

/-- For a monotone Boolean function read as signs, the squared influences sum to at most the
variance. -/
theorem sum_influence_sq_le_of_monotone (hf : Monotone f) :
    ∑ i, influence i (fun x => signVal (f x)) ^ 2 ≤
      𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 := by
  simp only [influence_eq_fourierCoeff_singleton_of_monotone hf]
  exact sum_fourierCoeff_singleton_sq_le _

/-- **Monotone functions have total influence at most `√(n σ²)`**: a monotone Boolean function on
`n` coordinates, read as signs with variance `σ²`, has total influence at most `√(n σ²)`,
refining [O'Donnell, Exercise 2.23][ODonnell2014]. -/
theorem totalInfluence_le_sqrt_card_mul_of_monotone (hf : Monotone f) :
    totalInfluence (fun x => signVal (f x)) ≤
      √(Fintype.card ι * 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) := by
  have h : totalInfluence (fun x => signVal (f x)) =
      ∑ i, fourierCoeff (fun x => signVal (f x)) {i} :=
    sum_congr rfl fun i _ => influence_eq_fourierCoeff_singleton_of_monotone hf i
  rw [h]
  exact (le_abs_self _).trans (abs_sum_fourierCoeff_singleton_le _)

/-- Antitone functions have total influence at most `√(n σ²)`: an antitone Boolean function on `n`
coordinates, read as signs with variance `σ²`, has total influence at most `√(n σ²)`. -/
theorem totalInfluence_le_sqrt_card_mul_of_antitone (hf : Antitone f) :
    totalInfluence (fun x => signVal (f x)) ≤
      √(Fintype.card ι * 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) := by
  have h : totalInfluence (fun x => signVal (f x)) =
      -∑ i, fourierCoeff (fun x => signVal (f x)) {i} := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun i _ => influence_eq_neg_fourierCoeff_singleton_of_antitone hf i
  rw [h]
  exact (neg_le_abs _).trans (abs_sum_fourierCoeff_singleton_le _)

/-- **Monotone functions have total influence at most `√n`**: a monotone Boolean function on `n`
coordinates, read as signs, has total influence at most `√n`
[O'Donnell, Exercise 2.23][ODonnell2014]. -/
theorem totalInfluence_le_sqrt_card_of_monotone (hf : Monotone f) :
    totalInfluence (fun x => signVal (f x)) ≤ √(Fintype.card ι) :=
  (totalInfluence_le_sqrt_card_mul_of_monotone hf).trans <| Real.sqrt_le_sqrt <|
    mul_le_of_le_one_right (Nat.cast_nonneg _) (expect_sub_expect_sq_signVal_le_one f)

/-- Antitone functions have total influence at most `√n`: an antitone Boolean function on `n`
coordinates, read as signs, has total influence at most `√n`. -/
theorem totalInfluence_le_sqrt_card_of_antitone (hf : Antitone f) :
    totalInfluence (fun x => signVal (f x)) ≤ √(Fintype.card ι) :=
  (totalInfluence_le_sqrt_card_mul_of_antitone hf).trans <| Real.sqrt_le_sqrt <|
    mul_le_of_le_one_right (Nat.cast_nonneg _) (expect_sub_expect_sq_signVal_le_one f)

end Cslib.BitString
