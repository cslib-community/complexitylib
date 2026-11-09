/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Data.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Fourier coefficients of restrictions

Fixing the coordinates outside a set `J` to the bits of `z` turns `f` into the function
`x ↦ f (J.piecewise x z)` of the coordinates in `J`. Its Fourier coefficient on `S` collects the
coefficients of `f` on the sets `U` with `U ∩ J = S`, twisted by the characters of `U \ J` at `z`
(`BitString.fourierCoeff_piecewise`). Averaged over a uniformly random `z`, the twists are
orthogonal, so the expected squared coefficient on `S` is the weight of `f` on the sets meeting
`J` in `S` (`BitString.expect_fourierCoeff_piecewise_sq`), and the expected weight of the
restriction on sets of at least `m` coordinates is the weight of `f` on the sets meeting `J` in at
least `m` coordinates (`BitString.expect_sum_fourierCoeff_piecewise_sq`)
[O'Donnell, Section 3.3][ODonnell2014].

Averaging over the fixed bits instead of over their squares averages the twists away: the average
of `f` over the coordinates outside `J` keeps the coefficients of `f` on the subsets of `J` and
kills the others (`BitString.fourierCoeff_expect_piecewise`), so it is the part of the Fourier
expansion of `f` on the subsets of `J` (`BitString.expect_piecewise_eq_sum`), at mean square
distance from `f` the weight of `f` outside the subsets of `J`
(`BitString.expect_sub_expect_piecewise_sq`).

## Main results

* `Cslib.BitString.fourierCoeff_piecewise`: the coefficients of a restriction.
* `Cslib.BitString.expect_sum_fourierCoeff_piecewise_sq`: the expected weight of a restriction
  above a degree.
* `Cslib.BitString.fourierCoeff_expect_piecewise`, `Cslib.BitString.expect_piecewise_eq_sum`: the
  average over the coordinates outside a set.
* `Cslib.BitString.expect_sub_expect_piecewise_sq`: the mean square distance of a function from
  that average is its Fourier weight outside the subsets of the set.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- A character at a point with the coordinates outside `J` replaced splits into the characters
of the parts of `U` inside and outside `J`. -/
theorem chi_piecewise {R : Type*} [CommRing R] (U J : Finset ι) (x z : ι → Bool) :
    chi R U (J.piecewise x z) = chi R (U ∩ J) x * chi R (U \ J) z := by
  rw [chi, ← prod_filter_mul_prod_filter_not U (· ∈ J), filter_mem_eq_inter, ← sdiff_eq_filter,
    chi, chi]
  congr 1
  · exact prod_congr rfl fun i hi => by rw [piecewise_eq_of_mem _ _ _ (mem_inter.1 hi).2]
  · exact prod_congr rfl fun i hi => by rw [piecewise_eq_of_notMem _ _ _ (mem_sdiff.1 hi).2]

variable [Fintype ι]

/-- **The Fourier coefficients of a restriction**: the coefficient on `S` sums the coefficients
of `f` on the sets meeting `J` in `S`, each multiplied by the character of its part outside `J`
at `z`. -/
theorem fourierCoeff_piecewise (f : (ι → Bool) → ℝ) (J : Finset ι) (z : ι → Bool)
    (S : Finset ι) :
    fourierCoeff (fun x => f (J.piecewise x z)) S =
      ∑ U with U ∩ J = S, fourierCoeff f U * chi ℝ (U \ J) z := by
  have h (x : ι → Bool) : f (J.piecewise x z) =
      ∑ U, (fourierCoeff f U * chi ℝ (U \ J) z) * chi ℝ (U ∩ J) x := by
    rw [← sum_fourierCoeff_mul_chi f (J.piecewise x z)]
    exact sum_congr rfl fun U _ => by rw [chi_piecewise]; ring
  rw [fourierCoeff]
  simp only [h, sum_mul, mul_assoc]
  rw [expect_sum_comm, sum_filter]
  refine sum_congr rfl fun U _ => ?_
  simp only [← mul_expect, expect_chi_mul_chi]
  split_ifs <;> simp

/-- Averaged over the fixed bits, the squared coefficient of a restriction on `S` is the weight of
`f` on the sets meeting `J` in `S`. -/
theorem expect_fourierCoeff_piecewise_sq (f : (ι → Bool) → ℝ) (J S : Finset ι) :
    𝔼 z, fourierCoeff (fun x => f (J.piecewise x z)) S ^ 2 =
      ∑ U with U ∩ J = S, fourierCoeff f U ^ 2 := by
  have key (U V : Finset ι) :
      𝔼 z, fourierCoeff f U * chi ℝ (U \ J) z * (fourierCoeff f V * chi ℝ (V \ J) z) =
        fourierCoeff f U * fourierCoeff f V * if U \ J = V \ J then 1 else 0 := by
    rw [← expect_chi_mul_chi, mul_expect]
    exact expect_congr rfl fun z _ => by ring
  simp only [fourierCoeff_piecewise, sq, sum_mul_sum, expect_sum_comm, key]
  refine sum_congr rfl fun U hU => ?_
  rw [sum_eq_single_of_mem U hU fun V hV hVU => ?_]
  · simp
  · -- two sets meeting `J` in the same part differ outside `J`
    rw [mem_filter] at hU hV
    have hne : U \ J ≠ V \ J := fun h => hVU (by
      rw [← sdiff_union_inter V J, ← sdiff_union_inter U J, h, hU.2, hV.2])
    simp [hne]

/-- **The expected weight of a restriction above a degree**: averaged over the fixed bits, the
Fourier weight of the restriction on sets of at least `m` coordinates is the weight of `f` on the
sets meeting `J` in at least `m` coordinates. -/
theorem expect_sum_fourierCoeff_piecewise_sq (f : (ι → Bool) → ℝ) (J : Finset ι) (m : ℕ) :
    𝔼 z, ∑ S with m ≤ #S, fourierCoeff (fun x => f (J.piecewise x z)) S ^ 2 =
      ∑ U with m ≤ #(U ∩ J), fourierCoeff f U ^ 2 := by
  rw [expect_sum_comm]
  simp only [expect_fourierCoeff_piecewise_sq]
  calc ∑ S with m ≤ #S, ∑ U with U ∩ J = S, fourierCoeff f U ^ 2
      = ∑ S with m ≤ #S, ∑ U, if U ∩ J = S then fourierCoeff f U ^ 2 else 0 := by
        simp only [sum_filter]
    _ = ∑ U, ∑ S with m ≤ #S, if U ∩ J = S then fourierCoeff f U ^ 2 else 0 := sum_comm
    _ = ∑ U with m ≤ #(U ∩ J), fourierCoeff f U ^ 2 := by
        rw [sum_filter]
        refine sum_congr rfl fun U _ => ?_
        rw [sum_ite_eq]
        simp

/-! ### Averaging out the coordinates outside a set -/

/-- **The Fourier coefficients of the average over the coordinates outside `J`**: averaging keeps
the coefficients on the subsets of `J` and kills the others. -/
theorem fourierCoeff_expect_piecewise (f : (ι → Bool) → ℝ) (J S : Finset ι) :
    fourierCoeff (fun x => 𝔼 z, f (J.piecewise x z)) S =
      if S ⊆ J then fourierCoeff f S else 0 := by
  have h : fourierCoeff (fun x => 𝔼 z, f (J.piecewise x z)) S =
      𝔼 z, fourierCoeff (fun x => f (J.piecewise x z)) S := by
    simp only [fourierCoeff, expect_mul]
    exact expect_comm _ _ _
  simp only [h, fourierCoeff_piecewise]
  rw [expect_sum_comm]
  simp only [← mul_expect, expect_chi, sdiff_eq_empty_iff_subset, mul_ite, mul_one, mul_zero]
  split_ifs with hS
  · have hSmem : S ∈ ({U | U ∩ J = S} : Finset (Finset ι)) :=
      mem_filter.2 ⟨mem_univ S, inter_eq_left.2 hS⟩
    rw [sum_eq_single_of_mem S hSmem fun U hU hUS => ?_, ite_eq_left hS]
    -- another set meeting `J` in `S` has elements outside `J`
    rw [mem_filter] at hU
    exact ite_eq_right fun hUJ => hUS (by rw [← hU.2, inter_eq_left.2 hUJ])
  · refine sum_eq_zero fun U hU => ?_
    rw [mem_filter] at hU
    exact ite_eq_right fun hUJ => hS (by rw [← hU.2]; exact inter_subset_right)

/-- **The average over the coordinates outside `J`** is the part of the Fourier expansion on the
subsets of `J`. -/
theorem expect_piecewise_eq_sum (f : (ι → Bool) → ℝ) (J : Finset ι) (x : ι → Bool) :
    𝔼 z, f (J.piecewise x z) = ∑ S with S ⊆ J, fourierCoeff f S * chi ℝ S x := by
  rw [← sum_fourierCoeff_mul_chi (fun x => 𝔼 z, f (J.piecewise x z)) x, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_expect_piecewise]
  split_ifs <;> simp

/-- The mean square distance from `f` to its average over the coordinates outside `J` is the
Fourier weight of `f` outside the subsets of `J`. -/
theorem expect_sub_expect_piecewise_sq (f : (ι → Bool) → ℝ) (J : Finset ι) :
    𝔼 x, (f x - 𝔼 z, f (J.piecewise x z)) ^ 2 = ∑ S with ¬S ⊆ J, fourierCoeff f S ^ 2 := by
  rw [expect_sq_eq_sum_fourierCoeff_sq, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_sub, fourierCoeff_expect_piecewise]
  split_ifs <;> simp

end Cslib.BitString
