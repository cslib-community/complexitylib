/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.FourierRestriction

/-!
# Fourier weight on the sets with a given part in a set of coordinates

For a set `J` of coordinates and a set `S`, the *bucket weight* of `S` in `J` is the Fourier weight
of `F` on the sets `U` with `U ∩ J = S` (`BitString.bucketWeight`). O'Donnell writes it
`W^{S | J̄} [F] = ∑_{T ⊆ J̄} F̂(S ∪ T)²` for `S ⊆ J`, where `J̄` is the complement of `J`
[O'Donnell, Definition 3.39][ODonnell2014]. The buckets of a fixed `J` partition the sets of
coordinates, so the bucket weights of distinct sets `S` add up to at most the total weight
(`BitString.sum_bucketWeight_le`), and the bucket of `U ∩ J` holds at least the weight of `U`
(`BitString.sq_fourierCoeff_le_bucketWeight`). For `J` the set of all coordinates the buckets are
single sets (`BitString.bucketWeight_univ`).

The bucket weight is the expected squared coefficient of the restriction of `F` fixing the
coordinates outside `J` at random (`BitString.expect_fourierCoeff_piecewise_sq`), hence the
expectation of `F (x, z) χ_S(x) F (y, z) χ_S(y)` for independent uniform `x`, `y`, `z`, where
`(x, z)` takes the coordinates in `J` from `x` and the others from `z`
(`BitString.bucketWeight_eq_expect_sample`), as in the proof of
[O'Donnell, Proposition 3.40][ODonnell2014]. With query
access to a Boolean function this lets one estimate any bucket weight by sampling: the basis of
the Goldreich–Levin and Kushilevitz–Mansour algorithms [GoldreichLevin1989]
[KushilevitzMansour1993].

## Main definitions

* `Cslib.BitString.bucketWeight`: the Fourier weight on the sets with a given part in `J`.

## Main results

* `Cslib.BitString.sum_bucketWeight_le`: the buckets of `J` partition the Fourier weight.
* `Cslib.BitString.sq_fourierCoeff_le_bucketWeight`: a bucket holds the weight of its sets.
* `Cslib.BitString.bucketWeight_eq_expect_sample`: the bucket weight as an expectation of samples.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [E. Kushilevitz and Y. Mansour, *Learning decision trees using the Fourier
  spectrum*][KushilevitzMansour1993]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The *bucket weight* of `S` in `J`: the Fourier weight of `F` on the sets `U` of coordinates
with `U ∩ J = S`, written `W^{S | J̄} [F]` by O'Donnell, where `J̄` is the complement of `J`. -/
noncomputable def bucketWeight (F : (ι → Bool) → ℝ) (J S : Finset ι) : ℝ :=
  ∑ U with U ∩ J = S, fourierCoeff F U ^ 2

/-- Every bucket weight is nonnegative. -/
theorem bucketWeight_nonneg (F : (ι → Bool) → ℝ) (J S : Finset ι) : 0 ≤ bucketWeight F J S :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- For `J` the set of all coordinates, the bucket of `S` is `S` alone. -/
@[simp] theorem bucketWeight_univ (F : (ι → Bool) → ℝ) (S : Finset ι) :
    bucketWeight F univ S = fourierCoeff F S ^ 2 := by
  simp [bucketWeight, filter_eq']

/-- The bucket of `U ∩ J` holds at least the weight of `U`. -/
theorem sq_fourierCoeff_le_bucketWeight (F : (ι → Bool) → ℝ) (J U : Finset ι) :
    fourierCoeff F U ^ 2 ≤ bucketWeight F J (U ∩ J) :=
  single_le_sum (f := fun V => fourierCoeff F V ^ 2) (fun _ _ => sq_nonneg _)
    (mem_filter.2 ⟨mem_univ U, rfl⟩)

/-- The buckets of `J` partition the sets of coordinates: the bucket weights of distinct sets add
up to at most the total Fourier weight. -/
theorem sum_bucketWeight_le (F : (ι → Bool) → ℝ) (J : Finset ι) (𝒮 : Finset (Finset ι)) :
    ∑ S ∈ 𝒮, bucketWeight F J S ≤ ∑ U, fourierCoeff F U ^ 2 := by
  calc ∑ S ∈ 𝒮, bucketWeight F J S
      = ∑ U, ∑ S ∈ 𝒮, if U ∩ J = S then fourierCoeff F U ^ 2 else 0 := by
        simp only [bucketWeight, sum_filter]
        exact sum_comm
    _ ≤ ∑ U, fourierCoeff F U ^ 2 := by
        refine sum_le_sum fun U _ => ?_
        rw [sum_ite_eq]
        split_ifs
        · exact le_rfl
        · exact sq_nonneg _

/-- The bucket weight is the expected squared coefficient of a random restriction. -/
theorem bucketWeight_eq_expect (F : (ι → Bool) → ℝ) (J S : Finset ι) :
    bucketWeight F J S = 𝔼 z, fourierCoeff (fun x => F (J.piecewise x z)) S ^ 2 :=
  (expect_fourierCoeff_piecewise_sq F J S).symm

/-- **Estimating a bucket weight by sampling**: the bucket weight of `S` in `J` is the expectation
of `F (x, z) χ_S(x) F (y, z) χ_S(y)` for independent uniform `x`, `y`, `z`, where `(x, z)` takes
the coordinates in `J` from `x` and the others from `z`, as in the proof of
[O'Donnell, Proposition 3.40][ODonnell2014]. -/
theorem bucketWeight_eq_expect_sample (F : (ι → Bool) → ℝ) (J S : Finset ι) :
    bucketWeight F J S = 𝔼 p : (ι → Bool) × (ι → Bool) × (ι → Bool),
      F (J.piecewise p.1 p.2.2) * chi ℝ S p.1 * (F (J.piecewise p.2.1 p.2.2) * chi ℝ S p.2.1) := by
  rw [bucketWeight_eq_expect, ← univ_product_univ, expect_product]
  simp only [← univ_product_univ, expect_product, fourierCoeff, sq, expect_mul_expect]
  conv_rhs => enter [2, x]; rw [expect_comm]
  conv_rhs => rw [expect_comm]

end Cslib.BitString
