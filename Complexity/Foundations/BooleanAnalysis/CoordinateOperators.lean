/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Influence
import Complexity.Foundations.BooleanAnalysis.Decomposition
import Complexity.Foundations.Data.Finset.SymmDiff
import Mathlib.Tactic.Ring

/-!
# Coordinate expectations and Laplacians

The *expectation over coordinate `i`* of a real function on the cube is its average over bit `i`,
`Eᵢ f x = (f (x with xᵢ = false) + f (x with xᵢ = true)) / 2` (`BitString.coordExpect`), and the
*coordinate Laplacian* is `Lᵢ f = f - Eᵢ f` (`BitString.coordLaplacian`)
[O'Donnell, Definitions 2.23 and 2.25][ODonnell2014]. The Laplacian is `χ_{i}` times the
derivative in `i` (`BitString.coordLaplacian_eq_chi_mul_derivative`); in Fourier terms `Eᵢ`
keeps the coefficients on the sets avoiding `i` and `Lᵢ` those on the sets containing `i`
(`BitString.fourierCoeff_coordExpect`, `BitString.fourierCoeff_coordLaplacian`), and
`⟨f, Lᵢ f⟩ = Infᵢ[f]` (`BitString.expect_mul_coordLaplacian`); averaging over `i` preserves the
expectation (`BitString.expect_coordExpect`)
[O'Donnell, Propositions 2.24 and 2.26][ODonnell2014].

The *Laplacian* `L = ∑ᵢ Lᵢ` (`BitString.laplacian`) multiplies the coefficient on `S` by `|S|`
(`BitString.fourierCoeff_laplacian`), so `⟨f, L f⟩ = I[f]` (`BitString.expect_mul_laplacian`)
[O'Donnell, Definition 2.36 and Proposition 2.37][ODonnell2014].

## Main definitions

* `Cslib.BitString.coordExpect`, `Cslib.BitString.coordLaplacian`: the expectation and the
  Laplacian along one coordinate.
* `Cslib.BitString.laplacian`: the Laplacian.

## Main results

* `Cslib.BitString.coordLaplacian_eq_chi_mul_derivative`: `Lᵢ f = χ_{i} Dᵢ f`.
* `Cslib.BitString.fourierCoeff_coordExpect`, `Cslib.BitString.fourierCoeff_coordLaplacian`,
  `Cslib.BitString.fourierCoeff_laplacian`: the Fourier coefficients of the three operators.
* `Cslib.BitString.expect_mul_coordLaplacian`, `Cslib.BitString.expect_mul_laplacian`:
  `⟨f, Lᵢ f⟩ = Infᵢ[f]` and `⟨f, L f⟩ = I[f]`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- The expectation `Eᵢ f` of `f` over coordinate `i`: its average over bit `i`
[O'Donnell, Definition 2.23][ODonnell2014]. -/
@[expose] noncomputable def coordExpect (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  (f (update x i false) + f (update x i true)) / 2

/-- The coordinate Laplacian `Lᵢ f = f - Eᵢ f` [O'Donnell, Definition 2.25][ODonnell2014]. -/
@[expose] noncomputable def coordLaplacian (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  f x - coordExpect i f x

/-- **The coordinate Laplacian is `χ_{i}` times the derivative**: `Lᵢ f = χ_{i} Dᵢ f`
[O'Donnell, Proposition 2.26][ODonnell2014]. -/
theorem coordLaplacian_eq_chi_mul_derivative (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    coordLaplacian i f x = chi ℝ {i} x * derivative i f x :=
  sub_eq_of_eq_add' (eq_add_chi_mul_derivative i f x)

/-- A function is the sum of its coordinate expectation and its coordinate Laplacian. -/
theorem coordExpect_add_coordLaplacian (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    coordExpect i f x + coordLaplacian i f x = f x :=
  add_sub_cancel _ _

variable [Fintype ι]

/-- **The Fourier coefficients of a coordinate Laplacian**: `Lᵢ f` keeps the coefficients of `f`
on the sets containing `i` [O'Donnell, Proposition 2.26][ODonnell2014]. -/
theorem fourierCoeff_coordLaplacian (i : ι) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (coordLaplacian i f) S = if i ∈ S then fourierCoeff f S else 0 := by
  rw [funext (coordLaplacian_eq_chi_mul_derivative i f), fourierCoeff_chi_mul,
    fourierCoeff_derivative, symmDiff_comm, symmDiff_singleton_eq]
  by_cases hi : i ∈ S <;> simp [hi]

/-- **The Fourier coefficients of a coordinate expectation**: `Eᵢ f` keeps the coefficients of `f`
on the sets avoiding `i` [O'Donnell, Proposition 2.24][ODonnell2014]. -/
theorem fourierCoeff_coordExpect (i : ι) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (coordExpect i f) S = if i ∈ S then 0 else fourierCoeff f S := by
  have h : coordExpect i f = fun x => f x - coordLaplacian i f x :=
    funext fun x => by rw [coordLaplacian]; ring
  rw [h, fourierCoeff_sub, fourierCoeff_coordLaplacian]
  split_ifs <;> ring

/-- Averaging over coordinate `i` preserves the expectation: `𝔼 Eᵢ f = 𝔼 f`. -/
theorem expect_coordExpect (i : ι) (f : (ι → Bool) → ℝ) :
    𝔼 x, coordExpect i f x = 𝔼 x, f x := by
  simp only [coordExpect, div_eq_mul_inv, ← expect_mul, expect_update_false_add_update_true]
  ring

/-- **The coordinate Laplacian and the influence**: `⟨f, Lᵢ f⟩ = Infᵢ[f]`
[O'Donnell, Proposition 2.26][ODonnell2014]. -/
theorem expect_mul_coordLaplacian (i : ι) (f : (ι → Bool) → ℝ) :
    𝔼 x, f x * coordLaplacian i f x = influence i f := by
  rw [expect_mul_eq_sum_fourierCoeff_mul, influence_eq_sum_fourierCoeff_sq, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_coordLaplacian]
  split_ifs <;> ring

/-- The Laplacian `L f = ∑ᵢ Lᵢ f` [O'Donnell, Definition 2.36][ODonnell2014]. -/
@[expose] noncomputable def laplacian (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, coordLaplacian i f x

/-- **The Fourier coefficients of the Laplacian**: `L f` multiplies the coefficient of `f` on `S`
by `|S|` [O'Donnell, Proposition 2.37][ODonnell2014]. -/
theorem fourierCoeff_laplacian (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (laplacian f) S = #S * fourierCoeff f S := by
  have h : fourierCoeff (laplacian f) S = ∑ i, fourierCoeff (coordLaplacian i f) S := by
    simp only [laplacian, fourierCoeff, sum_mul]
    rw [expect_sum_comm]
  rw [h]
  simp only [fourierCoeff_coordLaplacian]
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]

/-- **The Laplacian and the total influence**: `⟨f, L f⟩ = I[f]`
[O'Donnell, Proposition 2.37][ODonnell2014]. -/
theorem expect_mul_laplacian (f : (ι → Bool) → ℝ) :
    𝔼 x, f x * laplacian f x = totalInfluence f := by
  rw [expect_mul_eq_sum_fourierCoeff_mul, totalInfluence_eq_sum_card_mul_fourierCoeff_sq]
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_laplacian]
  ring

end Cslib.BitString
