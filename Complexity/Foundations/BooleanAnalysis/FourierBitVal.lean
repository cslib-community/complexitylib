/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Degree
import Complexity.Foundations.BooleanAnalysis.SignApproximation
import Mathlib.Algebra.BigOperators.Field

/-!
# Fourier coefficients of Boolean functions read as bits

A Boolean function `F` can be read as a real function with values `0` and `1`
(`fun x => bitVal ℝ (F x)`) or with values `±1` (`fun x => signVal (F x)`). Since
`signVal b = 1 - 2 bitVal b`, the two readings differ by an affine change, so away from the empty
set their Fourier coefficients differ by the factor `-1 / 2`
(`Cslib.BitString.fourierCoeff_bitVal_of_nonempty`). In particular the Fourier weight above any
level of the `0/1` reading is a quarter of that of the `±1` reading
(`Cslib.BitString.sum_fourierCoeff_bitVal_sq`). Fourier tail bounds such as the
[Linial, Mansour and Nisan][LinialMansourNisan1993] bound are usually stated for the `±1` reading,
while their applications, such as [Braverman][Braverman2010], approximate the `0/1` reading.

Cutting the Fourier expansion of a function at level `t` gives a function of degree at most `t`
whose squared `L²` distance to the original is the Fourier weight above `t`
(`Cslib.BitString.exists_mem_lowDegree_expect_sq_sub_eq`, from Parseval's identity in the form
`Cslib.BitString.expect_sq_sub_sum_mul_chi`), so a Fourier tail bound on a Boolean
function yields a low-degree `L²` approximation of its `0/1` reading
(`Cslib.BitString.exists_mem_lowDegree_expect_sq_bitVal_sub_eq`).

## Main results

* `Cslib.BitString.fourierCoeff_bitVal_of_nonempty`: the coefficients of the `0/1` reading at a
  nonempty set are `-1 / 2` times those of the `±1` reading.
* `Cslib.BitString.sum_fourierCoeff_bitVal_sq`: the Fourier weight of the `0/1` reading above a
  level is a quarter of that of the `±1` reading.
* `Cslib.BitString.exists_mem_lowDegree_expect_sq_sub_eq`,
  `Cslib.BitString.exists_mem_lowDegree_expect_sq_bitVal_sub_eq`: Fourier truncation.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [M. Braverman, *Polylogarithmic independence fools `AC⁰` circuits*][Braverman2010]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At a nonempty set, the Fourier coefficient of a Boolean function read as `0` or `1` is `-1 / 2`
times its coefficient when read as a sign. -/
theorem fourierCoeff_bitVal_of_nonempty (F : (ι → Bool) → Bool) {S : Finset ι}
    (hS : S.Nonempty) :
    fourierCoeff (fun x => bitVal ℝ (F x)) S = -fourierCoeff (fun x => signVal (F x)) S / 2 := by
  have h : (fun x => bitVal ℝ (F x)) = fun x => (1 / 2 : ℝ) - 1 / 2 * signVal (F x) := by
    funext x
    rw [signVal_eq_one_sub_two_mul_bitVal]
    ring
  rw [h, fourierCoeff_sub (fun _ => (1 / 2 : ℝ)) fun x => 1 / 2 * signVal (F x),
    fourierCoeff_const, fourierCoeff_const_mul]
  simp only [hS.ne_empty, ↓reduceIte]
  ring

/-- **Normalizing Fourier tails**: above any level `t`, the Fourier weight of a Boolean function
read as `0` or `1` is a quarter of its weight when read as a sign. -/
theorem sum_fourierCoeff_bitVal_sq (F : (ι → Bool) → Bool) (t : ℕ) :
    ∑ S with t < #S, fourierCoeff (fun x => bitVal ℝ (F x)) S ^ 2 =
      (∑ S with t < #S, fourierCoeff (fun x => signVal (F x)) S ^ 2) / 4 := by
  rw [sum_div]
  refine sum_congr rfl fun S hS => ?_
  have hS : S.Nonempty := card_pos.1 (Nat.zero_lt_of_lt (mem_filter.1 hS).2)
  rw [fourierCoeff_bitVal_of_nonempty F hS]
  ring

/-- **Fourier truncation**: cutting the Fourier expansion of `f` at level `t` gives a function of
degree at most `t` whose squared `L²` distance to `f` is the Fourier weight of `f` above `t`. -/
theorem exists_mem_lowDegree_expect_sq_sub_eq (f : (ι → Bool) → ℝ) (t : ℕ) :
    ∃ g ∈ lowDegree ℝ ι t, 𝔼 x, (f x - g x) ^ 2 = ∑ S with t < #S, fourierCoeff f S ^ 2 := by
  refine ⟨∑ S with #S ≤ t, fourierCoeff f S • chi ℝ S, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun S hS =>
      Submodule.smul_mem _ _ (lowDegree_mono (mem_filter.1 hS).2 (chi_mem_lowDegree S))
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [expect_sq_sub_sum_mul_chi, compl_filter]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
      zero_add, not_le]

/-- **Fourier truncation of a Boolean function**: the `0/1` reading of `F` is approximated by a
function of degree at most `t` with squared `L²` error a quarter of the Fourier weight of the `±1`
reading of `F` above `t`. -/
theorem exists_mem_lowDegree_expect_sq_bitVal_sub_eq (F : (ι → Bool) → Bool) (t : ℕ) :
    ∃ g ∈ lowDegree ℝ ι t, 𝔼 x, (bitVal ℝ (F x) - g x) ^ 2 =
      (∑ S with t < #S, fourierCoeff (fun x => signVal (F x)) S ^ 2) / 4 := by
  obtain ⟨g, hg, h⟩ := exists_mem_lowDegree_expect_sq_sub_eq (fun x => bitVal ℝ (F x)) t
  exact ⟨g, hg, h.trans (sum_fourierCoeff_bitVal_sq F t)⟩

end Cslib.BitString
