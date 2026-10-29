/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Fourier
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

## Main results

* `Cslib.BitString.fourierCoeff_bitVal_of_nonempty`: the coefficients of the `0/1` reading at a
  nonempty set are `-1 / 2` times those of the `±1` reading.
* `Cslib.BitString.sum_fourierCoeff_bitVal_sq`: the Fourier weight of the `0/1` reading above a
  level is a quarter of that of the `±1` reading.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [M. Braverman, *Polylogarithmic independence fools `AC⁰` circuits*][Braverman2010]
-/

public section

namespace Cslib.BitString

open Finset

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

end Cslib.BitString
