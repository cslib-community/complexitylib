/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.PolynomialThreshold
public import Mathlib.Analysis.Complex.Exponential
import Complexity.Foundations.BooleanAnalysis.LowDegreeMoments
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The low-degree Fourier weight of polynomial threshold functions

A polynomial threshold function `f` of degree at most `k` (`BitString.IsPTF k f`) has Fourier
weight `W^{≤k}[f] = ∑_{|S| ≤ k} f̂(S) ^ 2 ≥ e ^ (-2 k)` on the levels up to `k`
(`BitString.IsPTF.exp_neg_two_mul_le_sum_fourierCoeff_sq`): this is the **Gotsman–Linial
Theorem** [GotsmanLinial1994] [O'Donnell, Theorem 5.9][ODonnell2014].

Following O'Donnell, write `f = sgn p` with `p` of degree at most `k`. Then
`‖p‖_1 = 𝔼 f p = ∑_{|S| ≤ k} f̂(S) p̂(S) ≤ √(W^{≤k}[f]) ‖p‖_2` by Plancherel's identity and
Cauchy–Schwarz, and `‖p‖_2 ≤ e ^ k ‖p‖_1` by the `L^1`–`L^2` comparison for low-degree functions
(`BitString.lpNorm_two_le_exp_mul_lpNorm_one`, [O'Donnell, Theorem 9.22][ODonnell2014]). The bound
`e ^ (-2 k)` cannot be improved beyond `2 ^ (1 - k)` [O'Donnell, Exercise 5.11][ODonnell2014].

## Main results

* `Cslib.BitString.IsPTF.exp_neg_two_mul_le_sum_fourierCoeff_sq`: the Gotsman–Linial Theorem.

## References

* [C. Gotsman, N. Linial, *Spectral properties of threshold functions*][GotsmanLinial1994]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Gotsman–Linial Theorem**: a polynomial threshold function `f` of degree at most `k`,
read as signs, has Fourier weight at least `e ^ (-2 k)` on the sets of at most `k` coordinates
[GotsmanLinial1994] [O'Donnell, Theorem 5.9][ODonnell2014]. -/
theorem IsPTF.exp_neg_two_mul_le_sum_fourierCoeff_sq {k : ℕ} {f : (ι → Bool) → Bool}
    (hf : IsPTF k f) :
    Real.exp (-(2 * k)) ≤ ∑ S with #S ≤ k, fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  classical
  obtain ⟨p, hpdeg, hpos⟩ := isPTF_iff.1 hf
  set F : (ι → Bool) → ℝ := fun x => signVal (f x) with hF
  set W := ∑ S with #S ≤ k, fourierCoeff F S ^ 2 with hW
  set m := 𝔼 x, p x ^ 2 with hm
  -- `|p| = F p`
  have habs (x : ι → Bool) : |p x| = F x * p x := by
    calc |p x| = |F x| * |p x| := by rw [hF, abs_signVal, one_mul]
      _ = |F x * p x| := (abs_mul _ _).symm
      _ = F x * p x := abs_of_pos (hpos x)
  -- `‖p‖₁ = ⟨F, p⟩ = ∑_{|S| ≤ k} F̂(S) p̂(S) ≤ √W √m`
  have hinner : 𝔼 x, |p x| = ∑ S with #S ≤ k, fourierCoeff F S * fourierCoeff p S := by
    rw [expect_congr rfl fun x _ => habs x, expect_mul_eq_sum_fourierCoeff_mul, sum_filter]
    refine sum_congr rfl fun S _ => ?_
    split_ifs with hS
    · rfl
    · rw [hpdeg S (by omega), mul_zero]
  have hpm : m = ∑ S with #S ≤ k, fourierCoeff p S ^ 2 := by
    rw [hm, expect_sq_eq_sum_fourierCoeff_sq, sum_filter]
    refine sum_congr rfl fun S _ => ?_
    split_ifs with hS
    · rfl
    · rw [hpdeg S (by omega)]; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq ({S | #S ≤ k} : Finset (Finset ι))
    (fun S => fourierCoeff F S) (fun S => fourierCoeff p S)
  rw [← hinner, ← hW, ← hpm] at hcs
  -- `m > 0`, since `p` vanishes nowhere
  have hmpos : 0 < m := Finset.expect_pos (fun x _ => by
    have : p x ≠ 0 := fun h => by have := hpos x; rw [h, mul_zero] at this; exact lt_irrefl _ this
    positivity) univ_nonempty
  -- Theorem 9.22 with `p = 1`: `√m ≤ e^k ‖p‖₁`
  have h22 := lpNorm_two_le_exp_mul_lpNorm_one (mem_lowDegree_iff_fourierCoeff_eq_zero.2 hpdeg)
  rw [lpNorm_two, ← hm, lpNorm_one] at h22
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h22 2
  rw [Real.sq_sqrt hmpos.le] at hsq
  have hX : Real.exp (2 * k) = Real.exp k ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have h1 : m ≤ Real.exp (2 * k) * (W * m) := by
    calc m ≤ (Real.exp k * 𝔼 x, |p x|) ^ 2 := hsq
      _ = Real.exp (2 * k) * (𝔼 x, |p x|) ^ 2 := by rw [hX]; ring
      _ ≤ Real.exp (2 * k) * (W * m) := mul_le_mul_of_nonneg_left hcs (by positivity)
  have h2 : 1 ≤ Real.exp (2 * k) * W := by
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_right hlt hmpos
    linarith
  have hee : Real.exp (-(2 * k)) * Real.exp (2 * k) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(2 * k))).le
  rw [mul_one, ← mul_assoc, hee, one_mul] at h3
  exact h3

end Cslib.BitString
