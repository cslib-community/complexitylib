/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity

/-!
# The Bonami Lemma

A real function `f` on the cube has *degree at most `k`* when `f ∈ BitString.lowDegree ℝ ι k`,
equivalently when its Fourier coefficients on the sets of more than `k` coordinates vanish
(`BitString.mem_lowDegree_iff_fourierCoeff_eq_zero`). The **Bonami Lemma** says that low-degree
functions of uniformly random bits are *reasonable*: if `f` has degree at most `k`, then
`𝔼 f ^ 4 ≤ 9 ^ k (𝔼 f ^ 2) ^ 2`, that is, `‖f‖_4 ≤ √3 ^ k ‖f‖_2`
(`BitString.expect_pow_four_le`) [Bonami1970] [O'Donnell, Section 9.1][ODonnell2014]. More
generally `‖f‖_q ≤ √(q - 1) ^ k ‖f‖_2` for every `q ≥ 2`
(`BitString.lpNorm_le_sqrt_pow_mul_lpNorm_two`) [O'Donnell, Theorem 9.21][ODonnell2014].

The proof follows O'Donnell's derivation of Theorem 9.21 from the `(2, q)`-Hypercontractivity
Theorem, rather than his induction on the number of coordinates for the case `q = 4`. With
`c = √(q - 1)`, the function `g` with coefficients `c ^ |S| f̂(S)` satisfies `T_{1/c} g = f`, so
`‖f‖_q ≤ ‖g‖_2` (`BitString.lpNorm_noiseOp_le_lpNorm_two`), and `‖g‖_2 ^ 2` is
`∑_S c ^ (2 |S|) f̂(S) ^ 2 ≤ c ^ (2 k) ‖f‖_2 ^ 2` by Parseval's identity.

## Main results

* `Cslib.BitString.lpNorm_le_sqrt_pow_mul_lpNorm_two`,
  `Cslib.BitString.lpNorm_le_sqrt_pow_mul_lpNorm_two_of_fourierCoeff_eq_zero`:
  `‖f‖_q ≤ √(q - 1) ^ k ‖f‖_2` for `f` of degree at most `k`.
* `Cslib.BitString.expect_pow_four_le`,
  `Cslib.BitString.expect_pow_four_le_of_fourierCoeff_eq_zero`: the Bonami Lemma.

## References

* [A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p(G)`*][Bonami1970]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Low-degree functions are hypercontractive**, Fourier-coefficient form: if the Fourier
coefficients of `f` vanish above degree `k`, then `‖f‖_q ≤ √(q - 1) ^ k ‖f‖_2` for every `q ≥ 2`
[O'Donnell, Theorem 9.21][ODonnell2014]. -/
theorem lpNorm_le_sqrt_pow_mul_lpNorm_two_of_fourierCoeff_eq_zero {q : ℝ} (hq : 2 ≤ q) {k : ℕ}
    {f : (ι → Bool) → ℝ} (hf : ∀ S : Finset ι, k < #S → fourierCoeff f S = 0) :
    lpNorm q f ≤ √(q - 1) ^ k * lpNorm 2 f := by
  set c := √(q - 1)
  have hc : 0 < c := Real.sqrt_pos.2 (by linarith)
  have hc1 : 1 ≤ c := Real.one_le_sqrt.2 (by linarith)
  -- the function with coefficients `c ^ |S| f̂(S)`, which `T_{1/c}` takes to `f`
  set g : (ι → Bool) → ℝ := fun x => ∑ S, c ^ #S * fourierCoeff f S * chi ℝ S x
  have hg (S : Finset ι) : fourierCoeff g S = c ^ #S * fourierCoeff f S :=
    fourierCoeff_sum_mul_chi _ S
  have hTg : noiseOp c⁻¹ g = f := fourierCoeff_injective <| funext fun S => by
    rw [fourierCoeff_noiseOp, hg, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc.ne', one_pow,
      one_mul]
  calc lpNorm q f = lpNorm q (noiseOp c⁻¹ g) := by rw [hTg]
    _ ≤ lpNorm 2 g := lpNorm_noiseOp_le_lpNorm_two hq (inv_nonneg.2 hc.le) le_rfl g
    _ ≤ c ^ k * lpNorm 2 f := by
      refine (pow_le_pow_iff_left₀ (lpNorm_nonneg _ _)
        (mul_nonneg (pow_nonneg hc.le k) (lpNorm_nonneg _ _)) two_ne_zero).1 ?_
      rw [mul_pow, lpNorm_two_sq, lpNorm_two_sq, expect_sq_eq_sum_fourierCoeff_sq,
        expect_sq_eq_sum_fourierCoeff_sq, mul_sum]
      refine sum_le_sum fun S _ => ?_
      rw [hg, mul_pow]
      by_cases hS : k < #S
      · rw [hf S hS, zero_pow two_ne_zero, mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (pow_nonneg hc.le _) (pow_le_pow_right₀ hc1 (not_lt.1 hS)) 2)
          (sq_nonneg _)

/-- **Low-degree functions are hypercontractive**: if `f` has degree at most `k`, then
`‖f‖_q ≤ √(q - 1) ^ k ‖f‖_2` for every `q ≥ 2` [O'Donnell, Theorem 9.21][ODonnell2014]. -/
theorem lpNorm_le_sqrt_pow_mul_lpNorm_two {q : ℝ} (hq : 2 ≤ q) {k : ℕ} {f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι k) :
    lpNorm q f ≤ √(q - 1) ^ k * lpNorm 2 f :=
  lpNorm_le_sqrt_pow_mul_lpNorm_two_of_fourierCoeff_eq_zero hq
    (mem_lowDegree_iff_fourierCoeff_eq_zero.1 hf)

/-- **The Bonami Lemma**: if `f` has degree at most `k`, then `𝔼 f ^ 4 ≤ 9 ^ k (𝔼 f ^ 2) ^ 2`,
that is, `‖f‖_4 ≤ √3 ^ k ‖f‖_2` [Bonami1970] [O'Donnell, Section 9.1][ODonnell2014]. -/
theorem expect_pow_four_le {k : ℕ} {f : (ι → Bool) → ℝ}
    (hf : f ∈ lowDegree ℝ ι k) :
    𝔼 x, f x ^ 4 ≤ 9 ^ k * (𝔼 x, f x ^ 2) ^ 2 := by
  have h := lpNorm_le_sqrt_pow_mul_lpNorm_two (by norm_num : (2 : ℝ) ≤ 4) hf
  have h4 := pow_le_pow_left₀ (lpNorm_nonneg _ _) h 4
  have h9 : (√(4 - 1) ^ k) ^ 4 = (9 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, show (4 : ℝ) - 1 = 3 by norm_num,
      show √3 ^ 4 = (√3 ^ 2) ^ 2 by ring, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [mul_pow, h9, show lpNorm 2 f ^ 4 = (lpNorm 2 f ^ 2) ^ 2 by ring, lpNorm_two_sq,
    ← Real.rpow_natCast, Nat.cast_ofNat, lpNorm_rpow (by norm_num)] at h4
  simpa only [Real.rpow_ofNat, Even.pow_abs (by decide : Even 4)] using h4

/-- **The Bonami Lemma**, Fourier-coefficient form: if the Fourier coefficients of `f` vanish above
degree `k`, then `𝔼 f ^ 4 ≤ 9 ^ k (𝔼 f ^ 2) ^ 2` [Bonami1970]
[O'Donnell, Section 9.1][ODonnell2014]. -/
theorem expect_pow_four_le_of_fourierCoeff_eq_zero {k : ℕ} {f : (ι → Bool) → ℝ}
    (hf : ∀ S : Finset ι, k < #S → fourierCoeff f S = 0) :
    𝔼 x, f x ^ 4 ≤ 9 ^ k * (𝔼 x, f x ^ 2) ^ 2 :=
  expect_pow_four_le (mem_lowDegree_iff_fourierCoeff_eq_zero.2 hf)

end Cslib.BitString
