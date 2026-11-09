/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Hamming distance in the Fourier basis

Read Boolean functions `f g : (ι → Bool) → Bool` as the functions `F = (-1) ^ f` and
`G = (-1) ^ g` with values `±1`. Where `f` and `g` agree, `F - G` vanishes, and where they differ
`(F - G) ^ 2 = 4`, so the relative Hamming distance is a quarter of the mean of `(F - G) ^ 2`
(`BitString.expect_sq_signVal_sub_signVal`). By Parseval's identity it is a quarter of the squared
Euclidean distance between the Fourier coefficients,
`d_H(f, g) / 2 ^ n = 1 / 4 ∑_S (F̂(S) - Ĝ(S)) ^ 2`
(`BitString.hammingDist_div_eq_sum_fourierCoeff_sub_sq`) [O'Donnell, Section 1.4][ODonnell2014].

Smoothing both functions by the noise operator `T_ρ` before comparing them gives the *noise
distance* `D_ρ(f, g) = 1 / 4 𝔼 (T_ρ F - T_ρ G) ^ 2` (`BitString.noiseDist`). The noise operator
damps the coefficient on `S` by `ρ ^ |S|`, so `D_ρ(f, g) = 1 / 4 ∑_S ρ ^ (2 |S|) (F̂(S) - Ĝ(S)) ^ 2`
(`BitString.noiseDist_eq_sum`), the noise stability of `F - G` at `ρ ^ 2` up to the factor `1 / 4`
(`BitString.noiseDist_eq_noiseStability`). At `ρ = 1` it is the relative Hamming distance
(`BitString.noiseDist_one`), and it shrinks as `|ρ|` decreases
(`BitString.noiseDist_mono`), so on `|ρ| ≤ 1` noise contracts the relative Hamming distance
(`BitString.noiseDist_le_hammingDist_div`). High-degree disagreements are damped most: two
distinct parities on sets of size `k` are at relative Hamming distance `1 / 2`, but at noise
distance `ρ ^ (2 k) / 2` (`BitString.noiseDist_parityOn`).

The damped coefficients `ρ ^ |S| F̂(S) / 2` are a point of the Euclidean space indexed by the sets
of coordinates (`BitString.noiseEmbedding`), and `√D_ρ` is the Euclidean distance between the
points of `f` and `g` (`BitString.dist_noiseEmbedding`). Hence `√D_ρ` satisfies the triangle
inequality (`BitString.sqrt_noiseDist_triangle`), and for `ρ ≠ 0` it separates Boolean functions
(`BitString.noiseDist_eq_zero_iff`), since a function is determined by its Fourier coefficients.
So `√D_ρ` is a metric on Boolean functions for every `ρ ≠ 0` (`BitString.noiseMetricSpace`); for
`ρ = 1` this is the square root of the relative Hamming distance, which is therefore a Euclidean
metric. The noise distance is an average over a probability distribution only for `|ρ| ≤ 1`,
but the algebraic statements hold for every real `ρ`.

## Main definitions

* `Cslib.BitString.noiseDist`: the noise distance `D_ρ` between Boolean functions.
* `Cslib.BitString.noiseEmbedding`: the damped Fourier coefficients, as a point of Euclidean space.
* `Cslib.BitString.noiseMetricSpace`: the metric `√D_ρ`, for `ρ ≠ 0`.

## Main results

* `Cslib.BitString.hammingDist_div_eq_sum_fourierCoeff_sub_sq`: the relative Hamming distance is a
  quarter of the squared distance between the Fourier coefficients.
* `Cslib.BitString.noiseDist_eq_sum`, `Cslib.BitString.noiseDist_eq_noiseStability`: the Fourier
  formula for the noise distance.
* `Cslib.BitString.noiseDist_one`, `Cslib.BitString.noiseDist_mono`,
  `Cslib.BitString.noiseDist_le_hammingDist_div`: noise contracts the relative Hamming distance.
* `Cslib.BitString.noiseDist_parityOn`: the noise distance between two distinct parities.
* `Cslib.BitString.dist_noiseEmbedding`, `Cslib.BitString.sqrt_noiseDist_triangle`,
  `Cslib.BitString.noiseDist_eq_zero_iff`: `√D_ρ` is a Euclidean metric.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Hamming distance and the Fourier coefficients -/

/-- The mean squared difference of two Boolean functions read as signs is four times their
relative Hamming distance. -/
theorem expect_sq_signVal_sub_signVal (f g : (ι → Bool) → Bool) :
    𝔼 x, (signVal (f x) - signVal (g x)) ^ 2 = 4 * (hammingDist f g / 2 ^ Fintype.card ι) := by
  simp only [sq_signVal_sub_signVal, expect_sub_distrib, ← mul_expect,
    expect_signVal_mul_signVal, Fintype.expect_const]
  ring

/-- **The relative Hamming distance in the Fourier basis**: it is a quarter of the squared
Euclidean distance between the Fourier coefficients of the two functions read as signs,
`d_H(f, g) / 2 ^ n = 1 / 4 ∑_S (F̂(S) - Ĝ(S)) ^ 2`, by Parseval's identity for `F - G`
[O'Donnell, Section 1.4][ODonnell2014]. -/
theorem hammingDist_div_eq_sum_fourierCoeff_sub_sq (f g : (ι → Bool) → Bool) :
    (hammingDist f g : ℝ) / 2 ^ Fintype.card ι =
      1 / 4 * ∑ S, (fourierCoeff (fun x => signVal (f x)) S -
        fourierCoeff (fun x => signVal (g x)) S) ^ 2 := by
  have h := expect_sq_signVal_sub_signVal f g
  rw [expect_sq_eq_sum_fourierCoeff_sq] at h
  simp only [fourierCoeff_sub] at h
  rw [h]
  ring

/-! ### The noise distance -/

/-- The **noise distance** `D_ρ(f, g)` between two Boolean functions: a quarter of the mean
squared difference of `T_ρ F` and `T_ρ G`, for `F` and `G` the functions read as signs and `T_ρ`
the noise operator. For `|ρ| ≤ 1` it compares `f` and `g` after averaging each over the strings
`ρ`-correlated with the input. -/
noncomputable def noiseDist (ρ : ℝ) (f g : (ι → Bool) → Bool) : ℝ :=
  𝔼 x, (noiseOp ρ (fun y => signVal (f y)) x - noiseOp ρ (fun y => signVal (g y)) x) ^ 2 / 4

/-- The noise distance is a quarter of the noise stability of `F - G` at `ρ ^ 2`. -/
theorem noiseDist_eq_noiseStability (ρ : ℝ) (f g : (ι → Bool) → Bool) :
    noiseDist ρ f g =
      noiseStability (ρ ^ 2) (fun x => signVal (f x) - signVal (g x)) / 4 := by
  rw [noiseDist, ← expect_div]
  simp only [← noiseOp_sub]
  rw [expect_sq_eq_sum_fourierCoeff_sq, noiseStability_eq_sum]
  congr 1
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_noiseOp]
  ring

/-- **The Fourier formula for the noise distance**:
`D_ρ(f, g) = 1 / 4 ∑_S ρ ^ (2 |S|) (F̂(S) - Ĝ(S)) ^ 2`. -/
theorem noiseDist_eq_sum (ρ : ℝ) (f g : (ι → Bool) → Bool) :
    noiseDist ρ f g = 1 / 4 * ∑ S, ρ ^ (2 * #S) *
      (fourierCoeff (fun x => signVal (f x)) S - fourierCoeff (fun x => signVal (g x)) S) ^ 2 := by
  rw [noiseDist_eq_noiseStability, noiseStability_eq_sum, div_eq_mul_one_div, mul_comm]
  congr 1
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_sub, pow_mul]

/-- **Without noise, the noise distance is the relative Hamming distance.** -/
theorem noiseDist_one (f g : (ι → Bool) → Bool) :
    noiseDist 1 f g = hammingDist f g / 2 ^ Fintype.card ι := by
  rw [noiseDist_eq_sum, hammingDist_div_eq_sum_fourierCoeff_sub_sq]
  simp only [one_pow, one_mul]

/-- With full noise, the noise distance compares only the means. -/
theorem noiseDist_zero (f g : (ι → Bool) → Bool) :
    noiseDist 0 f g = (𝔼 x, signVal (f x) - 𝔼 x, signVal (g x)) ^ 2 / 4 := by
  rw [noiseDist_eq_noiseStability, zero_pow two_ne_zero, noiseStability_zero, expect_sub_distrib]

/-- The noise distance is nonnegative. -/
theorem noiseDist_nonneg (ρ : ℝ) (f g : (ι → Bool) → Bool) : 0 ≤ noiseDist ρ f g :=
  expect_nonneg fun _ _ => div_nonneg (sq_nonneg _) zero_le_four

/-- The noise distance is symmetric. -/
theorem noiseDist_comm (ρ : ℝ) (f g : (ι → Bool) → Bool) : noiseDist ρ f g = noiseDist ρ g f := by
  simp only [noiseDist, ← neg_sub (noiseOp ρ (fun y => signVal (f y)) _), neg_sq]

/-- A Boolean function is at noise distance zero from itself. -/
@[simp] theorem noiseDist_self (ρ : ℝ) (f : (ι → Bool) → Bool) : noiseDist ρ f f = 0 := by
  simp [noiseDist]

/-- **The noise distance grows with `|ρ|`.** -/
theorem noiseDist_mono {ρ σ : ℝ} (h : |ρ| ≤ |σ|) (f g : (ι → Bool) → Bool) :
    noiseDist ρ f g ≤ noiseDist σ f g := by
  simp only [noiseDist_eq_noiseStability]
  exact div_le_div_of_nonneg_right
    (noiseStability_mono (sq_nonneg ρ) (sq_le_sq.2 h) _) zero_le_four

/-- **Noise contracts the relative Hamming distance**: for `|ρ| ≤ 1`, the noise distance is at
most the relative Hamming distance. -/
theorem noiseDist_le_hammingDist_div {ρ : ℝ} (h : |ρ| ≤ 1) (f g : (ι → Bool) → Bool) :
    noiseDist ρ f g ≤ hammingDist f g / 2 ^ Fintype.card ι := by
  rw [← noiseDist_one]
  exact noiseDist_mono (h.trans_eq abs_one.symm) f g

/-- **Two distinct parities** on sets `S` and `T` are at noise distance
`(ρ ^ (2 |S|) + ρ ^ (2 |T|)) / 4`: all their Fourier weight sits on `S` and `T`. -/
theorem noiseDist_parityOn (ρ : ℝ) {S T : Finset ι} (h : S ≠ T) :
    noiseDist ρ (parityOn S) (parityOn T) = (ρ ^ (2 * #S) + ρ ^ (2 * #T)) / 4 := by
  have hterm (U : Finset ι) : ρ ^ (2 * #U) *
      ((if U = S then (1 : ℝ) else 0) - if U = T then 1 else 0) ^ 2 =
      (if U = S then ρ ^ (2 * #S) else 0) + if U = T then ρ ^ (2 * #T) else 0 := by
    by_cases hS : U = S <;> by_cases hT : U = T <;> simp_all
  rw [noiseDist_eq_sum]
  simp only [fourierCoeff_signVal_parityOn, hterm, sum_add_distrib, sum_ite_eq', mem_univ,
    ite_true]
  ring

/-! ### The Euclidean embedding -/

/-- The point of a Boolean function in the Euclidean space indexed by the sets of coordinates:
its Fourier coefficients, read as signs, damped by `ρ ^ |S|` and halved. -/
noncomputable def noiseEmbedding (ρ : ℝ) (f : (ι → Bool) → Bool) : EuclideanSpace ℝ (Finset ι) :=
  WithLp.toLp 2 fun S => ρ ^ #S * fourierCoeff (fun x => signVal (f x)) S / 2

/-- The noise distance is the squared Euclidean distance between the embedded functions. -/
theorem noiseDist_eq_dist_sq (ρ : ℝ) (f g : (ι → Bool) → Bool) :
    noiseDist ρ f g = dist (noiseEmbedding ρ f) (noiseEmbedding ρ g) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, noiseDist_eq_sum, mul_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [Real.dist_eq, sq_abs, noiseEmbedding, noiseEmbedding, pow_mul]
  ring

/-- **The square root of the noise distance is a Euclidean distance.** -/
theorem dist_noiseEmbedding (ρ : ℝ) (f g : (ι → Bool) → Bool) :
    dist (noiseEmbedding ρ f) (noiseEmbedding ρ g) = √(noiseDist ρ f g) := by
  rw [noiseDist_eq_dist_sq, Real.sqrt_sq dist_nonneg]

/-- **The triangle inequality for the square root of the noise distance.** -/
theorem sqrt_noiseDist_triangle (ρ : ℝ) (f g h : (ι → Bool) → Bool) :
    √(noiseDist ρ f h) ≤ √(noiseDist ρ f g) + √(noiseDist ρ g h) := by
  simp only [← dist_noiseEmbedding]
  exact dist_triangle _ _ _

/-- For `ρ ≠ 0` the embedding is injective: the damping is invertible, a function is determined
by its Fourier coefficients, and a Boolean function by its signs. -/
theorem noiseEmbedding_injective {ρ : ℝ} (hρ : ρ ≠ 0) :
    Function.Injective (noiseEmbedding (ι := ι) ρ) := fun f g h => by
  have hcoeff : fourierCoeff (fun x => signVal (f x)) = fourierCoeff fun x => signVal (g x) :=
    funext fun S => by
      have hS := congrFun (congrArg WithLp.ofLp h) S
      simp only [noiseEmbedding] at hS
      exact mul_left_cancel₀ (pow_ne_zero _ hρ) (by linarith)
  funext x
  have hx := congrFun (fourierCoeff_injective hcoeff) x
  cases hf : f x <;> cases hg : g x <;> simp_all <;> norm_num at hx

/-- **For `ρ ≠ 0`, the noise distance separates Boolean functions.** -/
theorem noiseDist_eq_zero_iff {ρ : ℝ} (hρ : ρ ≠ 0) {f g : (ι → Bool) → Bool} :
    noiseDist ρ f g = 0 ↔ f = g := by
  rw [noiseDist_eq_dist_sq, sq_eq_zero_iff, dist_eq_zero]
  exact (noiseEmbedding_injective hρ).eq_iff

/-- **The square root of the noise distance is a metric** on Boolean functions, for `ρ ≠ 0`:
the metric induced by the Euclidean embedding. For `ρ = 1` it is the square root of the relative
Hamming distance. This is a definition, not an instance, since it depends on `ρ`. -/
noncomputable abbrev noiseMetricSpace {ρ : ℝ} (hρ : ρ ≠ 0) : MetricSpace ((ι → Bool) → Bool) :=
  MetricSpace.induced (noiseEmbedding ρ) (noiseEmbedding_injective hρ) inferInstance

/-- The distance in `noiseMetricSpace` is the square root `√D_ρ` of the noise distance. -/
theorem noiseMetricSpace_dist {ρ : ℝ} (hρ : ρ ≠ 0) (f g : (ι → Bool) → Bool) :
    (noiseMetricSpace hρ).dist f g = √(noiseDist ρ f g) :=
  dist_noiseEmbedding ρ f g

end Cslib.BitString
