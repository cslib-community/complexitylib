/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Linearity
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Affinity testing

A Boolean function on the cube is *affine* when it is a parity plus a constant,
`f x = b ^^ parityOn S x`. Bit strings add coordinatewise modulo two (`x + y`, through Mathlib's
Boolean ring structure on `Bool`) and single bits by exclusive or (`^^`). The affine functions
are exactly those with `f (x + y + z) = (f x ^^ f y ^^ f z)` for all `x`, `y`, `z`
(`BitString.exists_eq_xor_parityOn_iff`), or equivalently with
`f (x + y) = (f x ^^ f y ^^ f 0)` for all `x`, `y` (`BitString.exists_eq_xor_parityOn_iff_add`)
[O'Donnell, Exercise 1.29][ODonnell2014].

The *affinity test* queries `f` at independent uniformly random `x`, `y` and `z` and at
`x + y + z`, which is uniformly distributed as well (`BitString.expect_expect_expect_add_add`), and
accepts when `(f x ^^ f y ^^ f z) = f (x + y + z)`; `BitString.affinityAcceptance f` is the
probability that it accepts. Reading `f` as the function `F x = (-1) ^ f x`, the four-point
correlation `𝔼 F(x) F(y) F(z) F(x + y + z)` is `∑_S F̂(S)⁴`
(`BitString.expect_mul_mul_mul_eq_sum_fourierCoeff_pow_four`), by the convolution theorem applied
twice, so the test accepts with probability `1/2 + 1/2 ∑_S F̂(S)⁴`
(`BitString.affinityAcceptance_eq_sum_fourierCoeff_pow_four`). Affine functions pass with
probability one (`BitString.affinityAcceptance_xor_parityOn`). Conversely, a function passing with
probability at least `1 - ε` differs from some affine function on at most an `ε` fraction of the
inputs (`BitString.exists_hammingDist_xor_parityOn_le_of_le_affinityAcceptance`): by Parseval's
identity, `∑_S F̂(S)⁴ ≤ max_S F̂(S)² ≤ max_S |F̂(S)|`, and `|F̂(S)|` is one minus twice the
relative Hamming distance from `f` to the parity on `S` or to its negation
(`BitString.fourierCoeff_signVal_eq_signVal_mul`). This is the argument of the BLR test
(`BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance`) with fourth powers in place of
cubes, which is why it also finds negated parities.

The *anchored affinity test* reads `f` at uniformly random `x` and `y`, at `x + y`, and at the
fixed point `0`, and accepts when `(f x ^^ f y ^^ f 0) = f (x + y)`. It is the BLR test on
`x ↦ f x ^^ f 0` (`BitString.anchoredAffinityAcceptance_eq_blrAcceptance`), so it has the same
completeness and soundness (`BitString.anchoredAffinityAcceptance_xor_parityOn`,
`BitString.exists_hammingDist_xor_parityOn_le_of_le_anchoredAffinityAcceptance`).

## Main definitions

* `Cslib.BitString.affinityAcceptance`: the acceptance probability of the four-query affinity
  test with uniform queries.
* `Cslib.BitString.anchoredAffinityAcceptance`: the acceptance probability of the affinity test
  whose fourth query is the point `0`.

## Main results

* `Cslib.BitString.exists_eq_xor_parityOn_iff`, `Cslib.BitString.exists_eq_xor_parityOn_iff_add`:
  characterizations of the affine functions.
* `Cslib.BitString.expect_mul_mul_mul_eq_sum_fourierCoeff_pow_four`: the four-point correlation
  in terms of the Fourier coefficients.
* `Cslib.BitString.expect_expect_expect_add_add`: the fourth query `x + y + z` is uniform.
* `Cslib.BitString.affinityAcceptance_eq_sum_fourierCoeff_pow_four`: the acceptance probability
  in terms of the Fourier coefficients.
* `Cslib.BitString.affinityAcceptance_xor_parityOn`: completeness of the affinity test.
* `Cslib.BitString.fourierCoeff_signVal_eq_signVal_mul`: the Fourier coefficients measure the
  distance to the affine functions.
* `Cslib.BitString.exists_hammingDist_xor_parityOn_le_of_le_affinityAcceptance`: soundness of the
  affinity test.
* `Cslib.BitString.anchoredAffinityAcceptance_eq_blrAcceptance`,
  `Cslib.BitString.anchoredAffinityAcceptance_xor_parityOn`,
  `Cslib.BitString.exists_hammingDist_xor_parityOn_le_of_le_anchoredAffinityAcceptance`: the
  anchored test is the BLR test on a shifted function, with completeness and soundness.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*}

/-! ### Affine functions -/

/-- **The affine Boolean functions, through a fixed point**: a Boolean function satisfies
`f (x + y) = (f x ^^ f y ^^ f 0)` exactly when it is a parity plus a constant
[O'Donnell, Exercise 1.29(d)][ODonnell2014]. -/
theorem exists_eq_xor_parityOn_iff_add [Finite ι] {f : (ι → Bool) → Bool} :
    (∃ b S, f = fun x => b ^^ parityOn S x) ↔ ∀ x y, f (x + y) = (f x ^^ f y ^^ f 0) := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨b, S, rfl⟩ x y
    have h0 : parityOn S 0 = false := map_zero (parityOnAddMonoidHom S)
    simp only [parityOn_add, h0]
    cases b <;> cases parityOn S x <;> cases parityOn S y <;> rfl
  · have hlin (x y : ι → Bool) : (f (x + y) ^^ f 0) = ((f x ^^ f 0) ^^ (f y ^^ f 0)) := by
      rw [hf x y]
      cases f x <;> cases f y <;> cases f 0 <;> rfl
    obtain ⟨S, hS⟩ := BitString.exists_eq_parityOn_iff (f := fun x => f x ^^ f 0) |>.2 hlin
    refine ⟨f 0, S, funext fun x => ?_⟩
    have hx : (f x ^^ f 0) = parityOn S x := congr_fun hS x
    rw [← hx]
    cases f x <;> cases f 0 <;> rfl

/-- **The affine Boolean functions**: a Boolean function satisfies
`f (x + y + z) = (f x ^^ f y ^^ f z)` exactly when it is a parity plus a constant
[O'Donnell, Exercise 1.29(a)][ODonnell2014]. -/
theorem exists_eq_xor_parityOn_iff [Finite ι] {f : (ι → Bool) → Bool} :
    (∃ b S, f = fun x => b ^^ parityOn S x) ↔ ∀ x y z, f (x + y + z) = (f x ^^ f y ^^ f z) := by
  rw [exists_eq_xor_parityOn_iff_add]
  refine ⟨fun hf x y z => ?_, fun hf x y => by simpa only [add_zero] using hf x y 0⟩
  rw [hf, hf x y]
  cases f x <;> cases f y <;> cases f z <;> cases f 0 <;> rfl

variable [Fintype ι] [DecidableEq ι]

/-! ### The four-point correlation -/

/-- **The four-point correlation**: for independent uniformly random `x`, `y` and `z`,
`𝔼 F(x) F(y) F(z) F(x + y + z) = ∑_S F̂(S)⁴` [O'Donnell, Exercise 1.29(b)][ODonnell2014]. -/
theorem expect_mul_mul_mul_eq_sum_fourierCoeff_pow_four (F : (ι → Bool) → ℝ) :
    𝔼 x, 𝔼 y, 𝔼 z, F x * F y * F z * F (x + y + z) = ∑ S, fourierCoeff F S ^ 4 := by
  have h (x y : ι → Bool) : 𝔼 z, F x * F y * F z * F (x + y + z) =
      F x * (F y * convolution F F (x + y)) := by
    simp only [convolution, mul_expect, mul_assoc]
  simp only [h, ← mul_expect]
  change 𝔼 x, F x * convolution F (convolution F F) x = _
  rw [expect_mul_eq_sum_fourierCoeff_mul]
  simp only [fourierCoeff_convolution]
  exact sum_congr rfl fun S _ => by ring

/-- The fourth query `x + y + z` of the affinity test is uniformly distributed. -/
theorem expect_expect_expect_add_add {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (g : (ι → Bool) → M) : 𝔼 x, 𝔼 y, 𝔼 z, g (x + y + z) = 𝔼 w, g w := by
  have h (x y : ι → Bool) : 𝔼 z, g (x + y + z) = 𝔼 w, g w := Fintype.expect_add_left g (x + y)
  simp only [h, Fintype.expect_const]

/-! ### The affinity test -/

/-- The acceptance probability of the affinity test on `f`: the probability, over independent
uniformly random bit strings `x`, `y` and `z`, that `(f x ^^ f y ^^ f z) = f (x + y + z)`. Each of
the four queries is uniformly distributed (`expect_expect_expect_add_add`). -/
@[expose]
noncomputable def affinityAcceptance (f : (ι → Bool) → Bool) : ℝ :=
  𝔼 x, 𝔼 y, 𝔼 z, if (f x ^^ f y ^^ f z) = f (x + y + z) then 1 else 0

/-- **The acceptance probability of the affinity test**: reading `f` as signs, the test accepts
with probability `1/2 + 1/2 ∑_S F̂(S)⁴`. -/
theorem affinityAcceptance_eq_sum_fourierCoeff_pow_four (f : (ι → Bool) → Bool) :
    affinityAcceptance f = 1 / 2 + 1 / 2 * ∑ S, fourierCoeff (fun x => signVal (f x)) S ^ 4 := by
  have hind (a b c d : Bool) : (if (a ^^ b ^^ c) = d then (1 : ℝ) else 0) =
      1 / 2 + 1 / 2 * (signVal a * signVal b * signVal c * signVal d) := by
    cases a <;> cases b <;> cases c <;> cases d <;> norm_num
  rw [← expect_mul_mul_mul_eq_sum_fourierCoeff_pow_four]
  simp only [affinityAcceptance, hind, expect_add_distrib, ← mul_expect, Fintype.expect_const]

/-- **Completeness of the affinity test**: affine functions pass with probability one
[O'Donnell, Exercise 1.29(c)][ODonnell2014]. -/
theorem affinityAcceptance_xor_parityOn (b : Bool) (S : Finset ι) :
    affinityAcceptance (fun x => b ^^ parityOn S x) = 1 := by
  have h := (exists_eq_xor_parityOn_iff (f := fun x => b ^^ parityOn S x)).1 ⟨b, S, rfl⟩
  simp only [affinityAcceptance, h, ↓reduceIte, Fintype.expect_const]

/-- The Fourier coefficient on `S` of a Boolean function read as signs is `±1` times one minus
twice the relative Hamming distance from the function to the affine function `b ^^ parityOn S`,
with sign `(-1) ^ b`. -/
theorem fourierCoeff_signVal_eq_signVal_mul (f : (ι → Bool) → Bool) (b : Bool) (S : Finset ι) :
    fourierCoeff (fun x => signVal (f x)) S =
      signVal b * (1 - 2 * hammingDist f (fun x => b ^^ parityOn S x) / 2 ^ Fintype.card ι) := by
  rw [← expect_signVal_mul_signVal, mul_expect, fourierCoeff]
  refine expect_congr rfl fun x _ => ?_
  rw [chi_eq_signVal_parityOn, signVal_xor]
  linear_combination (signVal (f x) * signVal (parityOn S x)) * (signVal_mul_self b).symm

/-- **Soundness of the affinity test**: if the test accepts `f` with probability at least
`1 - ε`, then `f` differs from some affine function on at most an `ε` fraction of the inputs
[O'Donnell, Exercise 1.29(c)][ODonnell2014]. -/
theorem exists_hammingDist_xor_parityOn_le_of_le_affinityAcceptance {f : (ι → Bool) → Bool}
    {ε : ℝ} (h : 1 - ε ≤ affinityAcceptance f) :
    ∃ b S, (hammingDist f (fun x => b ^^ parityOn S x) : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  rw [affinityAcceptance_eq_sum_fourierCoeff_pow_four] at h
  set c := fourierCoeff fun x => signVal (f x)
  obtain ⟨S, -, hS⟩ := exists_max_image univ (fun S => c S ^ 2) univ_nonempty
  have hc : ∑ T, c T ^ 4 ≤ c S ^ 2 := calc
    ∑ T, c T ^ 4 ≤ ∑ T, c S ^ 2 * c T ^ 2 := sum_le_sum fun T _ => by
        rw [show c T ^ 4 = c T ^ 2 * c T ^ 2 by ring]
        exact mul_le_mul_of_nonneg_right (hS T (mem_univ T)) (sq_nonneg _)
    _ = c S ^ 2 := by rw [← mul_sum, sum_fourierCoeff_sq_signVal, mul_one]
  have hsq : c S ^ 2 ≤ |c S| := by
    rw [← sq_abs, sq]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_fourierCoeff_signVal_le_one f S)
  set b := decide (c S < 0)
  have hb : signVal b * c S = |c S| := by
    by_cases hneg : c S < 0
    · simp [b, hneg, abs_of_neg hneg]
    · simp [b, hneg, abs_of_nonneg (not_lt.1 hneg)]
  refine ⟨b, S, ?_⟩
  have key : c S = _ := fourierCoeff_signVal_eq_signVal_mul f b S
  have hd : signVal b * c S =
      1 - 2 * ((hammingDist f (fun x => b ^^ parityOn S x) : ℝ) / 2 ^ Fintype.card ι) := by
    rw [key, ← mul_assoc, signVal_mul_self, one_mul, mul_div_assoc]
  linarith

/-! ### The anchored affinity test -/

/-- The acceptance probability of the anchored affinity test on `f`: the probability, over
independent uniformly random bit strings `x` and `y`, that `(f x ^^ f y ^^ f 0) = f (x + y)`.
Three of the four queries are uniformly distributed and the fourth is the point `0`. -/
@[expose]
noncomputable def anchoredAffinityAcceptance (f : (ι → Bool) → Bool) : ℝ :=
  𝔼 x, 𝔼 y, if (f x ^^ f y ^^ f 0) = f (x + y) then 1 else 0

/-- The anchored affinity test on `f` is the BLR test on `x ↦ f x ^^ f 0`. -/
theorem anchoredAffinityAcceptance_eq_blrAcceptance (f : (ι → Bool) → Bool) :
    anchoredAffinityAcceptance f = blrAcceptance fun x => f x ^^ f 0 := by
  have h (x y : ι → Bool) : ((f x ^^ f y ^^ f 0) = f (x + y)) ↔
      (((f x ^^ f 0) ^^ (f y ^^ f 0)) = (f (x + y) ^^ f 0)) := by
    cases f x <;> cases f y <;> cases f 0 <;> cases f (x + y) <;> decide
  simp only [anchoredAffinityAcceptance, blrAcceptance, h]

/-- **Completeness of the anchored affinity test**: affine functions pass with probability one
[O'Donnell, Exercise 1.29(d)][ODonnell2014]. -/
theorem anchoredAffinityAcceptance_xor_parityOn (b : Bool) (S : Finset ι) :
    anchoredAffinityAcceptance (fun x => b ^^ parityOn S x) = 1 := by
  have h := (exists_eq_xor_parityOn_iff_add (f := fun x => b ^^ parityOn S x)).1 ⟨b, S, rfl⟩
  simp only [anchoredAffinityAcceptance, h, ↓reduceIte, Fintype.expect_const]

/-- **Soundness of the anchored affinity test**: if the test accepts `f` with probability at
least `1 - ε`, then `f` differs from some affine function on at most an `ε` fraction of the inputs
[O'Donnell, Exercise 1.29(d)][ODonnell2014]. -/
theorem exists_hammingDist_xor_parityOn_le_of_le_anchoredAffinityAcceptance
    {f : (ι → Bool) → Bool} {ε : ℝ} (h : 1 - ε ≤ anchoredAffinityAcceptance f) :
    ∃ b S, (hammingDist f (fun x => b ^^ parityOn S x) : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  rw [anchoredAffinityAcceptance_eq_blrAcceptance] at h
  obtain ⟨S, hS⟩ := exists_hammingDist_parityOn_le_of_le_blrAcceptance h
  refine ⟨f 0, S, ?_⟩
  have hdist : hammingDist f (fun x => f 0 ^^ parityOn S x) =
      hammingDist (fun x => f x ^^ f 0) (parityOn S) := by
    simp only [hammingDist]
    congr 1
    refine filter_congr fun x _ => ?_
    cases f x <;> cases f 0 <;> cases parityOn S x <;> decide
  rw [hdist]
  exact hS

end Cslib.BitString
