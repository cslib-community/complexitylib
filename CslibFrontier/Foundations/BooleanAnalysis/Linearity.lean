/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Convolution
public import CslibFrontier.Foundations.Data.BitString.Hamming
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Linearity testing

A Boolean function on the cube is *linear* when it turns sums into sums,
`f (x + y) = (f x ^^ f y)`, where bit strings add coordinatewise modulo two (`x + y`, through
Mathlib's Boolean ring structure on `Bool`) and single bits by exclusive or (`^^`). The linear
functions are exactly the parities (`BitString.exists_eq_parityOn_iff`, with `parityOn_add`).
Distinct parities differ on half of the inputs (`BitString.two_mul_hammingDist_parityOn`, from
`CslibFrontier.Foundations.Data.BitString.Hamming`), and a linear function that is not constantly
`false` takes the value `true` on half of the inputs
(`BitString.expect_boole_eq_one_div_two_of_map_add`).

The *Blum–Luby–Rubinfeld test* queries `f` at independent uniformly random `x` and `y` and at
`x + y`, and accepts when `(f x ^^ f y) = f (x + y)`; `BitString.blrAcceptance f` is the probability
that it accepts. Reading `f` as the function `F x = (-1) ^ f x`, the test accepts with probability
`1/2 + 1/2 ∑_S F̂(S)³` (`BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three`), by the
convolution theorem. Parities pass with probability one (`BitString.blrAcceptance_parityOn`).
Conversely, a function passing with probability at least `1 - ε` differs from some parity on at
most an `ε` fraction of the inputs
(`BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance`): the squares `F̂(S)²` sum to one
by Parseval's identity, so `∑_S F̂(S)³ ≤ max_S F̂(S)`, and `F̂(S)` is one minus twice the relative
Hamming distance from `f` to the parity on `S` (`BitString.fourierCoeff_signVal`)
[O'Donnell, Section 1.6][ODonnell2014], [BlumLubyRubinfeld1993].

## Main definitions

* `Cslib.BitString.blrAcceptance`: the acceptance probability of the Blum–Luby–Rubinfeld test.

## Main results

* `Cslib.BitString.expect_boole_eq_one_div_two_of_map_add`: nonzero linear functions are
  balanced.
* `Cslib.BitString.blrAcceptance_eq_sum_fourierCoeff_pow_three`: the acceptance probability in
  terms of the Fourier coefficients.
* `Cslib.BitString.blrAcceptance_parityOn`: completeness of the test.
* `Cslib.BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance`: soundness of the test.

## References

* [M. Blum, M. Luby, R. Rubinfeld, *Self-testing/correcting with applications to numerical
  problems*][BlumLubyRubinfeld1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Linear functions -/

/-- **Nonzero linear functions are balanced**: a Boolean function that turns sums of bit strings
into the exclusive or of its values, and is not constantly `false`, takes the value `true` with
probability one half at a uniformly random input. -/
theorem expect_boole_eq_one_div_two_of_map_add {f : (ι → Bool) → Bool}
    (hf : ∀ x y, f (x + y) = (f x ^^ f y)) (h : ∃ x, f x = true) :
    𝔼 x, (if f x = true then (1 : ℝ) else 0) = 1 / 2 := by
  obtain ⟨S, rfl⟩ := exists_eq_parityOn_iff.2 hf
  have hS : S.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    simp at h
  rw [Fintype.expect_boole, dens_filter_parityOn_eq hS]
  norm_num

/-! ### The Blum–Luby–Rubinfeld test -/

/-- The acceptance probability of the Blum–Luby–Rubinfeld linearity test on `f`: the probability,
over independent uniformly random bit strings `x` and `y`, that `(f x ^^ f y) = f (x + y)`. -/
noncomputable def blrAcceptance (f : (ι → Bool) → Bool) : ℝ :=
  𝔼 x, 𝔼 y, if (f x ^^ f y) = f (x + y) then 1 else 0

/-- **The acceptance probability of the BLR test**: reading `f` as signs, the test accepts with
probability `1/2 + 1/2 ∑_S F̂(S)³`. -/
theorem blrAcceptance_eq_sum_fourierCoeff_pow_three (f : (ι → Bool) → Bool) :
    blrAcceptance f = 1 / 2 + 1 / 2 * ∑ S, fourierCoeff (fun x => signVal (f x)) S ^ 3 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hind (a b c : Bool) : (if (a ^^ b) = c then (1 : ℝ) else 0) =
      1 / 2 + 1 / 2 * (signVal a * (signVal b * signVal c)) := by
    cases a <;> cases b <;> cases c <;> norm_num
  have hconv : 𝔼 x, 𝔼 y, F x * (F y * F (x + y)) =
      𝔼 x, F x * convolution F F x := by
    simp only [convolution, mul_expect]
  calc blrAcceptance f = 1 / 2 + 1 / 2 * 𝔼 x, 𝔼 y, F x * (F y * F (x + y)) := by
        simp only [blrAcceptance, hind, expect_add_distrib, ← mul_expect, Fintype.expect_const]
        rfl
    _ = 1 / 2 + 1 / 2 * ∑ S, fourierCoeff F S ^ 3 := by
        rw [hconv, expect_mul_eq_sum_fourierCoeff_mul]
        simp only [fourierCoeff_convolution, pow_three]

/-- **Completeness of the BLR test**: parities pass with probability one. -/
theorem blrAcceptance_parityOn (S : Finset ι) : blrAcceptance (parityOn S) = 1 := by
  simp [blrAcceptance, parityOn_add]

/-- **Soundness of the BLR test**: if the test accepts `f` with probability at least `1 - ε`,
then `f` differs from some parity on at most an `ε` fraction of the inputs
[O'Donnell, Theorem 1.30][ODonnell2014]. -/
theorem exists_hammingDist_parityOn_le_of_le_blrAcceptance {f : (ι → Bool) → Bool} {ε : ℝ}
    (h : 1 - ε ≤ blrAcceptance f) :
    ∃ S, (hammingDist f (parityOn S) : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  rw [blrAcceptance_eq_sum_fourierCoeff_pow_three] at h
  set c := fourierCoeff fun x => signVal (f x)
  obtain ⟨S, -, hS⟩ := exists_max_image univ c univ_nonempty
  refine ⟨S, ?_⟩
  have hc : ∑ T, c T ^ 3 ≤ c S := calc
    ∑ T, c T ^ 3 ≤ ∑ T, c S * c T ^ 2 := sum_le_sum fun T _ => by
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_right (hS T (mem_univ T)) (sq_nonneg _)
    _ = c S := by rw [← mul_sum, sum_fourierCoeff_sq_signVal, mul_one]
  have hcS : c S = 1 - 2 * hammingDist f (parityOn S) / 2 ^ Fintype.card ι :=
    fourierCoeff_signVal f S
  rw [mul_div_assoc] at hcS
  linarith

end Cslib.BitString
