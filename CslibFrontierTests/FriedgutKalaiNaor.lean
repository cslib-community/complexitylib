/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.BooleanAnalysis.FriedgutKalaiNaor

/-!
# The Friedgut–Kalai–Naor Theorem and low-degree anticoncentration

Instances for `CslibFrontier.Foundations.Data.Finset.PaleyZygmund`,
`CslibFrontier.Foundations.BooleanAnalysis.Anticoncentration` and
`CslibFrontier.Foundations.BooleanAnalysis.FriedgutKalaiNaor`. The dictator `x ↦ x_0` has degree-one
weight `1`, so it meets the FKN hypothesis with `δ = 0` and Exercise 1.19(a) recovers it. Its sign
`x_0` has variance `1`, so the anticoncentration theorem applies to it (with `k = 1`). The
indicator of the all-`true` input on `n` bits, the biased Bernoulli variable of
[O'Donnell, Examples 9.2][ODonnell2014], has `𝔼 y ^ 4 = 2 ^ n (𝔼 y ^ 2) ^ 2`: it is not
`B`-reasonable for `B < 2 ^ n`, and the bound `1 / λ` of Proposition 9.5 is attained.
-/

namespace CslibFrontierTests.FriedgutKalaiNaor

open Finset Cslib Cslib.BitString
open scoped BigOperators

/-! ### The dictator -/

/-- The degree-one Fourier coefficients of the dictator `x ↦ x_0`, read as signs. -/
theorem fourierCoeff_dictator_singleton (i : Fin 3) :
    fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0)) {i} = if (0 : Fin 3) = i then 1 else 0 :=
  by simp only [fourierCoeff, ← chi_singleton, expect_chi_mul_chi, singleton_inj]

/-- The dictator has all of its Fourier weight at degree one. -/
theorem levelWeight_one_dictator :
    levelWeight 1 (fun x : Fin 3 → Bool => signVal (x 0)) = 1 := by
  simp only [levelWeight_one, fourierCoeff_dictator_singleton, ite_pow, one_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Fintype.sum_ite_eq]

-- The FKN hypothesis holds with `δ = 0`, so the conclusion is exact closeness.
example : ∃ (i : Fin 3) (b : Bool),
    (hammingDist (fun x : Fin 3 → Bool => x 0) (fun x => b ^^ x i) : ℝ) / 2 ^ 3 ≤ 1601 * 0 :=
  exists_hammingDist_xor_div_le_of_le_levelWeight_one (by rw [levelWeight_one_dictator]; norm_num)

-- The coefficient form at `δ = 0`: some degree-one coefficient has absolute value `1`.
example : ∃ i : Fin 3, 1 - 3202 * 0 ≤ |fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0)) {i}| :=
  exists_one_sub_le_abs_fourierCoeff_singleton (by norm_num)
    (by rw [levelWeight_one_dictator]; norm_num)

-- Exercise 1.19(a) recovers a signed dictator from `W^1 = 1`.
example : ∃ (i : Fin 3) (b : Bool), (fun x : Fin 3 → Bool => x 0) = fun x => b ^^ x i :=
  exists_eq_xor_of_levelWeight_one_eq_one levelWeight_one_dictator

/-! ### Anticoncentration -/

/-- The sign of a coordinate has mean `0` and variance `1`. -/
theorem expect_sub_expect_sq_signVal_apply :
    𝔼 x : Fin 2 → Bool, (signVal (x 0) - 𝔼 y : Fin 2 → Bool, signVal (y 0)) ^ 2 = 1 := by
  simp only [← chi_singleton, expect_chi, singleton_ne_empty, ite_false, sub_zero, sq,
    chi_mul_chi, symmDiff_self, bot_eq_empty, ite_true]

-- Theorem 9.7 applies, nonvacuously, to the degree-one function `x ↦ x_0`.
example : 9 / 16 / 9 ^ 1 ≤ (dens {x : Fin 2 → Bool | √(𝔼 z : Fin 2 → Bool,
      (signVal (z 0) - 𝔼 y : Fin 2 → Bool, signVal (y 0)) ^ 2) / 2 <
      |signVal (x 0) - 𝔼 y : Fin 2 → Bool, signVal (y 0)|} : ℝ) :=
  nine_div_sixteen_div_nine_pow_le_dens
    (by
      rw [show (fun z : Fin 2 → Bool => signVal (z 0)) = chi ℝ {0} from
        funext fun z => (chi_singleton 0 z).symm]
      exact chi_mem_lowDegree (F := ℝ) ({0} : Finset (Fin 2)))
    (by rw [expect_sub_expect_sq_signVal_apply]; norm_num)

/-! ### An unreasonable random variable -/

/-- The indicator of the all-`true` input on `n` bits has `𝔼 y ^ 4 = 2 ^ n (𝔼 y ^ 2) ^ 2`. -/
theorem expect_pow_four_indicator_eq (n : ℕ) :
    𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 4 =
      2 ^ n * (𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 2) ^ 2 := by
  simp only [ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Fintype.expect_boole, filter_eq', mem_univ, ite_true, dens_singleton, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  push_cast
  field_simp

-- So it is not `B`-reasonable for any `B < 2 ^ n`.
example (n : ℕ) {B : ℝ} (hB : B < 2 ^ n) :
    ¬ 𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 4 ≤
      B * (𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 2) ^ 2 := by
  rw [expect_pow_four_indicator_eq]
  have : 0 < 𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 2 := by
    simp only [ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Fintype.expect_boole, filter_eq', mem_univ, ite_true, dens_singleton]
    positivity
  intro h
  linarith [mul_lt_mul_of_pos_right hB (pow_pos this 2)]

-- Proposition 9.5 applies with `λ = 2⁻ⁿ`: the indicator takes each value with probability at
-- least `2⁻ⁿ`.
example (n : ℕ) :
    (2 ^ n)⁻¹ * 𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 4 ≤
      (𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 2) ^ 2 :=
  Fintype.mul_expect_pow_four_le_of_le_dens fun x => by
    have hsub : ({x} : Finset (Fin n → Bool)) ⊆
        ({y | (if y = fun _ => true then (1 : ℝ) else 0) =
          if x = fun _ => true then (1 : ℝ) else 0} : Finset (Fin n → Bool)) := by
      simp only [singleton_subset_iff, mem_filter, mem_univ, and_self]
    calc ((2 : ℝ) ^ n)⁻¹ = (dens ({x} : Finset (Fin n → Bool)) : ℝ) := by
          simp only [dens_singleton, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
          push_cast; rfl
      _ ≤ _ := by exact_mod_cast dens_le_dens hsub

-- and it is attained there: `2⁻ⁿ 𝔼 y ^ 4 = (𝔼 y ^ 2) ^ 2`.
example (n : ℕ) :
    (2 ^ n)⁻¹ * 𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 4 =
      (𝔼 x : Fin n → Bool, (if x = fun _ => true then (1 : ℝ) else 0) ^ 2) ^ 2 := by
  rw [expect_pow_four_indicator_eq, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end CslibFrontierTests.FriedgutKalaiNaor
