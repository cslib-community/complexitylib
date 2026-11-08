/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.BitString.BinarySymmetricChannel.Converse
import Mathlib.Tactic.NormNum

/-!
# Tests: Fano's inequality and the weak converse for the binary symmetric channel

* Fano's inequality is tight for the uniform law on three symbols: both sides are `log₂ 3`.
* If the estimate is always right, Fano's inequality forces `H(X | Y) = 0`.
* The noise of `BSC_{1/2}` on three bits has entropy `3`; uniform inputs carry `0` bits across
  `BSC_{1/2}` and `n` bits across `BSC_0`.
* Four messages cannot be sent over one use of the noiseless channel without error, and over three
  uses of `BSC_{1/2}` every code with four messages errs with average probability at least `1/2`.
* The asymptotic converse is not vacuous: over `BSC_{1/2}` at rate `1/2`, and over `BSC_0` at rate
  `2`, every long code has error bounded below; so does its maximal error.
-/

namespace ComplexityTests.BinarySymmetricChannelConverse

open Cslib Cslib.BitString Cslib.Probability.PMF Finset Real
open scoped BigOperators ENNReal unitInterval

/-- The crossover probability `1/2`. -/
private noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem binEntropy_half : binEntropy (half : ℝ) / log 2 = 1 := by
  rw [show (half : ℝ) = 2⁻¹ by norm_num [half], binEntropy_two_inv,
    div_self (log_pos one_lt_two).ne']

private theorem binEntropy_zero_div : binEntropy ((0 : I) : ℝ) / log 2 = 0 := by
  rw [Set.Icc.coe_zero, binEntropy_zero, zero_div]

/-! ### Fano's inequality -/

/-- Fano's inequality is tight for the uniform law on three symbols, guessing `0`: the error
probability is `2/3` and both sides equal `log₂ 3`. -/
example :
    entropy (Probability.PMF.uniformOfFintype (Fin 3)) =
      binEntropy (1 - (Probability.PMF.uniformOfFintype (Fin 3) 0).toReal) / log 2 +
        (1 - (Probability.PMF.uniformOfFintype (Fin 3) 0).toReal) *
          logb 2 (Fintype.card (Fin 3) - 1) := by
  rw [entropy_uniform, Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  have h3 : ((3 : ℝ≥0∞)⁻¹).toReal = 1 / 3 := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]
  push_cast
  rw [h3, binEntropy, logb, logb]
  have hl : log ((1 - 1 / 3 : ℝ)⁻¹) = log 3 - log 2 := by
    rw [show (1 - 1 / 3 : ℝ)⁻¹ = 3 / 2 by norm_num, log_div (by norm_num) (by norm_num)]
  have hl' : log ((1 - (1 - 1 / 3) : ℝ)⁻¹) = log 3 := by norm_num
  rw [hl, hl', show (3 : ℝ) - 1 = 2 by norm_num]
  have h2 : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  field_simp
  ring

/-- An estimate that is never wrong leaves no uncertainty: Fano's inequality gives `H(X | Y) ≤ 0`.
-/
example {Ω α β : Type*} [Fintype α] [Finite β] (ν : PMF Ω) (X : Ω → α) (Y : Ω → β) (g : β → α)
    (hg : ∀ ω, g (Y ω) = X ω) :
    conditionalEntropy (ν.map fun ω => (Y ω, X ω)) ≤ 0 := by
  have h := conditionalEntropy_map_le_binEntropy_add_mul_logb ν X Y g
  have hempty : {ω | g (Y ω) ≠ X ω} = ∅ := Set.eq_empty_of_forall_notMem fun ω h => h (hg ω)
  rw [hempty, MeasureTheory.measure_empty, ENNReal.toReal_zero, binEntropy_zero, zero_div,
    zero_mul, add_zero] at h
  exact h

/-! ### Entropy and mutual information across the channel -/

/-- The noise of `BSC_{1/2}` on three bits is uniform: three bits of entropy. -/
example : entropy (bscNoise (ι := Fin 3) half) = 3 := by
  rw [entropy_bscNoise, binEntropy_half, Fintype.card_fin]
  norm_num

/-- `BSC_{1/2}` is useless: a uniform input carries no information. -/
example (n : ℕ) :
    mutualInfo ((Probability.PMF.uniformOfFintype (BitString n)).bind fun x =>
      (bsc half x).map (x, ·)) = 0 := by
  rw [mutualInfo_uniformOfFintype_bind_bsc, binEntropy_half, sub_self, mul_zero]

/-- `BSC_0` is noiseless: a uniform input carries all `n` bits. -/
example (n : ℕ) :
    mutualInfo ((Probability.PMF.uniformOfFintype (BitString n)).bind fun x =>
      (bsc 0 x).map (x, ·)) = n := by
  rw [mutualInfo_uniformOfFintype_bind_bsc, binEntropy_zero_div, sub_zero, mul_one,
    Fintype.card_fin]

/-! ### The converse on small codes -/

/-- Four messages cannot be sent without error over one use of the noiseless channel `BSC_0`. -/
example (E : Fin 4 → BitString 1) (D : BitString 1 → Fin 4) :
    𝔼 m, decodingError 0 E D m ≠ 0 := by
  intro h
  have := logb_card_le_add_fano 0 E D
  rw [h, binEntropy_zero_div, Real.binEntropy_zero, zero_div, zero_mul, add_zero, add_zero,
    sub_zero, mul_one, Fintype.card_fin, Fintype.card_fin] at this
  have h4 : logb 2 (4 : ℕ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, logb_pow, logb_self_eq_one one_lt_two]
    norm_num
  rw [h4] at this
  norm_num at this

/-- Over three uses of `BSC_{1/2}`, every code with four messages errs with average probability at
least `1/2`, whatever the decoder. -/
example (E : Fin 4 → BitString 3) (D : BitString 3 → Fin 4) :
    1 / 2 ≤ 𝔼 m, decodingError half E D m := by
  have h := one_sub_expect_decodingError_mul_logb_card_le half E D
  rw [binEntropy_half, sub_self, mul_zero, zero_add, Fintype.card_fin] at h
  have h4 : logb 2 (4 : ℕ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, logb_pow, logb_self_eq_one one_lt_two]
    norm_num
  rw [h4] at h
  linarith

/-! ### Nonvacuity of the asymptotic converse -/

/-- Over `BSC_{1/2}` at rate `1/2`, long codes err with average probability at least `1/2`. -/
example : ∀ᶠ n : ℕ in Filter.atTop, ∀ (E : Fin (2 ^ ⌈(1 / 2 : ℝ) * n⌉₊) → BitString n)
    (D : BitString n → Fin (2 ^ ⌈(1 / 2 : ℝ) * n⌉₊)),
    1 / 2 ≤ 𝔼 m, decodingError half E D m := by
  have hR : 1 - binEntropy (half : ℝ) / log 2 < 1 / 2 := by
    rw [binEntropy_half]
    norm_num
  filter_upwards [eventually_le_expect_decodingError half hR] with n hn E D
  have := hn E D
  rw [binEntropy_half] at this
  norm_num at this
  linarith

/-- Over the noiseless channel at rate `2`, long codes have maximal error at least `1/4`: some
message is decoded wrongly with probability at least `1/4`. -/
example : ∀ᶠ n : ℕ in Filter.atTop, ∀ (E : Fin (2 ^ ⌈(2 : ℝ) * n⌉₊) → BitString n)
    (D : BitString n → Fin (2 ^ ⌈(2 : ℝ) * n⌉₊)),
    ∃ m, 1 / 4 ≤ decodingError 0 E D m := by
  have hR : 1 - binEntropy ((0 : I) : ℝ) / log 2 < 2 := by
    rw [binEntropy_zero_div]
    norm_num
  filter_upwards [eventually_le_expect_decodingError 0 hR] with n hn E D
  have := hn E D
  rw [binEntropy_zero_div] at this
  norm_num at this
  obtain ⟨m, -, hm⟩ := Finset.exists_le_of_le_expect ⟨⟨0, by positivity⟩, mem_univ _⟩ this
  exact ⟨m, by linarith⟩

end ComplexityTests.BinarySymmetricChannelConverse
