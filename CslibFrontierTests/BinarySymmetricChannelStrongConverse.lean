/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.BitString.BinarySymmetricChannel.Capacity
import CslibFrontier.Probability.BitString.BinarySymmetricChannel.StrongConverse
import Mathlib.Tactic.NormNum

/-!
# Tests: the strong converse and the capacity of the binary symmetric channel

* The packing bound: over one use of `BSC_0`, every code with four messages errs with average
  probability at least `1/2`.
* Symmetry: over `BSC_1`, complementing the received word recovers a noiseless code exactly.
* The strong converse is not vacuous: over `BSC_{1/2}` at rate `1/2`, long codes err with average
  probability at least `99/100`. In the source's form, over `BSC_0` at rate `2`, some message of
  every long code is misdecoded with probability more than `1/2`.
* The capacity of `BSC_{1/2}` is `0` and that of `BSC_0` is `1`. Rate `1/2` is achievable over
  `BSC_0` but not over `BSC_{1/2}`.
-/

namespace CslibFrontierTests.BinarySymmetricChannelStrongConverse

open Cslib Cslib.BitString Finset Real
open scoped BigOperators unitInterval

/-- The crossover probability `1/2`. -/
private noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem binEntropy_half : binEntropy (half : ℝ) / log 2 = 1 := by
  rw [show (half : ℝ) = 2⁻¹ by norm_num [half], binEntropy_two_inv,
    div_self (log_pos one_lt_two).ne']

private theorem binEntropy_zero_div : binEntropy ((0 : I) : ℝ) / log 2 = 0 := by
  rw [Set.Icc.coe_zero, binEntropy_zero, zero_div]

/-! ### The packing bound and symmetry -/

/-- Over one use of the noiseless channel, four messages are decoded correctly with average
probability at most `1/2`: the packing bound with cutoff `0`. -/
example (E : Fin 4 → BitString 1) (D : BitString 1 → Fin 4) :
    1 / 2 ≤ 𝔼 m, decodingError 0 E D m := by
  have h := one_sub_expect_decodingError_le 0 (by norm_num) E D 0
  norm_num at h
  linarith

/-- Over `BSC_1`, every bit is flipped, so a decoder that first complements the received word
inverts the identity code exactly. -/
example (n : ℕ) (m : BitString n) :
    decodingError (σ 0) id (fun y => id fun i => !y i) m = 0 := by
  rw [decodingError_symm]
  exact decodingError_zero_eq_zero (fun _ => rfl) m

/-! ### Nonvacuity of the strong converse -/

/-- Over `BSC_{1/2}` at rate `1/2`, long codes err with average probability at least `99/100`. -/
example : ∀ᶠ n : ℕ in Filter.atTop, ∀ (E : Fin (2 ^ ⌈(1 / 2 : ℝ) * n⌉₊) → BitString n)
    (D : BitString n → Fin (2 ^ ⌈(1 / 2 : ℝ) * n⌉₊)),
    99 / 100 ≤ 𝔼 m, decodingError half E D m := by
  have hR : 1 - binEntropy (half : ℝ) / log 2 < 1 / 2 := by
    rw [binEntropy_half]
    norm_num
  filter_upwards [eventually_one_sub_le_expect_decodingError half hR (ε := 1 / 100)
    (by norm_num)] with n hn E D
  have : Nonempty (Fin (2 ^ ⌈(1 / 2 : ℝ) * n⌉₊)) := ⟨⟨0, by positivity⟩⟩
  have h := hn E D (by
    rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_two, logb_pow, logb_self_eq_one one_lt_two,
      mul_one]
    exact Nat.le_ceil _)
  linarith

/-- Over the noiseless channel `BSC_0`, at rate `2`, long codes misdecode some message with
probability more than `1/2`: the form of Guruswami–Rudra–Sudan Theorem 6.3.1(2). -/
example : ∀ᶠ n : ℕ in Filter.atTop, ∀ (E : BitString (2 * n) → BitString n)
    (D : BitString n → BitString (2 * n)), ∃ m, 1 / 2 < decodingError 0 E D m := by
  have hR : 1 - binEntropy ((0 : I) : ℝ) / log 2 < 2 := by
    rw [binEntropy_zero_div]
    norm_num
  filter_upwards [eventually_exists_lt_decodingError 0 hR (ε := 1 / 2) (by norm_num)] with n hn
  exact hn (2 * n) (by push_cast; rfl)

/-! ### The capacity -/

/-- The capacity of `BSC_{1/2}` is `0`. -/
example : sSup {R | IsAchievableRate half R} = 0 := by
  rw [sSup_isAchievableRate, binEntropy_half, sub_self]

/-- The capacity of the noiseless channel `BSC_0` is one bit per use. -/
example : sSup {R | IsAchievableRate 0 R} = 1 := by
  rw [sSup_isAchievableRate, binEntropy_zero_div, sub_zero]

/-- Rate `1/2` is achievable over the noiseless channel. -/
example : IsAchievableRate 0 (1 / 2) :=
  isAchievableRate_of_lt 0 (by rw [binEntropy_zero_div]; norm_num)

/-- Rate `1/2` is not achievable over `BSC_{1/2}`. -/
example : ¬ IsAchievableRate half (1 / 2) :=
  not_isAchievableRate_of_lt half (by rw [binEntropy_half]; norm_num)

/-- Rate `0` is achievable over every `BSC_p`: one codeword is never misdecoded. -/
example (p : I) : IsAchievableRate p 0 := isAchievableRate_of_nonpos p le_rfl

end CslibFrontierTests.BinarySymmetricChannelStrongConverse
