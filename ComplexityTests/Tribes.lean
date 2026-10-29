/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Boolean.Tribes
import Complexity.Foundations.Data.BitString.AgreeExpect
import ComplexityTests.BravermanFooling

/-!
# The Tribes function

Concrete values of the Tribes function `Tribes_{w,s}`: the probability `7 / 16` of `true` for
`w = s = 2` [O'Donnell, Fact 4.10][ODonnell2014], and the resilience bound `2 ^ (q - w)` for
`w = 2`, `s = 1`, `q = 1`, which is attained. Then the instances of
[Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019] for Tribes under the even-parity
distribution on all `s w` bits (`ComplexityTests.BravermanFooling`), at concrete sufficient
parameters: `w = 1015`, `s = tribesSize w`, `p = 1016` for the bias, and `w = 2723`,
`s = 2 ^ w`, `p = 2727` for the influence. These instances check that the hypotheses can be met.

For the bias, the circuit reads all `s w` bits and the even-parity distribution on them is not
uniform. For the influence of a nonempty coalition `Q`, the influence depends only on the marginal
outside `Q` (`Cslib.BitString.isUndetermined_congr`), which for the even-parity distribution is
uniform, so that instance adds nothing beyond `Cslib.BitString.coalitionInfluence_tribes_le` and
only checks that the statement applies.
-/

namespace ComplexityTests.Tribes

open Finset Function Cslib Cslib.BitString Cslib.Circuits.Boolean.Braverman
  ComplexityTests.BravermanFooling
open scoped BigOperators

/-! ### Small cases -/

-- `Tribes_{2,2}` is true with probability `1 - (3 / 4) ^ 2 = 7 / 16`.
example : 𝔼 x, bitVal ℝ (tribes 2 2 x) = 7 / 16 := by
  rw [expect_bitVal_tribes]
  norm_num

/-- `Tribes_{2,1}` is `AND` of two bits. -/
theorem tribes_two_one (x : BitString (1 * 2)) : tribes 2 1 x = (x 0 && x 1) := by
  have h0 : finProdFinEquiv ((0 : Fin 1), (0 : Fin 2)) = 0 := rfl
  have h1 : finProdFinEquiv ((0 : Fin 1), (1 : Fin 2)) = 1 := rfl
  simp [tribes, Fin.exists_fin_one, Fin.forall_fin_two, h0, h1]

/-- The first bit leaves `Tribes_{2,1}` undetermined exactly when the second bit is `true`. -/
theorem isUndetermined_tribes_two_one_iff (x : BitString (1 * 2)) :
    IsUndetermined {0} (tribes 2 1) x ↔ ∀ i ∈ ({1} : Finset (Fin (1 * 2))), x i = true := by
  rw [isUndetermined_singleton_iff, tribes_two_one, tribes_two_one, update_self,
    update_of_ne (by decide : (1 : Fin (1 * 2)) ≠ 0)]
  simp only [mem_singleton, forall_eq]
  have key : ∀ a b : Bool, (!a && b) ≠ (a && b) ↔ b = true := by decide
  exact key _ _

/-- The first bit has influence exactly `1 / 2 = 2 ^ (1 - 2)` on `Tribes_{2,1}`. -/
theorem coalitionInfluence_tribes_two_one :
    coalitionInfluence (Probability.PMF.uniformOfFintype _) {0} (tribes 2 1) = 1 / 2 := by
  rw [coalitionInfluence_uniformOfFintype]
  simp only [isUndetermined_tribes_two_one_iff]
  rw [expect_ite_forall_mem_eq, card_singleton]
  norm_num

-- `Tribes_{2,1}` is `(1, 1 / 2)`-resilient, by the bound `2 ^ (q - w)`.
example : IsResilient 1 (1 / 2) (tribes 2 1) := by
  convert isResilient_tribes 2 1 1 using 1
  norm_num

-- The bound is attained: `Tribes_{2,1}` is not `(1, ε)`-resilient for any `ε < 1 / 2`.
example {ε : ℝ} (hε : ε < 1 / 2) : ¬IsResilient 1 ε (tribes 2 1) := fun h => by
  have h0 := h {0} (card_singleton 0)
  rw [coalitionInfluence_tribes_two_one] at h0
  linarith

/-! ### Theorem 4.1 of Chattopadhyay and Zuckerman -/

-- The bias at `w = 1015` with `s = tribesSize 1015`, which is largest with
-- `(1 - 2 ^ (-w)) ^ s ≥ 1 / 2`, and `p = w + 1`: under the even-parity distribution on its `s w`
-- bits, `Tribes_{w,s}` is true with probability within `2 ^ (-1015) + 2 ^ (-1016)` of `1 / 2`.
-- From `s ≥ 2 ^ (w - 1)`, `1015` is the least `w` with `2 ^ (w - 1) w - 1 ≥ (64 (w + 1)) ^ 64`.
-- `norm_num` evaluates `2 ^ 1016`, beyond the default `exponentiation.threshold` of `256`.
set_option exponentiation.threshold 1024 in
example : |∑ x, (evenParity (tribesSize 1015 * 1015) x).toReal *
      bitVal ℝ (tribes 1015 (tribesSize 1015) x) - 1 / 2| ≤ 2⁻¹ ^ 1015 + 1 / 2 ^ 1016 := by
  have hs : 2 ^ (1015 - 1) ≤ tribesSize 1015 := two_pow_sub_one_le_tribesSize (by norm_num)
  obtain ⟨K, hK⟩ : ∃ K, tribesSize 1015 * 1015 = K + 1 :=
    Nat.exists_eq_add_one.2 (Nat.mul_pos ((Nat.two_pow_pos _).trans_le hs) (by norm_num))
  have ht : (64 * 1016) ^ 64 ≤ K :=
    Nat.le_of_succ_le_succ (((show (64 * 1016) ^ 64 + 1 ≤ 2 ^ (1015 - 1) * 1015 by norm_num).trans
      (Nat.mul_le_mul_right 1015 hs)).trans hK.le)
  exact abs_sum_bitVal_tribes_sub_half_le (by norm_num)
    ((tribesSize_lt_two_pow 1015).trans (Nat.pow_lt_pow_right one_lt_two (by norm_num)))
    (by norm_num) (one_div_two_le_pow_tribesSize 1015) (pow_tribesSize_add_one_lt_one_div_two 1015)
    ht (hK ▸ isKWiseIndependent_evenParity K)

-- The influence at `w = 2723`, `s = 2 ^ w` and `p = w + 4`: under the even-parity distribution on
-- its `s w` bits, every coalition `Q` has influence at most `2 ^ (|Q| - 2723) + 2 ^ (-2727)` on
-- `Tribes_{w,s}`. For `s = 2 ^ w`, `p = w + 4`, `2723` is the least `w` with
-- `s w - 1 ≥ (64 p) ^ 157`.
-- `norm_num` evaluates `2 ^ 2727`, beyond the default `exponentiation.threshold` of `256`.
set_option exponentiation.threshold 2727 in
example (Q : Finset (Fin (2 ^ 2723 * 2723))) :
    coalitionInfluence (evenParity (2 ^ 2723 * 2723)) Q (tribes 2723 (2 ^ 2723)) ≤
      2 ^ #Q / 2 ^ 2723 + 1 / 2 ^ 2727 := by
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ 2723 * 2723 = K + 1 := Nat.exists_eq_add_one.2 (by positivity)
  have ht : (64 * 2727) ^ 157 ≤ K :=
    Nat.le_of_succ_le_succ ((show (64 * 2727) ^ 157 + 1 ≤ 2 ^ 2723 * 2723 by norm_num).trans hK.le)
  exact isKWiseResilient_tribes (by norm_num) (by norm_num) (by norm_num) ht Q rfl _
    (hK ▸ isKWiseIndependent_evenParity K)

end ComplexityTests.Tribes
