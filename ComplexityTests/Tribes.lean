/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Boolean.Tribes
import ComplexityTests.BravermanFooling

/-!
# The Tribes function

Concrete values of the Tribes function `Tribes_{w,s}`: the probability `7 / 16` of `true` for
`w = s = 2` [O'Donnell, Fact 4.10][ODonnell2014], and the resilience bound `2 ^ (q - w)` for
`w = 2`, `s = 1`, `q = 1`, which is attained. Then the instances of
[Chattopadhyay–Zuckerman, Theorem 4.1][ChattopadhyayZuckerman2019] for Tribes under the even-parity
distribution on all `s w` bits (`ComplexityTests.BravermanFooling`), for symbolic `w` and `s`.

The hypotheses of these instances hold only for very large `w`, about `2800` and more, which is
not checked here. For the bias, the circuit reads all `s w` bits and the even-parity distribution
on them is not uniform. For the influence of a nonempty coalition `Q`, the influence depends only
on the marginal outside `Q` (`Cslib.BitString.isUndetermined_congr`), which for the even-parity
distribution is uniform, so that instance only checks that the statement applies.
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
  have h := isResilient_tribes 2 1 1
  norm_num at h
  exact h

-- The bound is attained: `Tribes_{2,1}` is not `(1, ε)`-resilient for any `ε < 1 / 2`.
example {ε : ℝ} (hε : ε < 1 / 2) : ¬IsResilient 1 ε (tribes 2 1) := fun h => by
  have h0 := h {0} (card_singleton 0)
  rw [coalitionInfluence_tribes_two_one] at h0
  linarith

/-! ### Theorem 4.1 of Chattopadhyay and Zuckerman -/

-- The bias: if `s` is largest with `(1 - 2 ^ (-w)) ^ s ≥ 1 / 2` and `s w = K + 1` with
-- `K ≥ (64 (w + 1)) ^ 64`, then `Tribes_{w,s}` is true with probability within
-- `2 ^ (-w) + 2 ^ (-(w + 1))` of `1 / 2` under the even-parity distribution on its `s w` bits.
example {w s K : ℕ} (hs : s < 2 ^ w)
    (h₁ : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) (h₂ : (1 - (2⁻¹ : ℝ) ^ w) ^ (s + 1) < 1 / 2)
    (hK : (64 * (w + 1)) ^ 64 ≤ K) (h : s * w = K + 1) :
    |∑ x, (evenParity (s * w) x).toReal * bitVal ℝ (tribes w s x) - 1 / 2| ≤
      2⁻¹ ^ w + 1 / 2 ^ (w + 1) :=
  abs_sum_bitVal_tribes_sub_half_le (by omega)
    (hs.trans (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self w)))
    (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self w))) h₁ h₂
    hK (h ▸ isKWiseIndependent_evenParity K)

-- The influence: if `s ≤ 2 ^ w` and `s w = K + 1` with `K ≥ (64 (w + 4)) ^ 157`, then every
-- coalition `Q` has influence at most `2 ^ (|Q| - w) + 2 ^ (-(w + 4))` on `Tribes_{w,s}` under the
-- even-parity distribution on its `s w` bits.
example {w s K : ℕ} (hs : s ≤ 2 ^ w) (hK : (64 * (w + 4)) ^ 157 ≤ K) (h : s * w = K + 1)
    (Q : Finset (Fin (s * w))) :
    coalitionInfluence (evenParity (s * w)) Q (tribes w s) ≤ 2 ^ #Q / 2 ^ w + 1 / 2 ^ (w + 4) := by
  have h16 : 2 ^ (w + 4) = 2 ^ w * 16 := by rw [pow_add]; norm_num
  have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  exact isKWiseResilient_tribes (by omega) (by omega)
    (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right two_pos (Nat.le_add_right w 4))) hK Q rfl
    _ (h ▸ isKWiseIndependent_evenParity K)

end ComplexityTests.Tribes
