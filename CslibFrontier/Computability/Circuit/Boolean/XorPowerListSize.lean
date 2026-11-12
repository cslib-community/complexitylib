/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.XorLemma
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.Sign.BigOperators
import CslibFrontier.Foundations.Data.Code.BinaryJohnson
import CslibFrontier.Foundations.Data.Code.HammingBound
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The list size of the `k`-fold XOR code

The `k`-fold XOR `g^{⊕k}` of a Boolean function `g` on `n` bits (`Cslib.Circuits.Boolean.xorPower`)
encodes the truth table of `g`, a message of `M = 2 ^ n` bits, as a word of `2 ^ (k n)` bits. Read
as signs, the XOR of the values of `g` on `k` blocks is the product of their signs
(`signVal_xorPower`). Since the blocks of a uniform input are independent and uniform, the
correlation of two encodings is the `k`-th power of the correlation of the messages
(`expect_signVal_xorPower_mul_signVal_xorPower`):
`𝔼 signVal (g^{⊕k}) signVal (g'^{⊕k}) = (𝔼 signVal g signVal g') ^ k` for every `k`.

The code is not injective for even `k`, since `g` and its complement have the same encoding, and
its distance is poor; still its lists are short. Let `k` be odd. Messages at relative distance at
least `δ₀` have correlation at most `1 - 2 δ₀`, so their encodings have correlation at most
`(1 - 2 δ₀) ^ k`, also when the messages are nearly complementary, because `t ↦ t ^ k` is monotone.
If `(1 - 2 δ₀) ^ k ≤ 2 ε ^ 2`, the binary Johnson bound
(`Cslib.Code.card_filter_mul_two_mul_sq_le`) shows that at most `V / (2 ε ^ 2)` functions `g`
have encodings agreeing with a fixed word on a `1 / 2 + ε` fraction of the inputs, where
`V = ∑_{j ≤ r} C(M, j)` is the size of a Hamming ball of radius `r ≥ δ₀ M - 1` among the messages
(`card_filter_xorPower_mul_two_mul_sq_le`). With `r = ⌊δ₀ M⌋` and the entropy bound on the ball,
for `δ₀ ≤ 1 / 2` the list has at most `exp (M H(δ₀)) / (2 ε ^ 2) = 2 ^ (H₂(δ₀) M) / (2 ε ^ 2)`
functions, where `H = Real.binEntropy` is the binary entropy in nats
(`card_filter_xorPower_mul_two_mul_sq_le_exp`).

Faithfulness: the correlation identity is the classical computation for XOR codes. The list
size bound is a library result combining it with the binary Johnson bound and a covering argument;
it is the list-size step of the library's route to the NP-hardness of partial MCSP (issue #4362,
milestone H2), not a statement taken from a source.

## Main results

* `Cslib.Circuits.Boolean.signVal_xorPower`: the sign of a `k`-fold XOR is the product of the signs
  on the blocks.
* `Cslib.Circuits.Boolean.sum_signVal_xorPower_mul_signVal_xorPower`,
  `Cslib.Circuits.Boolean.expect_signVal_xorPower_mul_signVal_xorPower`: the correlation of two
  `k`-fold XORs is the `k`-th power of the correlation of the functions.
* `Cslib.Circuits.Boolean.card_filter_xorPower_mul_two_mul_sq_le`,
  `Cslib.Circuits.Boolean.card_filter_xorPower_mul_two_mul_sq_le_exp`: the list size of the `k`-fold
  XOR code for odd `k`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019],
  Proposition 3.3.3
-/

public section

namespace Cslib.Circuits.Boolean

open Finset BitString Real
open scoped BigOperators

variable {n : ℕ}

/-- The sign of the `k`-fold XOR is the product of the signs of the values on the blocks. -/
theorem signVal_xorPower (f : BooleanFunction n) (k : ℕ) (x : BitString (k * n)) :
    signVal (xorPower f k x) = ∏ i, signVal (f (BitString.block x i)) := by
  rw [xorPower_apply, signVal_sum]

/-- The sign correlation of two `k`-fold XORs is the `k`-th power of the sign correlation of the
functions. -/
theorem sum_signVal_xorPower_mul_signVal_xorPower (f g : BooleanFunction n) (k : ℕ) :
    ∑ x, signVal (xorPower f k x) * signVal (xorPower g k x) =
      (∑ y, signVal (f y) * signVal (g y)) ^ k := by
  rw [Fintype.sum_pow]
  refine Fintype.sum_equiv BitString.blocksEquiv _ _ fun x => ?_
  rw [signVal_xorPower, signVal_xorPower, ← prod_mul_distrib, BitString.blocksEquiv_apply]

/-- **Correlation of `k`-fold XORs**: under the uniform distribution, the correlation of two
`k`-fold XORs is the `k`-th power of the correlation of the functions. -/
theorem expect_signVal_xorPower_mul_signVal_xorPower (f g : BooleanFunction n) (k : ℕ) :
    𝔼 x, signVal (xorPower f k x) * signVal (xorPower g k x) =
      (𝔼 y, signVal (f y) * signVal (g y)) ^ k := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card,
    sum_signVal_xorPower_mul_signVal_xorPower, div_pow, BitString.card, BitString.card, pow_mul']
  push_cast
  rfl

/-- The sign correlation of two Boolean functions at Hamming distance more than `r ≥ δ₀ 2 ^ n - 1`
is at most `(1 - 2 δ₀) 2 ^ n`. -/
private theorem sum_signVal_mul_signVal_le (f g : BooleanFunction n) {δ₀ : ℝ} {r : ℕ}
    (hr : δ₀ * 2 ^ n ≤ r + 1) (hfg : r < hammingDist f g) :
    ∑ y, signVal (f y) * signVal (g y) ≤ (1 - 2 * δ₀) * 2 ^ n := by
  rw [sum_signVal_mul_signVal_eq_card_sub, BitString.card]
  have : (r : ℝ) + 1 ≤ hammingDist f g := by exact_mod_cast hfg
  push_cast
  linarith

/-- **The list size of the `k`-fold XOR code** (library result): let `k` be odd, `ε ≥ 0`, and
`(1 - 2 δ₀) ^ k ≤ 2 ε ^ 2`. The Boolean functions `g` on `n` bits whose `k`-fold XORs agree with a
word `w` on at least a `1 / 2 + ε` fraction of the inputs number at most `V / (2 ε ^ 2)`, where
`V = ∑_{j ≤ r} C(2 ^ n, j)` is the size of a Hamming ball of radius `r` among them, for any
`r ≥ δ₀ 2 ^ n - 1`. -/
theorem card_filter_xorPower_mul_two_mul_sq_le {k : ℕ} (hk : Odd k) (w : BitString (k * n) → Bool)
    {ε δ₀ : ℝ} (hε : 0 ≤ ε) (hkε : (1 - 2 * δ₀) ^ k ≤ 2 * ε ^ 2) {r : ℕ}
    (hr : δ₀ * 2 ^ n ≤ r + 1) :
    (#{g : BooleanFunction n | (1 / 2 + ε) * 2 ^ (k * n) ≤ #{x | xorPower g k x = w x}} : ℝ) *
      (2 * ε ^ 2) ≤ ((∑ j ∈ range (r + 1), (2 ^ n).choose j : ℕ) : ℝ) := by
  have h := Code.card_filter_mul_two_mul_sq_le (fun g => xorPower g k) w hε
    (V := ((∑ j ∈ range (r + 1), (2 ^ n).choose j : ℕ) : ℝ)) (Nat.cast_nonneg _) r
    (fun g g' hgg' => ?_) (fun g => ?_)
  · simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using h
  · -- distant functions have nearly uncorrelated `k`-fold XORs
    rw [sum_signVal_xorPower_mul_signVal_xorPower, BitString.card, Nat.cast_pow, Nat.cast_ofNat,
      pow_mul']
    calc (∑ y, signVal (g y) * signVal (g' y)) ^ k ≤ ((1 - 2 * δ₀) * 2 ^ n) ^ k :=
          hk.strictMono_pow.monotone (sum_signVal_mul_signVal_le g g' hr hgg')
      _ = (1 - 2 * δ₀) ^ k * (2 ^ n) ^ k := mul_pow _ _ _
      _ ≤ 2 * ε ^ 2 * (2 ^ n) ^ k := by gcongr
  · -- the size of a Hamming ball among the Boolean functions
    rw [Code.card_filter_hammingDist_le_eq_sum]
    exact_mod_cast le_of_eq (sum_congr rfl fun j _ => by
      rw [Code.card_filter_hammingDist_eq_choose_mul_pow (q := 2) (fun _ => Fintype.card_bool) g j,
        BitString.card]
      simp)

/-- **The list size of the `k`-fold XOR code**, entropy form (library result): let `k` be odd,
`ε ≥ 0`, `0 ≤ δ₀ ≤ 1 / 2` and `(1 - 2 δ₀) ^ k ≤ 2 ε ^ 2`. The Boolean functions on `n` bits whose
`k`-fold XORs agree with a word on at least a `1 / 2 + ε` fraction of the inputs number at most
`exp (2 ^ n H(δ₀)) / (2 ε ^ 2)`, where `H = Real.binEntropy` is the binary entropy in nats; that is,
`2 ^ (H₂(δ₀) 2 ^ n) / (2 ε ^ 2)` for the binary entropy `H₂` in bits. -/
theorem card_filter_xorPower_mul_two_mul_sq_le_exp {k : ℕ} (hk : Odd k)
    (w : BitString (k * n) → Bool) {ε δ₀ : ℝ} (hε : 0 ≤ ε) (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2)
    (hkε : (1 - 2 * δ₀) ^ k ≤ 2 * ε ^ 2) :
    (#{g : BooleanFunction n | (1 / 2 + ε) * 2 ^ (k * n) ≤ #{x | xorPower g k x = w x}} : ℝ) *
      (2 * ε ^ 2) ≤ exp (2 ^ n * binEntropy δ₀) := by
  have hM : (0 : ℝ) ≤ δ₀ * 2 ^ n := by positivity
  refine (card_filter_xorPower_mul_two_mul_sq_le hk w hε hkε (r := ⌊δ₀ * 2 ^ n⌋₊)
    (Nat.lt_floor_add_one _).le).trans ?_
  have h := sum_choose_mul_pow_le_exp_mul_qaryEntropy (q := 2) (n := 2 ^ n) (r := ⌊δ₀ * 2 ^ n⌋₊)
    le_rfl hδ₀ (by norm_num; linarith) (by exact_mod_cast Nat.floor_le hM)
  simpa only [Nat.add_one_sub_one, one_pow, mul_one, qaryEntropy_two, Nat.cast_pow,
    Nat.cast_ofNat] using h

end Cslib.Circuits.Boolean
