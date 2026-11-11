/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Cube
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.ExpectPi
import Mathlib.Analysis.Complex.Exponential

/-!
# The generalized inner product

The *generalized inner product* of `k` strings `x i` of `n` bits, one on each player's forehead, is
the parity of the number of positions at which all the strings have a `1`:
`GIP(x) = ⊕_r ∧_i x i r` (`NOF.gip`). With two players it is the inner product modulo two
(`NOF.gip_fin_two`).

Babai, Nisan and Szegedy [BabaiNisanSzegedy1992] proved an `Ω(n / 4 ^ k)` lower bound for it by
discrepancy, which holds for protocols with public coins and constant error below `1 / 2`
[Jukna, Section 5.6][Jukna2012]. We follow
the cube-bound proof (`CslibFrontier.Computability.Communication.NOF.Cube`). Over the corners of a
cube
spanned by `a` and `b`, the generalized inner product adds up to its value at `a + b`. This follows
from the distributive law `∏ i, (b i + a i) = ∑ S, ∏_{i ∈ S} b i ∏_{i ∉ S} a i` in the two-element
Boolean ring. So the cube expectation of `GIP` equals its bias `𝔼 (-1) ^ GIP`
(`NOF.cubeExpectation_gip`). By independence of the positions, the bias is
`(1 - 2 / 2 ^ k) ^ n` (`NOF.expect_signVal_gip`), so
`disc(GIP) ^ (2 ^ k) ≤ (1 - 2 / 2 ^ k) ^ n` under the uniform distribution
(`NOF.discrepancy_gip_pow_le`). With the discrepancy bound and `1 - x ≤ exp (-x)`, a public-coin
protocol with error `1 / 2 - γ` sending `c` bits has
`(2 γ) ^ (2 ^ k) ≤ 2 ^ (c 2 ^ k) (1 - 2 / 2 ^ k) ^ n`
(`NOF.PublicCoin.pow_le_of_ecomplexityFun_gip_le`). For error `1 / 3` this gives
`2 n < 4 ^ k (c + 2)` (`NOF.PublicCoin.two_mul_lt_four_pow_mul_of_ecomplexityFun_gip_le`), and
deterministic protocols give `2 n ≤ 4 ^ k c`
(`NOF.Protocol.two_mul_le_four_pow_mul_of_ecomplexityFun_gip_le`).

With one player the bias is `0` for `n ≥ 1`, so no protocol beats error `1 / 2`. That player
sees nothing.

## Main definitions

* `Cslib.Communication.NOF.gip`: the generalized inner product.

## Main results

* `Cslib.Communication.NOF.cubeExpectation_gip`, `Cslib.Communication.NOF.expect_signVal_gip`: the
  cube expectation of the generalized inner product is its bias `(1 - 2 / 2 ^ k) ^ n`.
* `Cslib.Communication.NOF.discrepancy_gip_pow_le`: `disc(GIP) ^ (2 ^ k) ≤ (1 - 2 / 2 ^ k) ^ n`.
* `Cslib.Communication.NOF.PublicCoin.two_mul_lt_four_pow_mul_of_ecomplexityFun_gip_le`,
  `Cslib.Communication.NOF.Protocol.two_mul_le_four_pow_mul_of_ecomplexityFun_gip_le`: the
  Babai–Nisan–Szegedy lower bound `Ω(n / 4 ^ k)`.

## References

* [L. Babai, N. Nisan and M. Szegedy, *Multiparty protocols, pseudorandom generators for logspace,
  and time-space trade-offs*][BabaiNisanSzegedy1992]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Communication.NOF

open Finset Function BitString Probability
open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι]

/-- The *generalized inner product* of `k` strings of `n` bits held by the players `ι`: the parity
of the number of positions `r` at which every string has a `1`, `⊕_r ∧_i x i r`, computed in the
two-element Boolean ring. -/
def gip {n : ℕ} (x : ι → BitString n) : Bool :=
  ∑ r, ∏ i, x i r

/-- With two players, the generalized inner product is the inner product modulo two. -/
theorem gip_fin_two {n : ℕ} (x : Fin 2 → BitString n) : gip x = x 0 ⬝ᵥ x 1 := by
  simp only [gip, Fin.prod_univ_two, dotProduct]

end Cslib.Communication.NOF

namespace Cslib.BitString

open Finset

/-- The sign of a sum in the two-element Boolean ring is the product of the signs. -/
theorem signVal_sum {α : Type*} (s : Finset α) (f : α → Bool) :
    signVal (∑ a ∈ s, f a) = ∏ a ∈ s, signVal (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, prod_empty]; rfl
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, Bool.add_eq_xor, signVal_xor, ih]

/-- Reading a product of bits as a real number gives the product of the readings. -/
theorem bitVal_prod {α : Type*} (s : Finset α) (f : α → Bool) :
    bitVal ℝ (∏ a ∈ s, f a) = ∏ a ∈ s, bitVal ℝ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, prod_empty]; rfl
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, ← ih, Bool.mul_eq_and]
    cases f a <;> simp

end Cslib.BitString

namespace Cslib.Communication.NOF

open Finset Function BitString Probability
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The cube expectation of the generalized inner product is its bias**: over the corners of a
cube, the generalized inner product adds up to its value at `a + b`, by the distributive law
`∏ i, (b i + a i) = ∑ S, ∏_{i ∈ S} b i ∏_{i ∉ S} a i` in the Boolean ring, and `a + b` is
uniform. -/
theorem cubeExpectation_gip (n : ℕ) :
    cubeExpectation (X := fun _ : ι => BitString n) gip =
      𝔼 c : ι → BitString n, signVal (gip c) := by
  have key : ∀ a b : ι → BitString n,
      ∏ S : Finset ι, signVal (gip (S.piecewise b a)) = signVal (gip (b + a)) := by
    intro a b
    rw [← signVal_sum]
    congr 1
    simp only [gip]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun r _ => ?_
    simp only [Pi.add_apply]
    rw [Fintype.prod_add]
    refine sum_congr rfl fun S _ => ?_
    rw [← prod_mul_prod_compl S]
    congr 1
    · exact prod_congr rfl fun i hi => by rw [piecewise_eq_of_mem _ _ _ hi]
    · exact prod_congr rfl fun i hi => by rw [piecewise_eq_of_notMem _ _ _ (mem_compl.mp hi)]
  unfold cubeExpectation
  refine (Finset.expect_congr rfl fun a _ => Finset.expect_congr rfl fun b _ => key a b).trans ?_
  have hshift : ∀ a : ι → BitString n,
      𝔼 b : ι → BitString n, signVal (gip (b + a)) = 𝔼 c : ι → BitString n, signVal (gip c) :=
    fun a => Fintype.expect_equiv (Equiv.addRight a) _ _ fun _ => rfl
  rw [Finset.expect_congr rfl fun a _ => hshift a, Fintype.expect_const]

/-- **The bias of the generalized inner product** of `k` strings of `n` bits is
`(1 - 2 / 2 ^ k) ^ n`: the positions are independent, and at each the bits of the players are all
`1` with probability `2 ^ (-k)`. -/
theorem expect_signVal_gip (n : ℕ) :
    𝔼 c : ι → BitString n, signVal (gip c) = (1 - 2 / 2 ^ Fintype.card ι) ^ n := by
  simp only [gip, signVal_sum]
  rw [Fintype.expect_equiv (Equiv.piComm fun (_ : ι) (_ : Fin n) => Bool)
    (fun c : ι → Fin n → Bool => ∏ r, signVal (∏ i, c i r))
    (fun c' : Fin n → ι → Bool => ∏ r, signVal (∏ i, c' r i)) fun _ => rfl,
    ← Fintype.prod_expect (fun (_ : Fin n) (v : ι → Bool) => signVal (∏ i, v i)), prod_const,
    card_univ, Fintype.card_fin]
  congr 1
  simp only [signVal_eq_one_sub_two_mul_bitVal, bitVal_prod]
  rw [Finset.expect_sub_distrib, Fintype.expect_const, ← Finset.mul_expect,
    ← Fintype.prod_expect (fun (_ : ι) (b : Bool) => bitVal ℝ b)]
  simp only [Fintype.expect_bool, bitVal_false, bitVal_true, prod_const, card_univ]
  rw [zero_add, div_pow, one_pow, mul_one_div]

/-- **The discrepancy of the generalized inner product** under the uniform distribution:
`disc(GIP) ^ (2 ^ k) ≤ (1 - 2 / 2 ^ k) ^ n` for `k ≥ 1` players holding `n` bits each, by the cube
bound. -/
theorem discrepancy_gip_pow_le [Nonempty ι] (n : ℕ) :
    discrepancy (PMF.uniformOfFintype (ι → BitString n)) gip ^ (2 ^ Fintype.card ι) ≤
      (1 - 2 / 2 ^ Fintype.card ι) ^ n := by
  rw [← expect_signVal_gip, ← cubeExpectation_gip]
  exact discrepancy_uniformOfFintype_pow_le (X := fun _ : ι => BitString n) gip

/-- From a bound `A ^ (2 ^ k) ≤ 2 ^ (c 2 ^ k) (1 - 2 / 2 ^ k) ^ n` with `A⁻¹ ≤ exp m`, using
`1 - x ≤ exp (-x)`: `2 n ≤ 4 ^ k (c + m)`. -/
private theorem two_mul_le_of_pow_le {k n c : ℕ} (hk : k ≠ 0) {A m : ℝ} (hA : 0 < A)
    (hAm : A⁻¹ ≤ Real.exp m) (h : A ^ (2 ^ k) ≤ 2 ^ (c * 2 ^ k) * (1 - 2 / 2 ^ k) ^ n) :
    2 * (n : ℝ) ≤ 4 ^ k * (c + m) := by
  have hK : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two (Nat.one_le_iff_ne_zero.mpr hk)
  have hKpos : (0 : ℝ) < 2 ^ k := by positivity
  -- `(1 - 2 / 2 ^ k) ^ n ≤ exp (-2 n / 2 ^ k)`.
  have h0 : 0 ≤ 1 - 2 / (2 : ℝ) ^ k := by
    rw [sub_nonneg, div_le_one hKpos]
    exact hK
  have hexp : (1 - 2 / (2 : ℝ) ^ k) ^ n ≤ Real.exp (-(2 * n / 2 ^ k)) := by
    calc (1 - 2 / (2 : ℝ) ^ k) ^ n ≤ Real.exp (-(2 / 2 ^ k)) ^ n :=
          pow_le_pow_left₀ h0 (by linarith [Real.add_one_le_exp (-(2 / (2 : ℝ) ^ k))]) n
      _ = Real.exp (-(2 * n / 2 ^ k)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  -- `2 ^ (c 2 ^ k) ≤ exp (c 2 ^ k)` and `(A ^ (2 ^ k))⁻¹ ≤ exp (m 2 ^ k)`.
  have htwo : (2 : ℝ) ^ (c * 2 ^ k) ≤ Real.exp (c * 2 ^ k) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    calc (2 : ℝ) ^ (c * 2 ^ k) ≤ Real.exp 1 ^ (c * 2 ^ k) := by gcongr
      _ = Real.exp (c * 2 ^ k) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring_nf
  have hAinv : (A ^ (2 ^ k))⁻¹ ≤ Real.exp (m * 2 ^ k) := by
    calc (A ^ (2 ^ k))⁻¹ = A⁻¹ ^ (2 ^ k) := (inv_pow A _).symm
      _ ≤ Real.exp m ^ (2 ^ k) := pow_le_pow_left₀ (inv_nonneg.mpr hA.le) hAm _
      _ = Real.exp (m * 2 ^ k) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring_nf
  have hApos : 0 < A ^ (2 ^ k) := pow_pos hA _
  have h1 : 1 ≤ Real.exp (m * 2 ^ k + c * 2 ^ k + -(2 * n / 2 ^ k)) := by
    calc (1 : ℝ) = (A ^ (2 ^ k))⁻¹ * A ^ (2 ^ k) := (inv_mul_cancel₀ hApos.ne').symm
      _ ≤ Real.exp (m * 2 ^ k) * (Real.exp (c * 2 ^ k) * Real.exp (-(2 * n / 2 ^ k))) := by
          refine mul_le_mul hAinv (h.trans ?_) hApos.le (Real.exp_pos _).le
          exact mul_le_mul htwo hexp (pow_nonneg h0 _) (Real.exp_pos _).le
      _ = Real.exp (m * 2 ^ k + c * 2 ^ k + -(2 * n / 2 ^ k)) := by
          rw [Real.exp_add, Real.exp_add, mul_assoc]
  have h2 := Real.one_le_exp_iff.mp h1
  have h3 : 2 * (n : ℝ) / 2 ^ k ≤ (m + c) * 2 ^ k := by linarith
  rw [div_le_iff₀ hKpos] at h3
  have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by
    rw [← mul_pow]
    norm_num
  rw [h4]
  linarith

omit [DecidableEq ι] in
/-- **Randomized protocols for the generalized inner product**: if `k ≥ 1` players holding `n`
bits each compute the generalized inner product by a public-coin NOF protocol with error at most
`1 / 2 - γ`, for `γ ≥ 0`, sending at most `c` bits, then
`(2 γ) ^ (2 ^ k) ≤ 2 ^ (c 2 ^ k) (1 - 2 / 2 ^ k) ^ n`. -/
theorem PublicCoin.pow_le_of_ecomplexityFun_gip_le [Nonempty ι] {n c : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (h : PublicCoin.ecomplexityFun (1 / 2 - γ) (gip : (ι → BitString n) → Bool) ≤ c) :
    (2 * γ) ^ (2 ^ Fintype.card ι) ≤
      2 ^ (c * 2 ^ Fintype.card ι) * (1 - 2 / 2 ^ Fintype.card ι) ^ n := by
  classical
  have hd := PublicCoin.two_mul_le_two_pow_mul_discrepancy h
    (PMF.uniformOfFintype (ι → BitString n))
  calc (2 * γ) ^ (2 ^ Fintype.card ι)
      ≤ (2 ^ c * discrepancy (PMF.uniformOfFintype (ι → BitString n)) gip) ^
          (2 ^ Fintype.card ι) := pow_le_pow_left₀ (by positivity) hd _
    _ = 2 ^ (c * 2 ^ Fintype.card ι) *
          discrepancy (PMF.uniformOfFintype (ι → BitString n)) gip ^ (2 ^ Fintype.card ι) := by
        rw [mul_pow, pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (discrepancy_gip_pow_le n) (by positivity)

omit [DecidableEq ι] in
/-- **Babai–Nisan–Szegedy lower bound for the generalized inner product** [BabaiNisanSzegedy1992]:
public-coin NOF protocols of `k ≥ 1` players holding `n` bits each that compute the generalized
inner product with error at most `1 / 3`, sending at most `c` bits, have `2 n < 4 ^ k (c + 2)`:
`R_{1/3}(GIP) = Ω(n / 4 ^ k)`. The proof gives `2 n ≤ 4 ^ k (c + 3 / 2)`, from `3 ≤ exp (3 / 2)`. -/
theorem PublicCoin.two_mul_lt_four_pow_mul_of_ecomplexityFun_gip_le [Nonempty ι] {n c : ℕ}
    (h : PublicCoin.ecomplexityFun (1 / 3) (gip : (ι → BitString n) → Bool) ≤ c) :
    2 * n < 4 ^ Fintype.card ι * (c + 2) := by
  have h' : PublicCoin.ecomplexityFun (1 / 2 - 1 / 6) (gip : (ι → BitString n) → Bool) ≤ c := by
    rw [show (1 : ℝ) / 2 - 1 / 6 = 1 / 3 by norm_num]
    exact h
  have hp := PublicCoin.pow_le_of_ecomplexityFun_gip_le (by norm_num) h'
  have hm : (2 * (1 / 6 : ℝ))⁻¹ ≤ Real.exp (3 / 2) := by
    have h34 : (7 / 4 : ℝ) ≤ Real.exp (3 / 4) := by linarith [Real.add_one_le_exp (3 / 4)]
    rw [show (2 * (1 / 6 : ℝ))⁻¹ = 3 by norm_num, show (3 / 2 : ℝ) = 3 / 4 + 3 / 4 by norm_num,
      Real.exp_add]
    nlinarith
  have := two_mul_le_of_pow_le Fintype.card_ne_zero (by norm_num) hm hp
  have hk : (0 : ℝ) < 4 ^ Fintype.card ι := by positivity
  have hlt : 2 * (n : ℝ) < 4 ^ Fintype.card ι * (c + 2) := by nlinarith
  exact_mod_cast hlt

omit [DecidableEq ι] in
/-- **Deterministic protocols for the generalized inner product**: a deterministic NOF protocol of
`k ≥ 1` players holding `n` bits each computing the generalized inner product exactly, sending at
most `c` bits, has `2 n ≤ 4 ^ k c`. This cannot be strict: with `n = 0` the function is constant
and `c = 0`. -/
theorem Protocol.two_mul_le_four_pow_mul_of_ecomplexityFun_gip_le [Nonempty ι] {n c : ℕ}
    (h : Protocol.ecomplexityFun (gip : (ι → BitString n) → Bool) ≤ c) :
    2 * n ≤ 4 ^ Fintype.card ι * c := by
  classical
  have hd := Protocol.one_le_two_pow_mul_discrepancy_of_ecomplexityFun_le h
    (PMF.uniformOfFintype (ι → BitString n))
  have hp : (1 : ℝ) ^ (2 ^ Fintype.card ι) ≤
      2 ^ (c * 2 ^ Fintype.card ι) * (1 - 2 / 2 ^ Fintype.card ι) ^ n :=
    calc (1 : ℝ) ^ (2 ^ Fintype.card ι)
        ≤ (2 ^ c * discrepancy (PMF.uniformOfFintype (ι → BitString n)) gip) ^
            (2 ^ Fintype.card ι) := pow_le_pow_left₀ zero_le_one hd _
      _ = 2 ^ (c * 2 ^ Fintype.card ι) *
            discrepancy (PMF.uniformOfFintype (ι → BitString n)) gip ^ (2 ^ Fintype.card ι) := by
          rw [mul_pow, pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (discrepancy_gip_pow_le n) (by positivity)
  have := two_mul_le_of_pow_le Fintype.card_ne_zero zero_lt_one
    (by rw [inv_one, Real.exp_zero]) hp
  rw [add_zero] at this
  exact_mod_cast this

end Cslib.Communication.NOF
