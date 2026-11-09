/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Complexity.Probability.Product
public import Cslib.Probability.StatisticalDistance
import Complexity.Probability.PMF
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The XOR construction for statistical distance

Given two distributions `p₀` and `p₁` on a finite type, `xorMix p₀ p₁ k c` draws selector bits
`b : BitString k` uniformly among those of parity `c`, then draws coordinate `i` from `p_{b i}`,
independently. Statistical distance between `c = false` and `c = true` is multiplicative:
for `k ≥ 1`,

`dist (xorMix p₀ p₁ k false) (xorMix p₀ p₁ k true) = dist p₀ p₁ ^ k` (`dist_xorMix`).

This is the XOR Lemma of Sahai and Vadhan [SahaiVadhan2003, Lemma 3.5]. The construction pushes
small distances towards `0`. The proof writes the difference of the two masses at `x` as a signed
sum over selectors and factors it as `∏ i, (p₀ (x i) - p₁ (x i)) / 2 ^ (k - 1)`
(`toReal_xorMix_sub`); summing absolute values factors again over the coordinates.

When `k = 0` there are no selectors of parity `true`, and `xorMix` returns the product of copies of
`p₀` on both sides; the identity then fails, since `dist p₀ p₁ ^ 0 = 1`.

## Main definitions

* `Cslib.Probability.PMF.xorMix`: the XOR construction.

## Main results

* `Cslib.Probability.PMF.toReal_xorMix`: masses of the construction.
* `Cslib.Probability.PMF.toReal_xorMix_sub`: the difference of masses factors over coordinates.
* `Cslib.Probability.PMF.dist_xorMix`: the XOR Lemma.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

@[expose] public section

namespace Cslib.Probability.PMF

open Finset

variable {α : Type*} [Fintype α]

/-- The XOR construction [SahaiVadhan2003, Lemma 3.5]: draw selector bits `b` of `k` coordinates
uniformly among those of parity `c`, then draw coordinate `i` from `p₀` or `p₁` according to
`b i`, independently. With no selector of parity `c` (only when `k = 0` and `c = true`), it draws
from `p₀` in every coordinate. -/
noncomputable def xorMix (p₀ p₁ : PMF α) (k : ℕ) (c : Bool) : PMF (Fin k → α) :=
  if h : ({b : BitString k | parity k b = c} : Finset (BitString k)).Nonempty then
    (PMF.uniformOfFinset _ h).bind fun b => pi fun i => bif b i then p₁ else p₀
  else pi fun _ => p₀

omit [Fintype α] in
/-- The selector of a coordinate. -/
private theorem pi_apply_select [Finite α] (p₀ p₁ : PMF α) {k : ℕ} (b : BitString k)
    (x : Fin k → α) :
    (pi (fun i => bif b i then p₁ else p₀) x).toReal =
      ∏ i, ((bif b i then p₁ else p₀) (x i)).toReal := by
  rw [pi_apply, ENNReal.toReal_prod]

/-- The selectors of parity `c` on `k ≥ 1` coordinates are half of the bit strings. -/
private theorem card_selectors {k : ℕ} (hk : k ≠ 0) (c : Bool) :
    (#{b : BitString k | parity k b = c} : ℝ) = 2 ^ (k - 1) := by
  have hk1 := Nat.one_le_iff_ne_zero.2 hk
  cases c
  · rw [card_filter_parity_eq_false hk1, Nat.cast_pow, Nat.cast_ofNat]
  · rw [card_filter_parity_eq_true hk1, Nat.cast_pow, Nat.cast_ofNat]

/-- **Masses of the XOR construction**: for `k ≥ 1`, the average over the selectors of parity `c`
of the product of the selected masses. -/
theorem toReal_xorMix (p₀ p₁ : PMF α) {k : ℕ} (hk : k ≠ 0) (c : Bool) (x : Fin k → α) :
    (xorMix p₀ p₁ k c x).toReal =
      (∑ b : BitString k, if parity k b = c then
        ∏ i, ((bif b i then p₁ else p₀) (x i)).toReal else 0) / 2 ^ (k - 1) := by
  classical
  have hne : ({b : BitString k | parity k b = c} : Finset (BitString k)).Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := ℝ), card_selectors hk]
    positivity
  rw [xorMix, dite_eq_left hne, bind_apply_toReal, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [PMF.uniformOfFinset_apply, pi_apply_select]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs
  · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, card_selectors hk, inv_mul_eq_div]
  · rw [ENNReal.toReal_zero, zero_mul, zero_div]

/-- The sign `(-1) ^ (number of true bits)` as a product over the coordinates. -/
private theorem prod_sign {k : ℕ} (b : BitString k) :
    (∏ i, (bif b i then (-1 : ℝ) else 1)) = if parity k b = true then -1 else 1 := by
  classical
  have hprod : (∏ i, (bif b i then (-1 : ℝ) else 1)) =
      (-1) ^ #{i : Fin k | b i = true} := by
    rw [← Finset.prod_filter_mul_prod_filter_not univ fun i => b i = true]
    have h₁ : ∏ i ∈ univ with b i = true, (bif b i then (-1 : ℝ) else 1) =
        ∏ _i ∈ univ.filter (fun i => b i = true), (-1 : ℝ) :=
      Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2, Bool.cond_true]
    have h₂ : ∏ i ∈ univ with ¬b i = true, (bif b i then (-1 : ℝ) else 1) = 1 :=
      Finset.prod_eq_one fun i hi => by
        rw [Bool.eq_false_iff.2 (Finset.mem_filter.1 hi).2, Bool.cond_false]
    rw [h₁, h₂, Finset.prod_const, mul_one]
  rw [hprod, parity, parityOn]
  rcases Nat.mod_two_eq_zero_or_one #{i ∈ (univ : Finset (Fin k)) | b i = true} with h | h
  · rw [Even.neg_one_pow (Nat.even_iff.2 h)]
    simp [h]
  · rw [Odd.neg_one_pow (Nat.odd_iff.2 h)]
    simp [h]

/-- **The masses differ by a product**: for `k ≥ 1` the masses of the XOR construction for
`c = false` and `c = true` at `x` differ by `∏ i, (p₀ (x i) - p₁ (x i)) / 2 ^ (k - 1)`. -/
theorem toReal_xorMix_sub (p₀ p₁ : PMF α) {k : ℕ} (hk : k ≠ 0) (x : Fin k → α) :
    (xorMix p₀ p₁ k false x).toReal - (xorMix p₀ p₁ k true x).toReal =
      (∏ i, ((p₀ (x i)).toReal - (p₁ (x i)).toReal)) / 2 ^ (k - 1) := by
  classical
  rw [toReal_xorMix p₀ p₁ hk, toReal_xorMix p₀ p₁ hk, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  -- Expand the product of differences as a signed sum over the selectors.
  have hexp : (∏ i, ((p₀ (x i)).toReal - (p₁ (x i)).toReal)) =
      ∏ i, ∑ c : Bool, (bif c then (-1 : ℝ) else 1) *
        ((bif c then p₁ else p₀) (x i)).toReal := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [Bool.cond_true, Bool.cond_false]
    ring
  rw [hexp, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.prod_mul_distrib, prod_sign]
  cases parity k b <;> simp

/-- **XOR Lemma** [SahaiVadhan2003, Lemma 3.5]: for `k ≥ 1` coordinates, the XOR construction raises
the statistical distance to the `k`-th power. -/
theorem dist_xorMix (p₀ p₁ : PMF α) {k : ℕ} (hk : k ≠ 0) :
    dist (xorMix p₀ p₁ k false) (xorMix p₀ p₁ k true) = dist p₀ p₁ ^ k := by
  classical
  have h2 : (0 : ℝ) < 2 ^ (k - 1) := by positivity
  have hsum : ∑ x : Fin k → α,
      |(xorMix p₀ p₁ k false x).toReal - (xorMix p₀ p₁ k true x).toReal| =
        (∑ a, |(p₀ a).toReal - (p₁ a).toReal|) ^ k / 2 ^ (k - 1) := by
    simp only [toReal_xorMix_sub p₀ p₁ hk, abs_div, abs_of_pos h2, Finset.abs_prod]
    rw [← Finset.sum_div]
    congr 1
    have h := Finset.prod_univ_sum (fun _ : Fin k => (univ : Finset α))
      (fun _ a => |(p₀ a).toReal - (p₁ a).toReal|)
    rw [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    rw [h]
  rw [dist_eq, dist_eq, hsum, div_pow, div_div, ← pow_succ,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk)]

/-- The XOR construction never increases the statistical distance beyond its `k`-th power; for
`k = 0` the right side is `1`. -/
theorem dist_xorMix_le (p₀ p₁ : PMF α) (k : ℕ) :
    dist (xorMix p₀ p₁ k false) (xorMix p₀ p₁ k true) ≤ dist p₀ p₁ ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [pow_zero]
    exact dist_le_one _ _
  · exact (dist_xorMix p₀ p₁ hk).le

end Cslib.Probability.PMF
