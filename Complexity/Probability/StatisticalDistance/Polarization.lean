/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.PolynomialBound.Log
public import Complexity.Probability.StatisticalDistance.DirectProduct
public import Complexity.Probability.StatisticalDistance.XOR
import Complexity.Foundations.Data.Nat.Log
import Complexity.Probability.StatisticalDistance.Product
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polarization of statistical distance

The Polarization Lemma of Sahai and Vadhan [SahaiVadhan2003, §3] turns a pair of distributions
whose statistical distance is either at least `α` or at most `β`, with `β < α²`, into a pair whose
distance is either at least `1 - 2⁻ᵏ` or at most `2⁻ᵏ`. It alternates the XOR construction
(`Cslib.Probability.PMF.xorMix`), which pushes small distances to `0`, with independent repetition
(`Cslib.Probability.PMF.iid`), which pushes large distances to `1`:

`polarize p₀ p₁ λ ℓ k c = xorMix (iid (xorMix p₀ p₁ λ false) ℓ) (iid (xorMix p₀ p₁ λ true) ℓ) k c`.

For `δ = dist p₀ p₁` the distance of the polarized pair is at most `(ℓ δ^λ)^k`
(`dist_polarize_le`) and, for `λ, k ≥ 1`, at least `1 - 2 k exp (-ℓ δ^(2λ) / 2)`
(`one_sub_two_mul_mul_exp_le_dist_polarize`). With `λ = m (⌊log₂ k⌋ + 1)` and
`ℓ = 2 ^ (b (⌊log₂ k⌋ + 1))` for constants `m, b` depending only on `α` and `β`, both parameters
are polynomial in `k` and the two bounds give the error `2⁻ᵏ` on each side
(`exists_polarization`). Clients obtain the constants with
`obtain ⟨m, b, hm, hlam, hell, h⟩ := exists_polarization hβ hβα hα hα1`.

This file works with explicit distributions on finite types. The efficient version on pairs of
circuits, where the polarized pair is computed from the input pair in polynomial time, is not
formalized here. The source is cited by section only: the lemma numbers in [SahaiVadhan2003] have
not been checked against a copy of the paper.

## Main definitions

* `Cslib.Probability.PMF.polarize`: the polarization construction.

## Main results

* `Cslib.Probability.PMF.dist_polarize_le`: the upper bound `(ℓ δ^λ)^k`.
* `Cslib.Probability.PMF.one_sub_two_mul_mul_exp_le_dist_polarize`: the lower bound
  `1 - 2 k exp (-ℓ δ^(2λ) / 2)`.
* `Cslib.Probability.PMF.exists_polarization`: the Polarization Lemma with polynomially bounded
  parameters, for constant thresholds `0 ≤ β < α² ≤ 1`.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

@[expose] public section

namespace Cslib.Probability.PMF

universe u

/-- The polarization construction [SahaiVadhan2003, §3]: the XOR construction on `k` coordinates
applied to `ℓ` independent copies of the XOR construction on `λ` coordinates. -/
noncomputable def polarize {Ω : Type*} [Fintype Ω] (p₀ p₁ : PMF Ω) (lam ell k : ℕ) (c : Bool) :
    PMF (Fin k → Fin ell → Fin lam → Ω) :=
  xorMix (iid (xorMix p₀ p₁ lam false) ell) (iid (xorMix p₀ p₁ lam true) ell) k c

/-- **Polarization, upper bound**: the polarized pair is at distance at most `(ℓ δ^λ)^k`, where
`δ = dist p₀ p₁`. -/
theorem dist_polarize_le {Ω : Type*} [Fintype Ω] (p₀ p₁ : PMF Ω) (lam ell k : ℕ) :
    dist (polarize p₀ p₁ lam ell k false) (polarize p₀ p₁ lam ell k true) ≤
      (ell * dist p₀ p₁ ^ lam) ^ k := by
  refine (dist_xorMix_le _ _ k).trans (pow_le_pow_left₀ dist_nonneg ?_ k)
  exact (dist_iid_le _ _ ell).trans
    (mul_le_mul_of_nonneg_left (dist_xorMix_le p₀ p₁ lam) (Nat.cast_nonneg ell))

/-- **Polarization, lower bound**: for `λ, k ≥ 1` the polarized pair is at distance at least
`1 - 2 k exp (-ℓ δ^(2λ) / 2)`, where `δ = dist p₀ p₁`. -/
theorem one_sub_two_mul_mul_exp_le_dist_polarize {Ω : Type*} [Fintype Ω] (p₀ p₁ : PMF Ω) {lam : ℕ}
    (hlam : lam ≠ 0) (ell : ℕ) {k : ℕ} (hk : k ≠ 0) :
    1 - 2 * k * Real.exp (-(ell * dist p₀ p₁ ^ (2 * lam)) / 2) ≤
      dist (polarize p₀ p₁ lam ell k false) (polarize p₀ p₁ lam ell k true) := by
  -- The direct-product lower bound for the inner pair, at distance `δ ^ λ`.
  have h := one_sub_two_mul_exp_le_dist_iid (xorMix p₀ p₁ lam false) (xorMix p₀ p₁ lam true) ell
  rw [dist_xorMix p₀ p₁ hlam, ← pow_mul, mul_comm lam 2] at h
  rw [polarize, polarize, dist_xorMix _ _ hk]
  set e := Real.exp (-(ell * dist p₀ p₁ ^ (2 * lam)) / 2)
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hk)
  have hpos : 0 ≤ e := (Real.exp_pos _).le
  rcases le_or_gt (2 * e) 1 with he | he
  · -- Bernoulli's inequality: `1 - 2 k e ≤ (1 - 2 e) ^ k`.
    calc 1 - 2 * k * e = 1 + k * -(2 * e) := by ring
      _ ≤ (1 + -(2 * e)) ^ k := one_add_mul_le_pow (by linarith) k
      _ ≤ _ := pow_le_pow_left₀ (by linarith) (by linarith) k
  · -- Otherwise the left side is negative.
    have : 1 - 2 * k * e ≤ 0 := by nlinarith
    exact this.trans (pow_nonneg dist_nonneg k)

/-- `2 k (1 / 2) ^ (2 k + 2) ≤ (1 / 2) ^ k`. -/
private theorem two_mul_half_pow_le (k : ℕ) :
    2 * k * (1 / 2 : ℝ) ^ (2 * k + 2) ≤ (1 / 2) ^ k := by
  have hk : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
  have hsplit : (1 / 2 : ℝ) ^ (2 * k + 2) = (1 / 2) ^ k * ((1 / 2) ^ k * (1 / 4)) := by
    rw [show 2 * k + 2 = k + (k + 2) by ring, pow_add, pow_add]
    norm_num
  have hhalf : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hsplit]
  have h0 : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  generalize (1 / 2 : ℝ) ^ k = x at h0 hhalf ⊢
  have hkx : k * x ≤ 1 := by nlinarith
  have hkxx : k * x * x ≤ x := by nlinarith
  nlinarith

/-- **Polarization Lemma** [SahaiVadhan2003, §3], for constant thresholds `0 ≤ β < α² ≤ 1`:
there are constants `m ≥ 1` and `b` such that, with `λ = m (⌊log₂ k⌋ + 1)` and
`ℓ = 2 ^ (b (⌊log₂ k⌋ + 1))`, both polynomially bounded in `k`, every pair at distance at least `α`
polarizes to distance at least `1 - 2⁻ᵏ` and every pair at distance at most `β` polarizes to
distance at most `2⁻ᵏ`. -/
theorem exists_polarization {α β : ℝ} (hβ : 0 ≤ β) (hβα : β < α ^ 2) (hα : 0 ≤ α)
    (hα1 : α ≤ 1) :
    ∃ m b : ℕ, m ≠ 0 ∧
      PolynomiallyBounded (fun k => m * (Nat.log 2 k + 1)) ∧
      PolynomiallyBounded (fun k => 2 ^ (b * (Nat.log 2 k + 1))) ∧
      ∀ {Ω : Type u} [Fintype Ω] (p₀ p₁ : PMF Ω) (k : ℕ),
        (α ≤ dist p₀ p₁ →
          1 - (1 / 2) ^ k ≤ dist (polarize p₀ p₁ (m * (Nat.log 2 k + 1))
            (2 ^ (b * (Nat.log 2 k + 1))) k false) (polarize p₀ p₁ (m * (Nat.log 2 k + 1))
            (2 ^ (b * (Nat.log 2 k + 1))) k true)) ∧
        (dist p₀ p₁ ≤ β →
          dist (polarize p₀ p₁ (m * (Nat.log 2 k + 1)) (2 ^ (b * (Nat.log 2 k + 1))) k false)
            (polarize p₀ p₁ (m * (Nat.log 2 k + 1)) (2 ^ (b * (Nat.log 2 k + 1))) k true) ≤
            (1 / 2) ^ k) := by
  have hα0 : 0 < α := by
    rcases hα.eq_or_lt with h | h
    · rw [← h] at hβα
      linarith [show (0 : ℝ) ^ 2 = 0 by norm_num]
    · exact h
  have hα2 : 0 < α ^ 2 := by positivity
  -- Choose `m` with `(β / α²) ^ m < 1 / 64`.
  have hr0 : 0 ≤ β / α ^ 2 := div_nonneg hβ hα2.le
  have hr1 : β / α ^ 2 < 1 := (div_lt_one hα2).2 hβα
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 64 by norm_num) hr1
  obtain ⟨m, hm⟩ : ∃ m, m = n + 1 := ⟨_, rfl⟩
  have hm0 : m ≠ 0 := by omega
  have hrm : (β / α ^ 2) ^ m < 1 / 64 :=
    (pow_le_pow_of_le_one hr0 hr1.le (show n ≤ m by omega)).trans_lt hn
  -- `A = α ^ (2 m)` bounds `δ ^ (2 m)` from below on the far side.
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = α ^ (2 * m) := ⟨_, rfl⟩
  have hA0 : 0 < A := hA ▸ pow_pos hα0 _
  have hA1 : A ≤ 1 := hA ▸ pow_le_one₀ hα hα1
  have hβm : β ^ m < A / 64 := by
    have : (β / α ^ 2) ^ m = β ^ m / A := by rw [hA, div_pow, pow_mul]
    rw [this, div_lt_iff₀ hA0] at hrm
    linarith
  -- Choose `b` with `8 / A ≤ 2 ^ b < 18 / A`.
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.clog 2 ⌈8 / A⌉₊ := ⟨_, rfl⟩
  have hceil0 : ⌈8 / A⌉₊ ≠ 0 := (Nat.ceil_pos.2 (by positivity)).ne'
  have hb_ge : 8 / A ≤ 2 ^ b := by
    have h₁ := Nat.le_ceil (8 / A)
    have h₂ : ((⌈8 / A⌉₊ : ℕ) : ℝ) ≤ ((2 ^ b : ℕ) : ℝ) := by
      rw [hb]
      exact_mod_cast Nat.le_pow_clog one_lt_two _
    push_cast at h₂
    linarith
  have hb_lt : (2 : ℝ) ^ b < 18 / A := by
    have h₁ : ((2 ^ b : ℕ) : ℝ) ≤ ((2 * ⌈8 / A⌉₊ : ℕ) : ℝ) := by
      rw [hb]
      exact_mod_cast Nat.pow_clog_le_mul one_lt_two hceil0
    have h₂ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 8 / A by positivity)
    push_cast at h₁
    have h₃ : 8 / A + 1 ≤ 9 / A := by
      rw [show (9 : ℝ) / A = 8 / A + 1 / A by ring]
      have : 1 ≤ 1 / A := by rw [le_div_iff₀ hA0]; linarith
      linarith
    have h₄ : (18 : ℝ) / A = 2 * (9 / A) := by ring
    linarith
  have hfar : 8 ≤ 2 ^ b * A := by
    rwa [div_le_iff₀ hA0] at hb_ge
  have hnear : 2 ^ b * β ^ m ≤ 1 / 2 := by
    have h₁ : 2 ^ b * β ^ m ≤ 18 / A * (A / 64) :=
      mul_le_mul hb_lt.le hβm.le (pow_nonneg hβ m) (by positivity)
    have h₂ : 18 / A * (A / 64) = 18 / 64 := by field_simp
    linarith
  refine ⟨m, b, hm0, ?_, polynomiallyBounded_two_pow_mul_log b, ?_⟩
  · simpa only [Nat.log2_eq_log_two] using polynomiallyBounded_mul_log2_add_one m
  intro Ω _ p₀ p₁ k
  -- The number of rounds `j = ⌊log₂ k⌋ + 1` satisfies `k + 1 ≤ 2 ^ j`.
  have hkj : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 k + 1) : ℕ) : ℝ) :=
    Nat.cast_le.2 (Nat.lt_pow_succ_log_self one_lt_two k)
  push_cast at hkj
  generalize hj : Nat.log 2 k + 1 = j at hkj ⊢
  have hj0 : j ≠ 0 := by
    rw [← hj]
    exact Nat.succ_ne_zero _
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [pow_zero, sub_self]
    exact ⟨fun _ => dist_nonneg, fun _ => dist_le_one _ _⟩
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hk)
  constructor
  · intro hd
    refine le_trans ?_
      (one_sub_two_mul_mul_exp_le_dist_polarize p₀ p₁ (Nat.mul_ne_zero hm0 hj0) _ hk)
    refine sub_le_sub_left ?_ 1
    -- The exponent is at least `(k + 1) ^ 3`.
    have hX : (k + 1 : ℝ) ^ 3 ≤
        ((2 ^ (b * j) : ℕ) : ℝ) * dist p₀ p₁ ^ (2 * (m * j)) := by
      have hdpow : (A ^ j : ℝ) ≤ dist p₀ p₁ ^ (2 * (m * j)) := by
        rw [hA, ← pow_mul, show 2 * m * j = 2 * (m * j) by ring]
        exact pow_le_pow_left₀ hα hd _
      calc (k + 1 : ℝ) ^ 3 ≤ ((2 : ℝ) ^ j) ^ 3 := pow_le_pow_left₀ (by positivity) hkj 3
        _ = (8 : ℝ) ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ (2 ^ b * A) ^ j := pow_le_pow_left₀ (by norm_num) hfar j
        _ = ((2 ^ (b * j) : ℕ) : ℝ) * A ^ j := by push_cast; rw [mul_pow, ← pow_mul]
        _ ≤ ((2 ^ (b * j) : ℕ) : ℝ) * dist p₀ p₁ ^ (2 * (m * j)) :=
          mul_le_mul_of_nonneg_left hdpow (by positivity)
    have hcube : 2 * (k + 1 : ℝ) ≤ (k + 1) ^ 3 / 2 := by
      have : 0 ≤ ((k : ℝ) - 1) * (k + 1) * (k + 3) := by
        apply mul_nonneg (mul_nonneg _ _) _ <;> linarith
      nlinarith
    have hexp : Real.exp (-(((2 ^ (b * j) : ℕ) : ℝ) * dist p₀ p₁ ^ (2 * (m * j))) / 2) ≤
        (1 / 2) ^ (2 * k + 2) := by
      calc Real.exp (-(((2 ^ (b * j) : ℕ) : ℝ) * dist p₀ p₁ ^ (2 * (m * j))) / 2)
          ≤ Real.exp (((2 * k + 2 : ℕ) : ℝ) * (-1)) := by
            apply Real.exp_le_exp.2
            push_cast at hX ⊢
            linarith
        _ = Real.exp (-1) ^ (2 * k + 2) := Real.exp_nat_mul _ _
        _ ≤ (1 / 2) ^ (2 * k + 2) :=
          pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le _
    calc 2 * (k : ℝ) * Real.exp (-(((2 ^ (b * j) : ℕ) : ℝ) * dist p₀ p₁ ^ (2 * (m * j))) / 2)
        ≤ 2 * k * (1 / 2) ^ (2 * k + 2) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (1 / 2) ^ k := two_mul_half_pow_le k
  · intro hd
    refine (dist_polarize_le p₀ p₁ _ _ k).trans (pow_le_pow_left₀ (by positivity) ?_ k)
    calc ((2 ^ (b * j) : ℕ) : ℝ) * dist p₀ p₁ ^ (m * j)
        ≤ ((2 ^ (b * j) : ℕ) : ℝ) * β ^ (m * j) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hd _) (by positivity)
      _ = (2 ^ b * β ^ m) ^ j := by push_cast; rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ (1 / 2) ^ j := pow_le_pow_left₀ (by positivity) hnear j
      _ ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) hj0

end Cslib.Probability.PMF
