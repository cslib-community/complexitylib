/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PropertyTesting.Distribution.Basic
public import Complexity.Probability.IID.CollisionCount
import Complexity.Probability.PMF
import Mathlib.Data.Nat.Choose.Cast

/-!
# The collision tester for uniformity

The collision tester of [Goldreich–Ron][GoldreichRon2000] draws `k` samples from an unknown
distribution `p` on a finite type of size `n` and accepts when the number of colliding pairs
(`Cslib.Probability.PMF.collisionCount`) is at most `C(k, 2) (1 + 2 ε²) / n`
(`collisionThreshold`). It is a uniformity tester with proximity `ε` in statistical distance
whenever `40 √n ≤ (k - 1) ε²` (`isTester_collisionTester`), so `k = O(√n / ε²)` samples suffice.
This sample complexity is optimal by Paninski's lower bound
(`Cslib.DistributionTesting.card_le_of_isTester_uniform`).

The proof is Chebyshev's inequality with the exact mean and variance of the collision count
(`Cslib.Probability.PMF.sum_iid_mul_collisionCount_sub_sq`), following the variance analysis of
[Diakonikolas–Gouleakis–Peebles–Price][DiakonikolasGouleakisPeeblesPrice2019]. Write
`s = ‖p‖₂²` and `D = s - 1 / n`. If `p` is uniform, `D = 0` and the variance is at most
`C(k, 2) / n`. If `p` is `ε`-far from uniform, Cauchy–Schwarz gives `n D ≥ 4 ε²`
(`Cslib.Probability.PMF.dist_uniform_sq_le`), and the excess third moment is at most
`D / n + √D D`. The original analysis [Goldreich–Ron][GoldreichRon2000] needed `O(√n / ε⁴)`
samples. The constant `40` is the one this proof gives; it is not optimized.

## Main definitions

* `Cslib.DistributionTesting.collisionThreshold`: the acceptance threshold.
* `Cslib.DistributionTesting.collisionTester`: the collision tester.

## Main results

* `Cslib.DistributionTesting.isTester_collisionTester`: the collision tester is a uniformity
  tester with `k = O(√n / ε²)` samples.

## References

* [O. Goldreich and D. Ron, *On testing expansion in bounded-degree graphs*][GoldreichRon2000]
* [I. Diakonikolas, T. Gouleakis, J. Peebles and E. Price, *Collision-based testers are optimal
  for uniformity and closeness*][DiakonikolasGouleakisPeeblesPrice2019]
* [C. L. Canonne, *A Survey on Distribution Testing: Your Data is Big. But is it
  Blue?*][Canonne2020]
-/

public section

namespace Cslib.DistributionTesting

open Cslib.Probability.PMF Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- Chebyshev's inequality for a finite distribution. -/
private theorem sum_mul_ite_le_sum_mul_sq_div (p : PMF α) (f : α → ℝ) (m : ℝ) {c : ℝ}
    (hc : 0 < c) (A : α → Bool) (hA : ∀ a, A a → c ≤ |f a - m|) :
    ∑ a, (p a).toReal * (if A a then 1 else 0) ≤ (∑ a, (p a).toReal * (f a - m) ^ 2) / c ^ 2 := by
  rw [le_div_iff₀ (by positivity), sum_mul]
  refine sum_le_sum fun a _ => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  split_ifs with h
  · rw [one_mul, ← sq_abs (f a - m)]
    exact pow_le_pow_left₀ hc.le (hA a h) 2
  · rw [zero_mul]
    exact sq_nonneg _

/-- The collision tester's threshold `C(k, 2) (1 + 2 ε²) / n`, halfway between the expected
collision counts `C(k, 2) / n` of the uniform distribution and `C(k, 2) (1 + 4 ε²) / n` of a
distribution `ε`-far from it. -/
noncomputable def collisionThreshold (n k : ℕ) (ε : ℝ) : ℝ := k.choose 2 * (1 + 2 * ε ^ 2) / n

/-- The collision tester accepts `k` samples when their number of colliding pairs is at most
`collisionThreshold`. -/
noncomputable def collisionTester (k : ℕ) (ε : ℝ) : (Fin k → α) → PMF Bool :=
  fun x => PMF.pure (decide ((collisionCount x : ℝ) ≤ collisionThreshold (Fintype.card α) k ε))

private theorem mass_le_one_third {k : ℕ} (p : PMF α) (A : (Fin k → α) → Bool) (m c : ℝ)
    (hc : 0 < c) (hA : ∀ x, A x → c ≤ |(collisionCount x : ℝ) - m|) {V : ℝ}
    (hV : ∑ x, (iid p k x).toReal * ((collisionCount x : ℝ) - m) ^ 2 ≤ V)
    (h3 : 3 * V ≤ c ^ 2) :
    ∑ x, (iid p k x).toReal * (if A x then 1 else 0) ≤ 1 / 3 := by
  refine (sum_mul_ite_le_sum_mul_sq_div _ _ m hc A hA).trans ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

omit [DecidableEq α] in
/-- With `D = ‖p‖₂² - 1 / n`, the third moment exceeds the squared collision probability by at
most `D / n + √D D`. -/
private theorem sum_cube_sub_sq_le [Nonempty α] (p : PMF α) :
    ∑ a, (p a).toReal ^ 3 - collisionProbability p ^ 2 ≤
      (collisionProbability p - (Fintype.card α : ℝ)⁻¹) * (Fintype.card α : ℝ)⁻¹ +
        Real.sqrt (collisionProbability p - (Fintype.card α : ℝ)⁻¹) *
          (collisionProbability p - (Fintype.card α : ℝ)⁻¹) := by
  set n : ℝ := (Fintype.card α : ℝ) with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast Fintype.card_ne_zero
  obtain ⟨d, hd⟩ : ∃ d : α → ℝ, ∀ a, (p a).toReal = n⁻¹ + d a :=
    ⟨fun a => (p a).toReal - n⁻¹, fun a => by ring⟩
  have hsum : ∑ a, d a = 0 := by
    have h := sum_toReal p
    simp only [hd, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← hn,
      mul_inv_cancel₀ hn0] at h
    linarith
  obtain ⟨D, hD⟩ : ∃ D, D = ∑ a, d a ^ 2 := ⟨_, rfl⟩
  have hs : collisionProbability p = n⁻¹ + D := by
    rw [collisionProbability_eq_sum, hD]
    have h (a : α) : (p a).toReal ^ 2 = n⁻¹ * n⁻¹ + 2 * n⁻¹ * d a + d a ^ 2 := by
      rw [hd]; ring
    simp only [h, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← hn, ← mul_sum, hsum,
      mul_zero, add_zero, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have ht : ∑ a, (p a).toReal ^ 3 = n⁻¹ * n⁻¹ + 3 * n⁻¹ * D + ∑ a, d a ^ 3 := by
    rw [hD]
    have h (a : α) : (p a).toReal ^ 3 =
        n⁻¹ * (n⁻¹ * n⁻¹) + 3 * (n⁻¹ * n⁻¹) * d a + 3 * n⁻¹ * d a ^ 2 + d a ^ 3 := by
      rw [hd]; ring
    simp only [h, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← hn, ← mul_sum, hsum,
      mul_zero, add_zero, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have hcube : ∑ a, d a ^ 3 ≤ Real.sqrt D * D := by
    calc ∑ a, d a ^ 3 ≤ ∑ a, Real.sqrt D * d a ^ 2 := by
          refine sum_le_sum fun a _ => ?_
          have h1 : |d a| ≤ Real.sqrt D := Real.abs_le_sqrt (by
            rw [hD]; exact single_le_sum (fun b _ => sq_nonneg (d b)) (mem_univ a))
          calc d a ^ 3 = d a * d a ^ 2 := by ring
            _ ≤ Real.sqrt D * d a ^ 2 :=
              mul_le_mul_of_nonneg_right ((le_abs_self _).trans h1) (sq_nonneg _)
      _ = Real.sqrt D * D := by rw [← mul_sum, hD]
  rw [hs, ht, add_sub_cancel_left]
  nlinarith [sq_nonneg D]

/-- Far-case arithmetic, with `q = √n`, `w = √(n D)` and `K = k - 1`. -/
private theorem far_arith {q w K ε : ℝ} (hq : 1 ≤ q) (hε : 0 < ε) (hε1 : ε ≤ 1) (hw : 2 * ε ≤ w)
    (hK : 40 * q ≤ K * ε ^ 2) :
    24 * q ^ 2 * (1 + w ^ 2) + 48 * K * (w ^ 2 + q * w ^ 3) ≤ K ^ 2 * w ^ 4 := by
  have hw0 : 0 < w := by linarith
  have hK0 : 0 < K := by
    by_contra h
    nlinarith [sq_nonneg ε]
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have h4 : 4 * ε ^ 2 ≤ w ^ 2 := by nlinarith
  have hKw2 : 160 * q ≤ K * w ^ 2 := by nlinarith
  have hK40 : 40 * q ≤ K := by nlinarith
  have hKw : 80 * q ≤ K * w := by
    have : 2 * K * ε ^ 2 ≤ K * w * ε := by nlinarith
    nlinarith
  set Z := K * w ^ 2 with hZ
  have hZ0 : 0 < Z := by positivity
  have t1 : 24 * q ^ 2 ≤ 24 / 25600 * Z ^ 2 := by nlinarith
  have t2 : 24 * q ^ 2 * w ^ 2 ≤ 24 / 6400 * Z ^ 2 := by
    have h1 : 6400 * q ^ 2 ≤ K ^ 2 * w ^ 2 := by
      have : K ^ 2 * w ^ 2 = K * (K * w ^ 2) := by ring
      rw [this]
      nlinarith
    have : Z ^ 2 = (K ^ 2 * w ^ 2) * w ^ 2 := by rw [hZ]; ring
    rw [this]
    nlinarith [sq_nonneg w]
  have t3 : 48 * K * w ^ 2 ≤ 48 / 160 * Z ^ 2 := by nlinarith
  have t4 : 48 * K * (q * w ^ 3) ≤ 48 / 80 * Z ^ 2 := by
    have : 48 * K * (q * w ^ 3) = 48 * q * (K * w ^ 3) := by ring
    nlinarith
  have hsum : K ^ 2 * w ^ 4 = Z ^ 2 := by rw [hZ]; ring
  rw [hsum]
  nlinarith

/-- The far-case Chebyshev condition, with `q = √n`, `r = √D` and `K = k - 1`. -/
private theorem far_variance_le {q r K ε : ℝ} (hq : 1 ≤ q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 0 ≤ r) (hw : 2 * ε ≤ q * r) (hK : 40 * q ≤ K * ε ^ 2) :
    3 * ((K + 1) * K / 2 * (1 / q ^ 2 + r ^ 2) +
        (K + 1) * K * (K - 1) * (r ^ 2 * (1 / q ^ 2) + r * r ^ 2)) ≤
      ((K + 1) * K / 2 * (r ^ 2 - 2 * ε ^ 2 / q ^ 2)) ^ 2 := by
  have key := far_arith hq hε hε1 hw hK
  have hq0 : 0 < q := by linarith
  have hK0 : 0 < K := by nlinarith [sq_nonneg ε]
  set w := q * r with hw_def
  have hw0 : 0 ≤ w := by positivity
  set N := (K + 1) * K / 2 with hN
  have hN0 : 0 < N := by positivity
  have hlhs : 3 * (N * (1 / q ^ 2 + r ^ 2) + (K + 1) * K * (K - 1) * (r ^ 2 * (1 / q ^ 2) +
      r * r ^ 2)) =
      3 * (N * q ^ 2 * (1 + w ^ 2) + 2 * N * (K - 1) * (w ^ 2 + q * w ^ 3)) / q ^ 4 := by
    rw [hw_def, hN]; field_simp
  have hrhs : (N * (r ^ 2 - 2 * ε ^ 2 / q ^ 2)) ^ 2 = N ^ 2 * (w ^ 2 - 2 * ε ^ 2) ^ 2 / q ^ 4 := by
    rw [hw_def]; field_simp
  rw [hlhs, hrhs, div_le_div_iff_of_pos_right (by positivity)]
  have hX : 0 ≤ w ^ 2 + q * w ^ 3 := by positivity
  have h1 : 2 * N * (K - 1) * (w ^ 2 + q * w ^ 3) ≤ 2 * N * K * (w ^ 2 + q * w ^ 3) := by
    nlinarith
  have h2 : w ^ 2 / 2 ≤ w ^ 2 - 2 * ε ^ 2 := by nlinarith
  have h3 : (w ^ 2 / 2) ^ 2 ≤ (w ^ 2 - 2 * ε ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have h4 : K ^ 2 ≤ 2 * N := by rw [hN]; nlinarith
  calc 3 * (N * q ^ 2 * (1 + w ^ 2) + 2 * N * (K - 1) * (w ^ 2 + q * w ^ 3))
      ≤ N / 8 * (24 * q ^ 2 * (1 + w ^ 2) + 48 * K * (w ^ 2 + q * w ^ 3)) := by linarith
    _ ≤ N / 8 * (K ^ 2 * w ^ 4) := mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ N / 8 * (2 * N * w ^ 4) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (by positivity)) (by positivity)
    _ = N ^ 2 * (w ^ 2 / 2) ^ 2 := by ring
    _ ≤ N ^ 2 * (w ^ 2 - 2 * ε ^ 2) ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)

variable [Nonempty α]

/-- **The collision tester is a uniformity tester** with `k = O(√n / ε²)` samples. -/
theorem isTester_collisionTester {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 40 * Real.sqrt (Fintype.card α) ≤ (k - 1) * ε ^ 2) :
    IsTester (collisionTester (α := α) k ε) {uniformOfFintype α} ε := by
  set n : ℝ := (Fintype.card α : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hn0 : 0 < n := by linarith
  set q := Real.sqrt n with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact Real.one_le_sqrt.mpr hn1
  have hqn : q ^ 2 = n := Real.sq_sqrt hn0.le
  set K : ℝ := (k : ℝ) - 1 with hK
  have hK0 : 0 < K := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg ε]
  have hk2 : 2 ≤ k := by
    have : (1 : ℝ) < k := by rw [hK] at hK0; linarith
    exact_mod_cast this
  have hK1 : 1 ≤ K := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    rw [hK]; linarith
  have hkK : (k : ℝ) = K + 1 := by rw [hK]; ring
  set N : ℝ := (k.choose 2 : ℝ) with hN
  have hNK : N = (K + 1) * K / 2 := by rw [hN, Nat.cast_choose_two, hkK]; ring
  have hN0 : 0 < N := by rw [hNK]; positivity
  have hM : (k : ℝ) * (k - 1) * (k - 2) = (K + 1) * K * (K - 1) := by rw [hkK]; ring
  have hM0 : 0 ≤ (K + 1) * K * (K - 1) := by
    have : 0 ≤ K - 1 := by linarith
    positivity
  have h1600 : 1600 * n ≤ (K * ε ^ 2) ^ 2 := by
    rw [← hqn]
    nlinarith
  have hτ : collisionThreshold (Fintype.card α) k ε = N * (1 + 2 * ε ^ 2) / n := rfl
  constructor
  · intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    have hcp : collisionProbability (uniformOfFintype α) = n⁻¹ := by
      rw [hn]; exact collisionProbability_uniform
    have hcube : ∑ a, ((uniformOfFintype α) a).toReal ^ 3 = n⁻¹ ^ 2 := by
      simp only [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        sum_const, card_univ, nsmul_eq_mul, ← hn]
      field_simp
    unfold collisionTester
    rw [acceptProb_pure_eq_one_sub]
    suffices h : ∑ x, (iid (uniformOfFintype α) k x).toReal *
        (if !decide ((collisionCount x : ℝ) ≤ collisionThreshold (Fintype.card α) k ε) then 1
          else 0) ≤ 1 / 3 by linarith
    refine mass_le_one_third _
      (fun x => !decide ((collisionCount x : ℝ) ≤ collisionThreshold (Fintype.card α) k ε)) _
      (2 * N * ε ^ 2 / n) (by positivity) ?_ (sum_iid_mul_collisionCount_sub_sq _ k).le ?_
    · intro x hx
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_le] at hx
      rw [hτ] at hx
      rw [← hN, hcp, le_abs]
      left
      have : 2 * N * ε ^ 2 / n = N * (1 + 2 * ε ^ 2) / n - N * n⁻¹ := by field_simp; ring
      linarith
    · rw [← hN, hcp, hcube, sub_self, mul_zero, add_zero]
      have hle : 3 * (N * (n⁻¹ - n⁻¹ ^ 2)) ≤ 3 * N / n := by
        have : 0 ≤ n⁻¹ ^ 2 := sq_nonneg _
        rw [div_eq_mul_inv]
        nlinarith
      refine hle.trans ?_
      rw [div_pow, mul_pow, mul_pow, div_le_div_iff₀ hn0 (by positivity)]
      have h4 : 3 * n ≤ 4 * N * ε ^ 4 := by
        rw [hNK]
        nlinarith [mul_pos hK0 (pow_pos hε 4)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (mul_pos hN0 hn0).le]
  · intro p hp
    have hfar : ε ≤ dist p (uniformOfFintype α) := hp _ rfl
    have hε1 : ε ≤ 1 := hfar.trans (dist_le_one _ _)
    have hsq := dist_uniform_sq_le p
    rw [← hn] at hsq
    set s := collisionProbability p with hs
    set D := s - n⁻¹ with hD
    have hnD : 4 * ε ^ 2 ≤ n * D := by
      have : ε ^ 2 ≤ dist p (uniformOfFintype α) ^ 2 := pow_le_pow_left₀ hε.le hfar 2
      have : n * D = n * s - 1 := by rw [hD, mul_sub, mul_inv_cancel₀ hn0.ne']
      nlinarith
    have hD0 : 0 < D := by
      by_contra h
      push Not at h
      nlinarith [pow_pos hε 2]
    set r := Real.sqrt D with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrD : r ^ 2 = D := Real.sq_sqrt hD0.le
    have hw : 2 * ε ≤ q * r := by
      have h2 : (2 * ε) ^ 2 ≤ (q * r) ^ 2 := by rw [mul_pow q r 2, hqn, hrD]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2
    unfold collisionTester
    rw [acceptProb_pure]
    refine mass_le_one_third _
      (fun x => decide ((collisionCount x : ℝ) ≤ collisionThreshold (Fintype.card α) k ε)) _
      (N * (D - 2 * ε ^ 2 / n)) ?_ ?_ (sum_iid_mul_collisionCount_sub_sq _ k).le ?_
    · have : 2 * ε ^ 2 / n < D := by
        rw [div_lt_iff₀ hn0]
        nlinarith [pow_pos hε 2]
      exact mul_pos hN0 (by linarith)
    · intro x hx
      simp only [decide_eq_true_eq] at hx
      have hτ' : collisionThreshold (Fintype.card α) k ε = N * s - N * (D - 2 * ε ^ 2 / n) := by
        rw [hτ, hD]; field_simp; ring
      rw [hτ'] at hx
      rw [← hN, ← hs, le_abs]
      right
      linarith
    · have hcube := sum_cube_sub_sq_le p
      rw [← hn, ← hs, ← hD, ← hr] at hcube
      rw [← hN, ← hs, hM]
      calc 3 * (N * (s - s ^ 2) + (K + 1) * K * (K - 1) * (∑ a, (p a).toReal ^ 3 - s ^ 2))
          ≤ 3 * (N * s + (K + 1) * K * (K - 1) * (D * n⁻¹ + r * D)) := by
            have h1 : 0 ≤ N * s ^ 2 := by positivity
            have h2 := mul_le_mul_of_nonneg_left hcube hM0
            linarith
        _ = 3 * ((K + 1) * K / 2 * (1 / q ^ 2 + r ^ 2) +
            (K + 1) * K * (K - 1) * (r ^ 2 * (1 / q ^ 2) + r * r ^ 2)) := by
            have hsD : s = n⁻¹ + D := by rw [hD]; ring
            rw [hNK, hqn, hrD, hsD]
            ring
        _ ≤ ((K + 1) * K / 2 * (r ^ 2 - 2 * ε ^ 2 / q ^ 2)) ^ 2 :=
            far_variance_le hq1 hε hε1 hr0 hw hk
        _ = (N * (D - 2 * ε ^ 2 / n)) ^ 2 := by rw [hNK, hqn, hrD]

end Cslib.DistributionTesting
