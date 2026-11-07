/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PropertyTesting.Distribution.Basic
public import Complexity.Probability.IID.CrossCollisionCount
import Complexity.Probability.PMF
import Mathlib.Data.Nat.Choose.Cast

/-!
# The collision tester for closeness

Given `k` samples `x` of an unknown distribution `p` and `k` independent samples `y` of an unknown
distribution `q` on a finite type, the collision statistic of
[Diakonikolas–Gouleakis–Peebles–Price, §3][DiakonikolasGouleakisPeeblesPrice2019] is
`Z = C₁ + C₂ - ((k - 1) / k) C₃` (`closenessStatistic`). Here `C₁` and `C₂` count colliding pairs
within `x` and within `y` (`Cslib.Probability.PMF.collisionCount`), and `C₃` counts colliding pairs
across them (`Cslib.Probability.PMF.crossCollisionCount`). The statistic estimates the squared
`ℓ₂` distance without bias: `E[Z] = C(k, 2) ‖p - q‖₂²` (`sum_sum_iid_mul_closenessStatistic`).

The variance has a closed form (`sum_sum_iid_mul_closenessStatistic_sub_sq`). If
`‖p‖₂², ‖q‖₂² ≤ b`, it is at most `(k - 1) (2 k - 1) b + 2 (k - 1)² (k + 1) √b ‖p - q‖₂²`
(`sum_sum_iid_mul_closenessStatistic_sub_sq_le`). The tester (`closenessTester`) accepts when
`Z ≤ C(k, 2) ε² / 2`. By Chebyshev's inequality it distinguishes `‖p - q‖₂ ≤ ε / 2` from
`‖p - q‖₂ ≥ ε`, with error at most `δ` on each side, once `36 √b ≤ (k - 1) ε² δ`
(`le_acceptProb₂_closenessTester`, `acceptProb₂_closenessTester_le`). So `k = O(√b / ε²)` samples
suffice, as in
[Diakonikolas–Gouleakis–Peebles–Price, Theorem 8][DiakonikolasGouleakisPeeblesPrice2019]. The `ℓ₂`
tester goes back to [Batu–Fortnow–Rubinfeld–Smith–White][BatuFortnowRubinfeldSmithWhite2013].

Since `‖p‖₂² ≤ 1` and `n ‖p - q‖₂² ≥ 4 dist(p, q)²` on a domain of size `n`, this is in particular
a closeness tester in statistical distance with `k = O(n / ε²)` samples
(`isClosenessTester_closenessTester`). This sample complexity is not optimal, but it is the
`ℓ₂` step of the optimal tester, which flattens the distributions first.

The source bounds the variance by `116 k² b + 16 k³ ‖p - q‖₂² √b`
([Diakonikolas–Gouleakis–Peebles–Price, Lemma 10][DiakonikolasGouleakisPeeblesPrice2019]), with
section and theorem numbers following arXiv:1611.03579v1. Here the variance is computed exactly
from the cross-collision moments, and the constants `2`, `36` and `27` are the ones this proof
gives.

## Main definitions

* `Cslib.DistributionTesting.closenessStatistic`: the collision statistic `Z`.
* `Cslib.DistributionTesting.closenessThreshold`: the acceptance threshold `C(k, 2) ε² / 2`.
* `Cslib.DistributionTesting.closenessTester`: the collision tester for closeness.

## Main results

* `Cslib.DistributionTesting.sum_sum_iid_mul_closenessStatistic`: the mean of `Z`.
* `Cslib.DistributionTesting.sum_sum_iid_mul_closenessStatistic_sub_sq`: the variance of `Z`.
* `Cslib.DistributionTesting.sum_sum_iid_mul_closenessStatistic_sub_sq_le`: the variance bound.
* `Cslib.DistributionTesting.le_acceptProb₂_closenessTester`,
  `acceptProb₂_closenessTester_le`: the tolerant `ℓ₂` closeness tester.
* `Cslib.DistributionTesting.isClosenessTester_closenessTester`: a closeness tester in
  statistical distance.

## References

* [T. Batu, L. Fortnow, R. Rubinfeld, W. D. Smith and P. White, *Testing closeness of discrete
  distributions*][BatuFortnowRubinfeldSmithWhite2013]
* [I. Diakonikolas, T. Gouleakis, J. Peebles and E. Price, *Collision-based testers are optimal
  for uniformity and closeness*][DiakonikolasGouleakisPeeblesPrice2019]
-/

public section

namespace Cslib.DistributionTesting

open Cslib.Probability.PMF Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The collision statistic `C₁ + C₂ - ((k - 1) / k) C₃` of two samples: the colliding pairs within
each sample minus a rescaled count of the colliding pairs across them. -/
noncomputable def closenessStatistic {k : ℕ} (x y : Fin k → α) : ℝ :=
  collisionCount x + collisionCount y - ((k : ℝ) - 1) / k * crossCollisionCount x y

omit [Fintype α] in
/-- Unfolding lemma for `closenessStatistic`. -/
theorem closenessStatistic_eq {k : ℕ} (x y : Fin k → α) :
    closenessStatistic x y =
      collisionCount x + collisionCount y - ((k : ℝ) - 1) / k * crossCollisionCount x y := by
  rw [closenessStatistic]

/-- The acceptance threshold `C(k, 2) ε² / 2` of the closeness tester with `ℓ₂` proximity `ε`,
halfway between `0` and the expected statistic `C(k, 2) ε²` at `ℓ₂` distance `ε`. -/
noncomputable def closenessThreshold (k : ℕ) (ε : ℝ) : ℝ := k.choose 2 * ε ^ 2 / 2

/-- Unfolding lemma for `closenessThreshold`. -/
theorem closenessThreshold_eq (k : ℕ) (ε : ℝ) :
    closenessThreshold k ε = k.choose 2 * ε ^ 2 / 2 := by
  rw [closenessThreshold]

/-- The collision tester for closeness with `ℓ₂` proximity `ε`: it accepts two samples when their
collision statistic is at most `closenessThreshold`. -/
noncomputable def closenessTester (k : ℕ) (ε : ℝ) : (Fin k → α) → (Fin k → α) → PMF Bool :=
  fun x y => PMF.pure (decide (closenessStatistic x y ≤ closenessThreshold k ε))

omit [Fintype α] in
/-- Unfolding lemma for `closenessTester`. -/
theorem closenessTester_apply (k : ℕ) (ε : ℝ) (x y : Fin k → α) :
    closenessTester k ε x y = PMF.pure (decide (closenessStatistic x y ≤ closenessThreshold k ε)) :=
  by rw [closenessTester]

section Moments

variable (p q : PMF α) (k : ℕ)

omit [DecidableEq α] in
private theorem sum_sum_left (f : (Fin k → α) → ℝ) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * f x = ∑ x, (iid p k x).toReal * f x := by
  refine sum_congr rfl fun x _ => ?_
  calc ∑ y, (iid p k x).toReal * (iid q k y).toReal * f x
      = (iid p k x).toReal * f x * ∑ y, (iid q k y).toReal := by
        rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
    _ = (iid p k x).toReal * f x := by rw [sum_toReal, mul_one]

omit [DecidableEq α] in
private theorem sum_sum_right (g : (Fin k → α) → ℝ) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * g y = ∑ y, (iid q k y).toReal * g y := by
  rw [Finset.sum_comm]
  refine sum_congr rfl fun y _ => ?_
  calc ∑ x, (iid p k x).toReal * (iid q k y).toReal * g y
      = (iid q k y).toReal * g y * ∑ x, (iid p k x).toReal := by
        rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
    _ = (iid q k y).toReal * g y := by rw [sum_toReal, mul_one]

omit [DecidableEq α] in
private theorem sum_sum_mul (f g : (Fin k → α) → ℝ) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (f x * g y) =
      (∑ x, (iid p k x).toReal * f x) * ∑ y, (iid q k y).toReal * g y := by
  rw [sum_mul]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by ring

omit [DecidableEq α] in
private theorem sum_sum_const (c : ℝ) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * c = c := by
  calc ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * c = ∑ x, (iid p k x).toReal * c :=
        sum_sum_left p q k fun _ => c
    _ = c := by rw [← sum_mul, sum_toReal, one_mul]

omit [DecidableEq α] in
private theorem sum_sub_sq_eq :
    ∑ a, ((p a).toReal - (q a).toReal) ^ 2 =
      collisionProbability p + collisionProbability q - 2 * ∑ a, (p a).toReal * (q a).toReal := by
  rw [collisionProbability_eq_sum, collisionProbability_eq_sum, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  exact sum_congr rfl fun a _ => by ring

omit [DecidableEq α] in
/-- Expansion of the second moment of `A f₁ + A f₂ - L f₃ - m` over two independent samples, where
`f₁` depends on the first sample, `f₂` on the second and `f₃` on both. -/
private theorem sum_sum_sub_sq (L m : ℝ) (f₁ f₂ : (Fin k → α) → ℝ)
    (f₃ : (Fin k → α) → (Fin k → α) → ℝ) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (f₁ x + f₂ y - L * f₃ x y - m) ^ 2 =
      ∑ x, (iid p k x).toReal * f₁ x ^ 2 + ∑ y, (iid q k y).toReal * f₂ y ^ 2 +
        L ^ 2 * ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * f₃ x y ^ 2 + m ^ 2 +
        2 * ((∑ x, (iid p k x).toReal * f₁ x) * ∑ y, (iid q k y).toReal * f₂ y) -
        2 * L * ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (f₁ x * f₃ x y) -
        2 * L * ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (f₃ x y * f₂ y) -
        2 * m * ∑ x, (iid p k x).toReal * f₁ x - 2 * m * ∑ y, (iid q k y).toReal * f₂ y +
        2 * L * m * ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * f₃ x y := by
  rw [← sum_sum_left p q k (fun x => f₁ x ^ 2), ← sum_sum_right p q k (fun y => f₂ y ^ 2),
    ← sum_sum_mul, ← sum_sum_left p q k f₁, ← sum_sum_right p q k f₂]
  conv_rhs => rw [← sum_sum_const p q k (m ^ 2)]
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  ring

/-- **Mean of the collision statistic**: for `k` independent samples of each of `p` and `q`, the
expected collision statistic is `C(k, 2) ‖p - q‖₂²`
[Diakonikolas–Gouleakis–Peebles–Price, Lemma 9][DiakonikolasGouleakisPeeblesPrice2019]. -/
theorem sum_sum_iid_mul_closenessStatistic :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * closenessStatistic x y =
      k.choose 2 * ∑ a, ((p a).toReal - (q a).toReal) ^ 2 := by
  have h (x y : Fin k → α) : (iid p k x).toReal * (iid q k y).toReal * closenessStatistic x y =
      (iid p k x).toReal * (iid q k y).toReal * collisionCount x +
        (iid p k x).toReal * (iid q k y).toReal * collisionCount y -
        ((k : ℝ) - 1) / k *
          ((iid p k x).toReal * (iid q k y).toReal * crossCollisionCount x y) := by
    rw [closenessStatistic_eq]; ring
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [sum_sum_left p q k (fun x => (collisionCount x : ℝ)),
    sum_sum_right p q k (fun y => (collisionCount y : ℝ)), sum_iid_mul_collisionCount,
    sum_iid_mul_collisionCount, sum_sum_iid_mul_crossCollisionCount, sum_sub_sq_eq,
    Nat.cast_choose_two]
  rcases eq_or_ne (k : ℝ) 0 with hk | hk
  · rw [hk]; ring
  · field_simp

/-- **Variance of the collision statistic**: with `s = ‖p‖₂²`, `s' = ‖q‖₂²`, `t = ∑ a, p(a) q(a)`
and `R = ∑ a, (p(a) + q(a)) (p(a) - q(a))²`, the statistic of `k ≥ 1` samples of each has
variance `(k - 1) [k (s + s') / 2 + (k - 1) t + (k² - 1) R - (2 k - 1) (‖p‖₃³ + ‖q‖₃³) -
k (k - 1) ((s - t)² + (s' - t)²) + k (s² + s'²) / 2 + (k - 1) t²]`. -/
theorem sum_sum_iid_mul_closenessStatistic_sub_sq (hk : k ≠ 0) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal *
        (closenessStatistic x y - k.choose 2 * ∑ a, ((p a).toReal - (q a).toReal) ^ 2) ^ 2 =
      (k - 1) * (k / 2 * (collisionProbability p + collisionProbability q) +
        (k - 1) * ∑ a, (p a).toReal * (q a).toReal +
        (k ^ 2 - 1) * ∑ a, ((p a).toReal + (q a).toReal) * ((p a).toReal - (q a).toReal) ^ 2 -
        (2 * k - 1) * (∑ a, (p a).toReal ^ 3 + ∑ a, (q a).toReal ^ 3) -
        k * (k - 1) * ((collisionProbability p - ∑ a, (p a).toReal * (q a).toReal) ^ 2 +
          (collisionProbability q - ∑ a, (p a).toReal * (q a).toReal) ^ 2) +
        k / 2 * (collisionProbability p ^ 2 + collisionProbability q ^ 2) +
        (k - 1) * (∑ a, (p a).toReal * (q a).toReal) ^ 2) := by
  simp only [closenessStatistic_eq]
  rw [sum_sum_sub_sq, sum_iid_mul_collisionCount_sq, sum_iid_mul_collisionCount_sq,
    sum_sum_iid_mul_crossCollisionCount_sq, sum_sum_iid_mul_collisionCount_mul_crossCollisionCount,
    sum_sum_iid_mul_crossCollisionCount_mul_collisionCount, sum_iid_mul_collisionCount,
    sum_iid_mul_collisionCount, sum_sum_iid_mul_crossCollisionCount]
  have hR : ∑ a, ((p a).toReal + (q a).toReal) * ((p a).toReal - (q a).toReal) ^ 2 =
      ∑ a, (p a).toReal ^ 3 + ∑ a, (q a).toReal ^ 3 - ∑ a, (p a).toReal * (q a).toReal ^ 2 -
        ∑ a, (p a).toReal ^ 2 * (q a).toReal := by
    rw [← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun a _ => by ring
  rw [hR, sum_sub_sq_eq, Nat.cast_choose_two]
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  field_simp
  ring

end Moments

omit [DecidableEq α] in
/-- Jensen's inequality for the collision probability: `‖p‖₂⁴ ≤ ‖p‖₃³`. -/
private theorem collisionProbability_sq_le (p : PMF α) :
    collisionProbability p ^ 2 ≤ ∑ a, (p a).toReal ^ 3 := by
  have key (s : ℝ) : ∑ a, (p a).toReal * ((p a).toReal - s) ^ 2 =
      ∑ a, (p a).toReal ^ 3 - 2 * s * ∑ a, (p a).toReal ^ 2 + s ^ 2 * ∑ a, (p a).toReal := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  have h0 : 0 ≤ ∑ a, (p a).toReal * ((p a).toReal - ∑ b, (p b).toReal ^ 2) ^ 2 :=
    sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  rw [key, sum_toReal] at h0
  rw [collisionProbability_eq_sum]
  nlinarith

omit [Fintype α] [DecidableEq α] in
/-- Every mass is at most the square root of a bound on the collision probability. -/
private theorem toReal_le_sqrt [Finite α] (p : PMF α) {b : ℝ} (hb : collisionProbability p ≤ b)
    (a : α) : (p a).toReal ≤ Real.sqrt b := by
  cases nonempty_fintype α
  refine Real.le_sqrt_of_sq_le (le_trans ?_ hb)
  rw [collisionProbability_eq_sum]
  exact single_le_sum (f := fun a => (p a).toReal ^ 2) (fun _ _ => sq_nonneg _) (mem_univ a)

omit [Fintype α] [DecidableEq α] in
private theorem collisionProbability_pos [Finite α] (p : PMF α) : 0 < collisionProbability p := by
  cases nonempty_fintype α
  obtain ⟨a, ha⟩ := p.support_nonempty
  rw [collisionProbability_eq_sum]
  have hpos : 0 < (p a).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff p a).mp ha) (p.apply_ne_top a)
  exact lt_of_lt_of_le (by positivity)
    (single_le_sum (f := fun a => (p a).toReal ^ 2) (fun _ _ => sq_nonneg _) (mem_univ a))

/-- The bracket of the variance identity, bounded by the collision-probability bound `b`. -/
private theorem bracket_le {k s s' t c c' R b r D : ℝ} (hk : 1 ≤ k) (hs : s ≤ b) (hs' : s' ≤ b)
    (hc : s ^ 2 ≤ c) (hc' : s' ^ 2 ≤ c') (htt : t ^ 2 ≤ s * s') (ht : t ≤ (s + s') / 2)
    (hR : R ≤ 2 * r * D) :
    k / 2 * (s + s') + (k - 1) * t + (k ^ 2 - 1) * R - (2 * k - 1) * (c + c') -
        k * (k - 1) * ((s - t) ^ 2 + (s' - t) ^ 2) + k / 2 * (s ^ 2 + s' ^ 2) + (k - 1) * t ^ 2 ≤
      (2 * k - 1) * b + (k ^ 2 - 1) * (2 * r * D) := by
  have h1 : 0 ≤ (2 * k - 1) * (c - s ^ 2 + (c' - s' ^ 2)) := by
    have : 0 ≤ 2 * k - 1 := by linarith
    have : 0 ≤ c - s ^ 2 + (c' - s' ^ 2) := by linarith
    positivity
  have h2 : 0 ≤ (k - 1) * (s ^ 2 + s' ^ 2 - 2 * t ^ 2) := by
    have : 0 ≤ k - 1 := by linarith
    have : 0 ≤ s ^ 2 + s' ^ 2 - 2 * t ^ 2 := by nlinarith [sq_nonneg (s - s')]
    positivity
  have h3 : 0 ≤ k * (k - 1) * ((s - t) ^ 2 + (s' - t) ^ 2) := by
    have : 0 ≤ k - 1 := by linarith
    have : 0 ≤ k := by linarith
    positivity
  have h4 : 0 ≤ (2 * k - 1) * (s ^ 2 + s' ^ 2) := by
    have : 0 ≤ 2 * k - 1 := by linarith
    positivity
  have h5 : (k ^ 2 - 1) * R ≤ (k ^ 2 - 1) * (2 * r * D) :=
    mul_le_mul_of_nonneg_left hR (by nlinarith)
  have h6 : (k - 1) * t ≤ (k - 1) * b := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h7 : k / 2 * (s + s') ≤ k * b := by nlinarith
  nlinarith

/-- **Variance bound for the collision statistic**: if `‖p‖₂², ‖q‖₂² ≤ b`, the statistic of
`k ≥ 1` samples of each has variance at most
`(k - 1) (2 k - 1) b + 2 (k - 1)² (k + 1) √b ‖p - q‖₂²`. -/
theorem sum_sum_iid_mul_closenessStatistic_sub_sq_le (p q : PMF α) {k : ℕ} (hk : k ≠ 0)
    {b : ℝ} (hp : collisionProbability p ≤ b) (hq : collisionProbability q ≤ b) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal *
        (closenessStatistic x y - k.choose 2 * ∑ a, ((p a).toReal - (q a).toReal) ^ 2) ^ 2 ≤
      (k - 1) * (2 * k - 1) * b +
        2 * (k - 1) ^ 2 * (k + 1) * Real.sqrt b * ∑ a, ((p a).toReal - (q a).toReal) ^ 2 := by
  rw [sum_sum_iid_mul_closenessStatistic_sub_sq p q k hk]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have htt : (∑ a, (p a).toReal * (q a).toReal) ^ 2 ≤
      collisionProbability p * collisionProbability q := by
    rw [collisionProbability_eq_sum, collisionProbability_eq_sum]
    exact sum_mul_sq_le_sq_mul_sq _ _ _
  have ht : ∑ a, (p a).toReal * (q a).toReal ≤
      (collisionProbability p + collisionProbability q) / 2 := by
    rw [collisionProbability_eq_sum, collisionProbability_eq_sum, ← sum_add_distrib, sum_div]
    exact sum_le_sum fun a _ => by nlinarith [sq_nonneg ((p a).toReal - (q a).toReal)]
  have hR : ∑ a, ((p a).toReal + (q a).toReal) * ((p a).toReal - (q a).toReal) ^ 2 ≤
      2 * Real.sqrt b * ∑ a, ((p a).toReal - (q a).toReal) ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    linarith [toReal_le_sqrt p hp a, toReal_le_sqrt q hq a]
  have hbr := bracket_le hk1 hp hq (collisionProbability_sq_le p) (collisionProbability_sq_le q)
    htt ht hR
  have hk0 : (0 : ℝ) ≤ k - 1 := by linarith
  calc (k - 1 : ℝ) * _ ≤ (k - 1) * ((2 * k - 1) * b +
        (k ^ 2 - 1) * (2 * Real.sqrt b * ∑ a, ((p a).toReal - (q a).toReal) ^ 2)) :=
        mul_le_mul_of_nonneg_left hbr hk0
    _ = _ := by ring

omit [DecidableEq α] in
/-- **Chebyshev's inequality** over two independent samples. -/
private theorem mass_le {k : ℕ} (p q : PMF α) (A : (Fin k → α) → (Fin k → α) → Bool)
    (f : (Fin k → α) → (Fin k → α) → ℝ) (m c δ V : ℝ) (hc : 0 < c)
    (hA : ∀ x y, A x y → c ≤ |f x y - m|)
    (hV : ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (f x y - m) ^ 2 ≤ V)
    (hδ : V ≤ δ * c ^ 2) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (if A x y then 1 else 0) ≤ δ := by
  have h : (∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (if A x y then 1 else 0)) * c ^ 2 ≤
      ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal * (f x y - m) ^ 2 := by
    rw [sum_mul]
    refine sum_le_sum fun x _ => ?_
    rw [sum_mul]
    refine sum_le_sum fun y _ => ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    split_ifs with hxy
    · rw [one_mul, ← sq_abs (f x y - m)]
      exact pow_le_pow_left₀ hc.le (hA x y hxy) 2
    · rw [zero_mul]
      exact sq_nonneg _
  have hc2 : 0 < c ^ 2 := by positivity
  exact le_of_mul_le_mul_right (by linarith) hc2

/-- Completeness arithmetic, with `K = k - 1`, `S = √b` and `D = ‖p - q‖₂² ≤ ε² / 4`. -/
private theorem close_arith {K S ε δ D : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 36 * S ≤ K * ε ^ 2 * δ) (hD0 : 0 ≤ D) (hD : D ≤ ε ^ 2 / 4) :
    K * (2 * (K + 1) - 1) * S ^ 2 + 2 * K ^ 2 * (K + 1 + 1) * S * D ≤
      δ * ((K + 1) * K / 2 * ε ^ 2 / 4) ^ 2 := by
  have hε : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hS2 : S ^ 2 ≤ (K * ε ^ 2 * δ) ^ 2 / 1296 := by nlinarith
  have hA : K * (2 * (K + 1) - 1) ≤ 2 * (K + 1) ^ 2 := by nlinarith
  have hB : K * (K + 1 + 1) ≤ (K + 1) ^ 2 := by nlinarith
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hQ : 0 ≤ (K + 1) ^ 2 * K ^ 2 * ε ^ 4 := by positivity
  have h1 : K * (2 * (K + 1) - 1) * S ^ 2 ≤ 2 / 1296 * (K + 1) ^ 2 * K ^ 2 * ε ^ 4 * δ := by
    calc K * (2 * (K + 1) - 1) * S ^ 2 ≤ 2 * (K + 1) ^ 2 * ((K * ε ^ 2 * δ) ^ 2 / 1296) :=
          mul_le_mul hA hS2 (sq_nonneg S) (by positivity)
      _ = 2 / 1296 * (K + 1) ^ 2 * K ^ 2 * ε ^ 4 * δ ^ 2 := by ring
      _ ≤ 2 / 1296 * (K + 1) ^ 2 * K ^ 2 * ε ^ 4 * δ :=
          mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have h2 : 2 * K ^ 2 * (K + 1 + 1) * S * D ≤ 1 / 72 * (K + 1) ^ 2 * K ^ 2 * ε ^ 4 * δ := by
    have hSD : S * D ≤ K * ε ^ 2 * δ / 36 * (ε ^ 2 / 4) :=
      mul_le_mul (by linarith) hD hD0 (by positivity)
    calc 2 * K ^ 2 * (K + 1 + 1) * S * D = 2 * K * (K * (K + 1 + 1)) * (S * D) := by ring
      _ ≤ 2 * K * (K + 1) ^ 2 * (K * ε ^ 2 * δ / 36 * (ε ^ 2 / 4)) := by
          have h2K : 0 ≤ 2 * K := by positivity
          have hKK : 0 ≤ K * (K + 1 + 1) := by positivity
          calc 2 * K * (K * (K + 1 + 1)) * (S * D) ≤ 2 * K * (K + 1) ^ 2 * (S * D) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB h2K) (by positivity)
            _ ≤ 2 * K * (K + 1) ^ 2 * (K * ε ^ 2 * δ / 36 * (ε ^ 2 / 4)) :=
                mul_le_mul_of_nonneg_left hSD (by positivity)
      _ = 1 / 72 * (K + 1) ^ 2 * K ^ 2 * ε ^ 4 * δ := by ring
  have hgoal :
      δ * ((K + 1) * K / 2 * ε ^ 2 / 4) ^ 2 = 1 / 64 * (K + 1) ^ 2 * K ^ 2 * ε ^ 4 * δ := by
    ring
  rw [hgoal]
  have hQδ : 0 ≤ (K + 1) ^ 2 * K ^ 2 * ε ^ 4 * δ := by positivity
  nlinarith

/-- Soundness arithmetic, with `K = k - 1`, `S = √b` and `D = ‖p - q‖₂² ≥ ε²`. -/
private theorem far_arith {K S ε δ D : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 36 * S ≤ K * ε ^ 2 * δ) (hD : ε ^ 2 ≤ D) :
    K * (2 * (K + 1) - 1) * S ^ 2 + 2 * K ^ 2 * (K + 1 + 1) * S * D ≤
      δ * ((K + 1) * K / 2 * D / 2) ^ 2 := by
  have hε : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hD0 : 0 ≤ D := hε.trans hD
  have hkD : 36 * S ≤ K * D * δ := hk.trans (by gcongr)
  have hS2 : S ^ 2 ≤ (K * D * δ) ^ 2 / 1296 := by nlinarith
  have hA : K * (2 * (K + 1) - 1) ≤ 2 * (K + 1) ^ 2 := by nlinarith
  have hB : K * (K + 1 + 1) ≤ (K + 1) ^ 2 := by nlinarith
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have h1 : K * (2 * (K + 1) - 1) * S ^ 2 ≤ 2 / 1296 * (K + 1) ^ 2 * K ^ 2 * D ^ 2 * δ := by
    calc K * (2 * (K + 1) - 1) * S ^ 2 ≤ 2 * (K + 1) ^ 2 * ((K * D * δ) ^ 2 / 1296) :=
          mul_le_mul hA hS2 (sq_nonneg S) (by positivity)
      _ = 2 / 1296 * (K + 1) ^ 2 * K ^ 2 * D ^ 2 * δ ^ 2 := by ring
      _ ≤ 2 / 1296 * (K + 1) ^ 2 * K ^ 2 * D ^ 2 * δ :=
          mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have h2 : 2 * K ^ 2 * (K + 1 + 1) * S * D ≤ 1 / 18 * (K + 1) ^ 2 * K ^ 2 * D ^ 2 * δ := by
    have hSD : S * D ≤ K * D * δ / 36 * D := mul_le_mul_of_nonneg_right (by linarith) hD0
    have h2K : 0 ≤ 2 * K := by positivity
    calc 2 * K ^ 2 * (K + 1 + 1) * S * D = 2 * K * (K * (K + 1 + 1)) * (S * D) := by ring
      _ ≤ 2 * K * (K + 1) ^ 2 * (S * D) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB h2K) (by positivity)
      _ ≤ 2 * K * (K + 1) ^ 2 * (K * D * δ / 36 * D) :=
          mul_le_mul_of_nonneg_left hSD (by positivity)
      _ = 1 / 18 * (K + 1) ^ 2 * K ^ 2 * D ^ 2 * δ := by ring
  have hgoal : δ * ((K + 1) * K / 2 * D / 2) ^ 2 = 1 / 16 * (K + 1) ^ 2 * K ^ 2 * D ^ 2 * δ := by
    ring
  rw [hgoal]
  have hQδ : 0 ≤ (K + 1) ^ 2 * K ^ 2 * D ^ 2 * δ := by positivity
  nlinarith

omit [Fintype α] [DecidableEq α] in
/-- Shared setup: the sample-size hypothesis forces `k > 1` and `ε ≠ 0`. -/
private theorem setup [Finite α] {p : PMF α} {k : ℕ} {ε δ b : ℝ} (hδ : 0 < δ)
    (hp : collisionProbability p ≤ b) (hk : 36 * Real.sqrt b ≤ (k - 1) * ε ^ 2 * δ) :
    0 < (k : ℝ) - 1 ∧ k ≠ 0 ∧ 0 < ε ^ 2 := by
  have hb : 0 < b := (collisionProbability_pos p).trans_le hp
  have hS : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hε : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hK : 0 < (k : ℝ) - 1 := by
    by_contra h
    push Not at h
    have : ((k : ℝ) - 1) * ε ^ 2 * δ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h hε) hδ.le
    linarith
  refine ⟨hK, ?_, ?_⟩
  · rintro rfl
    norm_num at hK
  · rcases hε.lt_or_eq with h | h
    · exact h
    · rw [← h] at hk
      linarith

/-- **Completeness of the `ℓ₂` closeness tester**: if `‖p‖₂², ‖q‖₂² ≤ b`, `‖p - q‖₂ ≤ ε / 2` and
`36 √b ≤ (k - 1) ε² δ`, the tester accepts with probability at least `1 - δ`. -/
theorem le_acceptProb₂_closenessTester {p q : PMF α} {k : ℕ} {ε δ b : ℝ} (hδ : 0 < δ)
    (hp : collisionProbability p ≤ b) (hq : collisionProbability q ≤ b)
    (hk : 36 * Real.sqrt b ≤ (k - 1) * ε ^ 2 * δ)
    (hpq : ∑ a, ((p a).toReal - (q a).toReal) ^ 2 ≤ ε ^ 2 / 4) :
    1 - δ ≤ acceptProb₂ (closenessTester k ε) p q := by
  obtain ⟨hK, hk0, hε⟩ := setup hδ hp hk
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · have : 0 ≤ acceptProb₂ (closenessTester k ε) p q := by
      rw [acceptProb₂_eq]; exact ENNReal.toReal_nonneg
    linarith
  have hS : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hb : 0 ≤ b := ((collisionProbability_pos p).trans_le hp).le
  have hD0 : 0 ≤ ∑ a, ((p a).toReal - (q a).toReal) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hN : (k.choose 2 : ℝ) = ((k - 1 : ℝ) + 1) * (k - 1) / 2 := by
    rw [Nat.cast_choose_two]; ring
  unfold closenessTester
  rw [acceptProb₂_pure_eq_one_sub]
  suffices h : ∑ x, ∑ y, (iid p k x).toReal * (iid q k y).toReal *
      (if !decide (closenessStatistic x y ≤ closenessThreshold k ε) then 1 else 0) ≤ δ by
    linarith
  refine mass_le p q _ closenessStatistic _ (k.choose 2 * ε ^ 2 / 4) δ _ (by rw [hN]; positivity)
    ?_ (sum_sum_iid_mul_closenessStatistic_sub_sq_le p q hk0 hp hq) ?_
  · intro x y hxy
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_le, closenessThreshold_eq] at hxy
    rw [le_abs]
    left
    have : (k.choose 2 : ℝ) * ∑ a, ((p a).toReal - (q a).toReal) ^ 2 ≤
        k.choose 2 * (ε ^ 2 / 4) := mul_le_mul_of_nonneg_left hpq (by rw [hN]; positivity)
    linarith
  · have h := close_arith hK hS hδ hδ1.le hk hD0 hpq
    rw [hN]
    calc ((k : ℝ) - 1) * (2 * k - 1) * b + 2 * (k - 1) ^ 2 * (k + 1) * Real.sqrt b *
          ∑ a, ((p a).toReal - (q a).toReal) ^ 2
        = ((k : ℝ) - 1) * (2 * ((k - 1) + 1) - 1) * Real.sqrt b ^ 2 +
            2 * (k - 1) ^ 2 * ((k - 1) + 1 + 1) * Real.sqrt b *
              ∑ a, ((p a).toReal - (q a).toReal) ^ 2 := by
          rw [Real.sq_sqrt hb]; ring
      _ ≤ δ * (((k - 1 : ℝ) + 1) * (k - 1) / 2 * ε ^ 2 / 4) ^ 2 := h
      _ = δ * (((k - 1 : ℝ) + 1) * (k - 1) / 2 * ε ^ 2 / 4) ^ 2 := rfl

/-- **Soundness of the `ℓ₂` closeness tester**: if `‖p‖₂², ‖q‖₂² ≤ b`, `‖p - q‖₂ ≥ ε` and
`36 √b ≤ (k - 1) ε² δ`, the tester accepts with probability at most `δ`. -/
theorem acceptProb₂_closenessTester_le {p q : PMF α} {k : ℕ} {ε δ b : ℝ} (hδ : 0 < δ)
    (hp : collisionProbability p ≤ b) (hq : collisionProbability q ≤ b)
    (hk : 36 * Real.sqrt b ≤ (k - 1) * ε ^ 2 * δ)
    (hpq : ε ^ 2 ≤ ∑ a, ((p a).toReal - (q a).toReal) ^ 2) :
    acceptProb₂ (closenessTester k ε) p q ≤ δ := by
  obtain ⟨hK, hk0, hε⟩ := setup hδ hp hk
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · have : acceptProb₂ (closenessTester k ε) p q ≤ 1 := by
      rw [acceptProb₂_eq]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one
        (ENNReal.ofReal_one.symm ▸ PMF.coe_le_one _ true)
    linarith
  have hS : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hb : 0 ≤ b := ((collisionProbability_pos p).trans_le hp).le
  set D := ∑ a, ((p a).toReal - (q a).toReal) ^ 2 with hD
  have hD0 : 0 < D := hε.trans_le hpq
  have hN : (k.choose 2 : ℝ) = ((k - 1 : ℝ) + 1) * (k - 1) / 2 := by
    rw [Nat.cast_choose_two]; ring
  unfold closenessTester
  rw [acceptProb₂_pure]
  refine mass_le p q _ closenessStatistic _ (k.choose 2 * D / 2) δ _ (by rw [hN]; positivity)
    ?_ (sum_sum_iid_mul_closenessStatistic_sub_sq_le p q hk0 hp hq) ?_
  · intro x y hxy
    simp only [decide_eq_true_eq, closenessThreshold_eq] at hxy
    rw [le_abs]
    right
    have : (k.choose 2 : ℝ) * ε ^ 2 ≤ k.choose 2 * D :=
      mul_le_mul_of_nonneg_left hpq (by rw [hN]; positivity)
    linarith
  · have h := far_arith hK hS hδ hδ1.le hk hpq
    rw [hN]
    calc ((k : ℝ) - 1) * (2 * k - 1) * b + 2 * (k - 1) ^ 2 * (k + 1) * Real.sqrt b * D
        = ((k : ℝ) - 1) * (2 * ((k - 1) + 1) - 1) * Real.sqrt b ^ 2 +
            2 * (k - 1) ^ 2 * ((k - 1) + 1 + 1) * Real.sqrt b * D := by
          rw [Real.sq_sqrt hb]; ring
      _ ≤ δ * (((k - 1 : ℝ) + 1) * (k - 1) / 2 * D / 2) ^ 2 := h

omit [Fintype α] [DecidableEq α] in
private theorem collisionProbability_le_one [Finite α] (p : PMF α) :
    collisionProbability p ≤ 1 := by
  cases nonempty_fintype α
  rw [collisionProbability_eq_sum]
  calc ∑ a, (p a).toReal ^ 2 ≤ ∑ a, (p a).toReal := sum_le_sum fun a _ => by
        have h0 : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
        have h1 : (p a).toReal ≤ 1 :=
          ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one p a)
        nlinarith
    _ = 1 := sum_toReal p

/-- **A closeness tester in statistical distance**: on a domain of size `n`, the collision tester
with `ℓ₂` proximity `2 ε / √n` is a closeness tester with proximity `ε` whenever
`27 n ≤ (k - 1) ε²`. -/
theorem isClosenessTester_closenessTester {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 27 * (Fintype.card α : ℝ) ≤ (k - 1) * ε ^ 2) :
    IsClosenessTester (closenessTester (α := α) k (2 * ε / Real.sqrt (Fintype.card α))) ε := by
  have key : ∀ p : PMF α, 36 * Real.sqrt 1 ≤
      (k - 1) * (2 * ε / Real.sqrt (Fintype.card α)) ^ 2 * (1 / 3) := by
    intro p
    have hn : (0 : ℝ) < Fintype.card α := by
      have : Nonempty α := ⟨p.support_nonempty.some⟩
      exact_mod_cast Fintype.card_pos
    rw [Real.sqrt_one, div_pow, Real.sq_sqrt hn.le]
    rw [show ((k : ℝ) - 1) * ((2 * ε) ^ 2 / (Fintype.card α : ℝ)) * (1 / 3) =
      4 / 3 * (((k : ℝ) - 1) * ε ^ 2) / Fintype.card α by ring, le_div_iff₀ hn]
    linarith
  constructor
  · intro p
    have h := le_acceptProb₂_closenessTester (by norm_num : (0 : ℝ) < 1 / 3)
      (collisionProbability_le_one p) (collisionProbability_le_one p) (key p)
      (by simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sum_const_zero]; positivity)
    linarith
  · intro p q hpq
    have hn : (0 : ℝ) < Fintype.card α := by
      have : Nonempty α := ⟨p.support_nonempty.some⟩
      exact_mod_cast Fintype.card_pos
    refine acceptProb₂_closenessTester_le (by norm_num) (collisionProbability_le_one p)
      (collisionProbability_le_one q) (key p) ?_
    -- Cauchy–Schwarz: `(∑ |p - q|)² ≤ n ∑ (p - q)²`, and `∑ |p - q| = 2 dist p q ≥ 2 ε`.
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun a => |(p a).toReal - (q a).toReal|)
      (fun _ => (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, sum_const, card_univ, nsmul_eq_mul] at hcs
    have hsum : 2 * ε ≤ ∑ a, |(p a).toReal - (q a).toReal| := by
      have := hpq
      rw [dist_eq] at this
      linarith
    have h2 : (2 * ε) ^ 2 ≤ (∑ a, |(p a).toReal - (q a).toReal|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsum 2
    rw [div_pow, Real.sq_sqrt hn.le, div_le_iff₀ hn]
    nlinarith

end Cslib.DistributionTesting
