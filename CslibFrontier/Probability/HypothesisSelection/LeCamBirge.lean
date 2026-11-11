/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Hellinger
public import CslibFrontier.Probability.IID
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.Event
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Robust Le Cam–Birgé and Scheffé pairwise tests

This module constructs robust pairwise hypothesis tests between finite discrete distributions:

1. **Hellinger Le Cam–Birgé test (`leCamBirgeTest`):** compares the product of clipped
   midpoint likelihood-ratio square roots `birgeWeight q₀ q₁ (x i) = √((q₀ + 2 q₁) / (2 q₀ + q₁))`
   against threshold `1`. Unlike the bare likelihood ratio `q₀^n ≤ q₁^n`, `birgeWeight` takes
   values in `[1 / √2, √2]` everywhere, making it robust under arbitrary Hellinger perturbations:
   under any unknown distribution `p` with `10 * h(p, q₀) ≤ h(q₀, q₁)` (in particular `h(p, q₀) ≤ r`
   when `10 * r ≤ h(q₀, q₁)`), the probability of rejecting `q₀` is at most
   `Real.exp (-n * h²(q₀, q₁) / 25)` (this `1/3`–`2/3` clipped `birgeWeight` formulation and its
   explicit constants are proved in this library; see [LeCam1973] and [Birge1983] as background).
2. **Total-variation Scheffé test (`scheffeTest`):** compares the empirical mass of the Scheffé
   set `scheffeSet q₀ q₁ = {a | q₁(a) < q₀(a)}` against the midpoint `(q₀(A) + q₁(A)) / 2`.
   Under any distribution `p` with `dist p q₀ + γ ≤ dist q₀ q₁ / 2` (in particular `dist p q₀ ≤ r`
   and `3 * r + 2 * γ ≤ dist p q₁`), the error probability is at most `Real.exp (-2 * n * γ ^ 2)`
   (this Hoeffding-based formulation and proof are this library's formulation; see
   [DevroyeLugosi2001] as background).

## Main definitions

* `Cslib.Probability.HypothesisSelection.birgeWeight`,
  `Cslib.Probability.HypothesisSelection.leCamBirgeTest`: Birgé's bounded likelihood-ratio
  statistic and pairwise Hellinger test.
* `Cslib.Probability.HypothesisSelection.scheffeSet`,
  `Cslib.Probability.HypothesisSelection.empiricalMass`,
  `Cslib.Probability.HypothesisSelection.scheffeTest`: Scheffé witness set, empirical frequency,
  and pairwise TV test.

## Main results

* `Cslib.Probability.HypothesisSelection.sum_mul_birgeWeight_le_of_mul`: Hellinger-ball drift
  bound `∑ a, p(a) * birgeWeight q₀ q₁ a ≤ 1 - h²(q₀, q₁) / 25` when `10 * h(p, q₀) ≤ h(q₀, q₁)`.
* `Cslib.Probability.HypothesisSelection.leCamBirgeTest_false_le`,
  `Cslib.Probability.HypothesisSelection.leCamBirgeTest_true_le`: two-sided exponential error
  bounds for `leCamBirgeTest`.
* `Cslib.Probability.HypothesisSelection.abs_empiricalMass_sub_ge_le`: Hoeffding concentration for
  `empiricalMass`.
* `Cslib.Probability.HypothesisSelection.scheffeTest_false_le`,
  `Cslib.Probability.HypothesisSelection.scheffeTest_true_le`: one-sided exponential error bounds
  for `scheffeTest`.

## References

* [L. Le Cam, *Convergence of estimates under dimensionality restrictions*, Ann. Statist. 1(1),
  38–53, 1973][LeCam1973] (bibliographic metadata only; article text not inspected).
* [L. Birgé, *Approximation dans les espaces métriques et théorie de l'estimation*, Z. Wahrsch.
  Verw. Gebiete 65, 181–237, 1983][Birge1983] (bibliographic metadata only; article text not
  inspected).
* [L. Devroye, G. Lugosi, *Combinatorial Methods in Density Estimation*][DevroyeLugosi2001]
  (bibliographic metadata only; book text not inspected, no chapter/theorem numbers claimed).
-/

public section

namespace Cslib.Probability.HypothesisSelection

open Cslib.Probability.PMF Finset
open scoped BigOperators ENNReal

variable {α : Type*}

section HellingerTest

private noncomputable def birgeScalar (a b : ℝ) : ℝ :=
  if 2 * a ^ 2 + b ^ 2 = 0 then 1
  else Real.sqrt ((a ^ 2 + 2 * b ^ 2) / (2 * a ^ 2 + b ^ 2))

private theorem birgeScalar_pos {a b : ℝ} : 0 < birgeScalar a b := by
  dsimp only [birgeScalar]
  split_ifs with h0
  · exact zero_lt_one
  · have hden : 0 < 2 * a ^ 2 + b ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hnum : 0 < a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact Real.sqrt_pos.mpr (div_pos hnum hden)

private theorem birgeScalar_le_sqrt_two {a b : ℝ} : birgeScalar a b ≤ Real.sqrt 2 := by
  dsimp only [birgeScalar]
  split_ifs with h0
  · exact Real.one_le_sqrt.mpr (by norm_num)
  · have hden : 0 < 2 * a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg a, sq_nonneg b]

private theorem birgeScalar_symm (a b : ℝ) :
    birgeScalar b a = (birgeScalar a b)⁻¹ := by
  dsimp only [birgeScalar]
  by_cases h0 : 2 * a ^ 2 + b ^ 2 = 0
  · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    simp [ha, hb]
  · have h0' : 2 * b ^ 2 + a ^ 2 ≠ 0 := by
      intro hba
      apply h0
      linarith [sq_nonneg a, sq_nonneg b]
    simp only [h0', h0, ↓reduceIte, ← Real.sqrt_inv, inv_div]
    congr 1
    ring

private theorem sq_mul_birgeScalar_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * birgeScalar a b + (b ^ 2 - a ^ 2) / 3 ≤
      (a ^ 2 + b ^ 2) / 2 - (a - b) ^ 2 / 8 := by
  dsimp only [birgeScalar]
  split_ifs with h0
  · have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb0 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    simp [ha0, hb0]
  · have hden : 0 < 2 * a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hrhs_eq :
        (a ^ 2 + b ^ 2) / 2 - (a - b) ^ 2 / 8 - (b ^ 2 - a ^ 2) / 3 =
          (17 * a ^ 2 + 6 * a * b + b ^ 2) / 24 := by
      ring
    suffices h : a ^ 2 * Real.sqrt ((a ^ 2 + 2 * b ^ 2) / (2 * a ^ 2 + b ^ 2)) ≤
        (17 * a ^ 2 + 6 * a * b + b ^ 2) / 24 by
      linarith
    have hrhs_nonneg : 0 ≤ (17 * a ^ 2 + 6 * a * b + b ^ 2) / 24 := by positivity
    refine le_of_sq_le_sq ?_ hrhs_nonneg
    rw [mul_pow, Real.sq_sqrt (div_nonneg (by positivity) hden.le), ← pow_mul]
    rw [mul_div_assoc', div_le_iff₀ hden]
    have hpoly :
        ((17 * a ^ 2 + 6 * a * b + b ^ 2) / 24) ^ 2 * (2 * a ^ 2 + b ^ 2) -
            a ^ 4 * (a ^ 2 + 2 * b ^ 2) =
          (a - b) ^ 2 *
            (2 * a ^ 4 + 412 * a ^ 3 * b + 99 * a ^ 2 * b ^ 2 + 14 * a * b ^ 3 + b ^ 4) /
              576 := by
      ring
    have hpos : 0 ≤
        (a - b) ^ 2 *
          (2 * a ^ 4 + 412 * a ^ 3 * b + 99 * a ^ 2 * b ^ 2 + 14 * a * b ^ 3 + b ^ 4) / 576 := by
      positivity
    linarith

private theorem mul_abs_birgeScalar_sub_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * |birgeScalar a b - 1| ≤ |a - b| / 2 := by
  dsimp only [birgeScalar]
  split_ifs with h0
  · have hnonneg : 0 ≤ |a - b| / 2 := by positivity
    simpa using hnonneg
  · have hden : 0 < 2 * a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    set w := Real.sqrt ((a ^ 2 + 2 * b ^ 2) / (2 * a ^ 2 + b ^ 2))
    have hw_nonneg : 0 ≤ w := Real.sqrt_nonneg _
    have hw1 : 0 < w + 1 := by linarith
    have hw_sq : w ^ 2 - 1 = (b ^ 2 - a ^ 2) / (2 * a ^ 2 + b ^ 2) := by
      dsimp only [w]
      rw [Real.sq_sqrt (div_nonneg (by positivity) hden.le), div_sub_one hden.ne']
      ring
    have habs_w : |w - 1| * (w + 1) = |a - b| * (a + b) / (2 * a ^ 2 + b ^ 2) := by
      calc |w - 1| * (w + 1)
          = |w - 1| * |w + 1| := by rw [abs_of_pos hw1]
        _ = |(w - 1) * (w + 1)| := (abs_mul _ _).symm
        _ = |w ^ 2 - 1| := by ring_nf
        _ = |(b ^ 2 - a ^ 2) / (2 * a ^ 2 + b ^ 2)| := by rw [hw_sq]
        _ = |b ^ 2 - a ^ 2| / (2 * a ^ 2 + b ^ 2) := by rw [abs_div, abs_of_pos hden]
        _ = |a - b| * (a + b) / (2 * a ^ 2 + b ^ 2) := by
            have hdiff : b ^ 2 - a ^ 2 = -(a - b) * (a + b) := by ring
            rw [hdiff, abs_mul, abs_neg, abs_of_nonneg (add_nonneg ha hb)]
    have hkey : 2 * (a * (a + b)) ≤ (2 * a ^ 2 + b ^ 2) * (w + 1) := by
      have hmul : (2 * a ^ 2 + b ^ 2) * w =
          Real.sqrt ((2 * a ^ 2 + b ^ 2) * (a ^ 2 + 2 * b ^ 2)) := by
        calc (2 * a ^ 2 + b ^ 2) * w
            = Real.sqrt ((2 * a ^ 2 + b ^ 2) ^ 2) *
                Real.sqrt ((a ^ 2 + 2 * b ^ 2) / (2 * a ^ 2 + b ^ 2)) := by
              rw [Real.sqrt_sq hden.le]
          _ = Real.sqrt ((2 * a ^ 2 + b ^ 2) ^ 2 *
                ((a ^ 2 + 2 * b ^ 2) / (2 * a ^ 2 + b ^ 2))) :=
              (Real.sqrt_mul (sq_nonneg _) _).symm
          _ = Real.sqrt ((2 * a ^ 2 + b ^ 2) * (a ^ 2 + 2 * b ^ 2)) := by
              congr 1
              field_simp [hden.ne']
      have hgoal : 2 * a * b - b ^ 2 ≤ (2 * a ^ 2 + b ^ 2) * w := by
        rw [hmul]
        by_cases h2ab : 2 * a * b - b ^ 2 ≤ 0
        · exact h2ab.trans (Real.sqrt_nonneg _)
        · refine Real.le_sqrt_of_sq_le ?_
          have hdiff :
              (2 * a ^ 2 + b ^ 2) * (a ^ 2 + 2 * b ^ 2) - (2 * a * b - b ^ 2) ^ 2 =
                2 * a ^ 4 + a ^ 2 * b ^ 2 + 4 * a * b ^ 3 + b ^ 4 := by
            ring
          have hpos : 0 ≤ 2 * a ^ 4 + a ^ 2 * b ^ 2 + 4 * a * b ^ 3 + b ^ 4 := by positivity
          linarith
      linarith
    have hcoeff : a * (a + b) / ((2 * a ^ 2 + b ^ 2) * (w + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (mul_pos hden hw1) zero_lt_two]
      linarith
    calc a * |w - 1|
        = a * (|w - 1| * (w + 1)) / (w + 1) := by field_simp [hw1.ne']
      _ = |a - b| * (a * (a + b) / ((2 * a ^ 2 + b ^ 2) * (w + 1))) := by
          rw [habs_w]
          field_simp [hden.ne', hw1.ne']
      _ ≤ |a - b| * (1 / 2) := mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)
      _ = |a - b| / 2 := by ring

/-- Clipped midpoint likelihood-ratio square root used by Le Cam and Birgé's pairwise Hellinger
test: `√((q₀(a) + 2 q₁(a)) / (2 q₀(a) + q₁(a)))`, defaulting to `1` when both distributions vanish
at `a`. It always lies in `[1 / √2, √2]`. -/
noncomputable def birgeWeight (q₀ q₁ : _root_.PMF α) (a : α) : ℝ :=
  birgeScalar (Real.sqrt (q₀ a).toReal) (Real.sqrt (q₁ a).toReal)

/-- Explicit formula for `birgeWeight q₀ q₁ a` in terms of `q₀ a` and `q₁ a`. -/
theorem birgeWeight_eq (q₀ q₁ : _root_.PMF α) (a : α) :
    birgeWeight q₀ q₁ a =
      if 2 * (q₀ a).toReal + (q₁ a).toReal = 0 then 1
      else Real.sqrt (((q₀ a).toReal + 2 * (q₁ a).toReal) /
        (2 * (q₀ a).toReal + (q₁ a).toReal)) := by
  simp only [birgeWeight, birgeScalar, Real.sq_sqrt ENNReal.toReal_nonneg]

/-- Positivity of `birgeWeight q₀ q₁ a`. -/
theorem birgeWeight_pos (q₀ q₁ : _root_.PMF α) (a : α) : 0 < birgeWeight q₀ q₁ a :=
  birgeScalar_pos

/-- Upper bound `birgeWeight q₀ q₁ a ≤ √2`. -/
theorem birgeWeight_le_sqrt_two (q₀ q₁ : _root_.PMF α) (a : α) :
    birgeWeight q₀ q₁ a ≤ Real.sqrt 2 :=
  birgeScalar_le_sqrt_two

/-- Swapping `q₀` and `q₁` inverts `birgeWeight q₀ q₁ a`. -/
theorem birgeWeight_symm (q₀ q₁ : _root_.PMF α) (a : α) :
    birgeWeight q₁ q₀ a = (birgeWeight q₀ q₁ a)⁻¹ :=
  birgeScalar_symm _ _

/-- Lower bound `1 / √2 ≤ birgeWeight q₀ q₁ a`. -/
theorem inv_sqrt_two_le_birgeWeight (q₀ q₁ : _root_.PMF α) (a : α) :
    (Real.sqrt 2)⁻¹ ≤ birgeWeight q₀ q₁ a := by
  rw [← inv_inv (birgeWeight q₀ q₁ a), ← birgeWeight_symm]
  exact inv_anti₀ birgeScalar_pos birgeScalar_le_sqrt_two

/-- General Hellinger drift bound for `birgeWeight` under an arbitrary distribution `p`:
`∑ a, p(a) * birgeWeight q₀ q₁ a ≤
  1 - h²(q₀, q₁) / 4 + 2 (√2 - 1) h²(p, q₀) + 2 h(p, q₀) h(q₀, q₁)`. -/
theorem sum_mul_birgeWeight_le [Fintype α] (p q₀ q₁ : _root_.PMF α) :
    ∑ a, (p a).toReal * birgeWeight q₀ q₁ a ≤
      1 - hellingerSq q₀ q₁ / 4 + 2 * (Real.sqrt 2 - 1) * hellingerSq p q₀ +
        2 * hellingerDist p q₀ * hellingerDist q₀ q₁ := by
  let u : α → ℝ := fun x => Real.sqrt (p x).toReal
  let a : α → ℝ := fun x => Real.sqrt (q₀ x).toReal
  let b : α → ℝ := fun x => Real.sqrt (q₁ x).toReal
  let w : α → ℝ := fun x => birgeWeight q₀ q₁ x
  have hu2 (x : α) : u x ^ 2 = (p x).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have ha2 (x : α) : a x ^ 2 = (q₀ x).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hb2 (x : α) : b x ^ 2 = (q₁ x).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hsum_q0 :
      ∑ x, (q₀ x).toReal * w x ≤ 1 - hellingerSq q₀ q₁ / 4 := by
    have hpt (x : α) :
        a x ^ 2 * w x + (b x ^ 2 - a x ^ 2) / 3 ≤ (a x ^ 2 + b x ^ 2) / 2 - (a x - b x) ^ 2 / 8 :=
      sq_mul_birgeScalar_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsum := Finset.sum_le_sum fun x (_ : x ∈ (Finset.univ : Finset α)) => hpt x
    simp_rw [ha2, hb2] at hsum
    have hzero : ∑ x : α, ((q₁ x).toReal - (q₀ x).toReal) / 3 = 0 := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_toReal, sum_toReal, sub_self, zero_div]
    have hone : ∑ x : α, ((q₀ x).toReal + (q₁ x).toReal) / 2 = 1 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, sum_toReal, sum_toReal]
      norm_num
    have hhell : ∑ x : α, (a x - b x) ^ 2 / 8 = hellingerSq q₀ q₁ / 4 := by
      rw [← Finset.sum_div, hellingerSq_eq_sum]
      ring
    rw [Finset.sum_add_distrib, hzero, add_zero, Finset.sum_sub_distrib, hone, hhell] at hsum
    exact hsum
  have hterm1 :
      ∑ x : α, (u x - a x) ^ 2 * (w x - 1) ≤ 2 * (Real.sqrt 2 - 1) * hellingerSq p q₀ := by
    have hpt (x : α) : (u x - a x) ^ 2 * (w x - 1) ≤ (Real.sqrt 2 - 1) * (u x - a x) ^ 2 := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (sub_le_sub_right (birgeWeight_le_sqrt_two q₀ q₁ x) 1)
        (sq_nonneg _)
    calc ∑ x : α, (u x - a x) ^ 2 * (w x - 1)
        ≤ ∑ x : α, (Real.sqrt 2 - 1) * (u x - a x) ^ 2 := Finset.sum_le_sum fun x _ => hpt x
      _ = (Real.sqrt 2 - 1) * (2 * hellingerSq p q₀) := by
          rw [← Finset.mul_sum, hellingerSq_eq_sum]
          ring
      _ = 2 * (Real.sqrt 2 - 1) * hellingerSq p q₀ := by ring
  have hterm2 :
      ∑ x : α, 2 * a x * (u x - a x) * (w x - 1) ≤
        2 * hellingerDist p q₀ * hellingerDist q₀ q₁ := by
    have hpt (x : α) : 2 * a x * (u x - a x) * (w x - 1) ≤ |u x - a x| * |a x - b x| := by
      calc 2 * a x * (u x - a x) * (w x - 1)
          ≤ |2 * a x * (u x - a x) * (w x - 1)| := le_abs_self _
        _ = 2 * |u x - a x| * (a x * |w x - 1|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
              abs_of_nonneg (Real.sqrt_nonneg _)]
            ring
        _ ≤ 2 * |u x - a x| * (|a x - b x| / 2) :=
            mul_le_mul_of_nonneg_left
              (mul_abs_birgeScalar_sub_one_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
              (by positivity)
        _ = |u x - a x| * |a x - b x| := by ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
      (fun x => |u x - a x|) (fun x => |a x - b x|)
    have h1 : ∑ x : α, |u x - a x| ^ 2 = 2 * hellingerSq p q₀ := by
      simp_rw [sq_abs]
      rw [hellingerSq_eq_sum]
      ring
    have h2 : ∑ x : α, |a x - b x| ^ 2 = 2 * hellingerSq q₀ q₁ := by
      simp_rw [sq_abs]
      rw [hellingerSq_eq_sum]
      ring
    rw [h1, h2] at hcs
    have hsqrt : ∑ x : α, |u x - a x| * |a x - b x| ≤
        2 * hellingerDist p q₀ * hellingerDist q₀ q₁ := by
      refine le_of_sq_le_sq ?_
        (mul_nonneg (mul_nonneg (by norm_num) (hellingerDist_nonneg _ _))
          (hellingerDist_nonneg _ _))
      calc (∑ x : α, |u x - a x| * |a x - b x|) ^ 2
          ≤ (2 * hellingerSq p q₀) * (2 * hellingerSq q₀ q₁) := hcs
        _ = (2 * hellingerDist p q₀ * hellingerDist q₀ q₁) ^ 2 := by
            rw [← hellingerDist_sq p q₀, ← hellingerDist_sq q₀ q₁]
            ring
    exact (Finset.sum_le_sum fun x _ => hpt x).trans hsqrt
  have hdiff_eq :
      ∑ x : α, (p x).toReal * w x - ∑ x : α, (q₀ x).toReal * w x =
        ∑ x : α, (u x - a x) ^ 2 * (w x - 1) +
          ∑ x : α, 2 * a x * (u x - a x) * (w x - 1) := by
    have hsum0 : ∑ x : α, ((p x).toReal - (q₀ x).toReal) = 0 := by
      rw [Finset.sum_sub_distrib, sum_toReal, sum_toReal, sub_self]
    have hpt (x : α) :
        (p x).toReal * w x - (q₀ x).toReal * w x - ((p x).toReal - (q₀ x).toReal) =
          (u x - a x) ^ 2 * (w x - 1) + 2 * a x * (u x - a x) * (w x - 1) := by
      rw [← hu2 x, ← ha2 x]
      ring
    rw [← Finset.sum_sub_distrib]
    calc ∑ x : α, ((p x).toReal * w x - (q₀ x).toReal * w x)
        = ∑ x : α, ((p x).toReal * w x - (q₀ x).toReal * w x) -
            ∑ x : α, ((p x).toReal - (q₀ x).toReal) := by rw [hsum0, sub_zero]
      _ = ∑ x : α, ((p x).toReal * w x - (q₀ x).toReal * w x -
            ((p x).toReal - (q₀ x).toReal)) := (Finset.sum_sub_distrib _ _).symm
      _ = ∑ x : α, ((u x - a x) ^ 2 * (w x - 1) + 2 * a x * (u x - a x) * (w x - 1)) := by
          simp_rw [hpt]
      _ = _ := Finset.sum_add_distrib
  linarith

/-- Robust Hellinger-ball drift bound: whenever `10 * hellingerDist p q₀ ≤ hellingerDist q₀ q₁`,
`∑ a, (p a).toReal * birgeWeight q₀ q₁ a ≤ 1 - hellingerSq q₀ q₁ / 25`. -/
theorem sum_mul_birgeWeight_le_of_mul [Fintype α] {p q₀ q₁ : _root_.PMF α}
    (hsep : 10 * hellingerDist p q₀ ≤ hellingerDist q₀ q₁) :
    ∑ a, (p a).toReal * birgeWeight q₀ q₁ a ≤ 1 - hellingerSq q₀ q₁ / 25 := by
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ hellingerDist p q₀ := hellingerDist_nonneg _ _
  have h1 : 0 ≤ hellingerDist q₀ q₁ := hellingerDist_nonneg _ _
  have hsq : 100 * hellingerSq p q₀ ≤ hellingerSq q₀ q₁ := by
    rw [← hellingerDist_sq p q₀, ← hellingerDist_sq q₀ q₁]
    nlinarith
  have hprod : 10 * (hellingerDist p q₀ * hellingerDist q₀ q₁) ≤ hellingerSq q₀ q₁ := by
    rw [← hellingerDist_sq q₀ q₁]
    nlinarith
  have hc1 : 2 * (Real.sqrt 2 - 1) ≤ 1 := by linarith
  have hterm1 : 2 * (Real.sqrt 2 - 1) * hellingerSq p q₀ ≤ hellingerSq q₀ q₁ / 100 :=
    calc 2 * (Real.sqrt 2 - 1) * hellingerSq p q₀
        ≤ 1 * hellingerSq p q₀ := mul_le_mul_of_nonneg_right hc1 (hellingerSq_nonneg _ _)
      _ ≤ hellingerSq q₀ q₁ / 100 := by linarith
  have hmain := sum_mul_birgeWeight_le p q₀ q₁
  linarith

private theorem sum_iid_mul_prod [Fintype α] (p : _root_.PMF α) (f : α → ℝ) (n : ℕ) :
    ∑ x : Fin n → α, (iid p n x).toReal * ∏ i, f (x i) = (∑ a, (p a).toReal * f a) ^ n := by
  have hpt (x : Fin n → α) :
      (iid p n x).toReal * ∏ i, f (x i) = ∏ i, (p (x i)).toReal * f (x i) := by
    rw [iid_eq_pi, pi_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  simp_rw [hpt]
  rw [← Fintype.prod_sum (fun _ a => (p a).toReal * f a), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Markov bound for the product of Birgé weights over `n` i.i.d. draws from `p`. -/
theorem toOuterMeasure_iid_birgeWeight_ge_one_le [Fintype α]
    (p q₀ q₁ : _root_.PMF α) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | 1 ≤ ∏ i, birgeWeight q₀ q₁ (x i)}).toReal ≤
      (∑ a, (p a).toReal * birgeWeight q₀ q₁ a) ^ n := by
  rw [toOuterMeasure_apply_toReal, ← sum_iid_mul_prod p (birgeWeight q₀ q₁) n]
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs with hx
  · exact le_mul_of_one_le_right ENNReal.toReal_nonneg hx
  · exact mul_nonneg ENNReal.toReal_nonneg
      (Finset.prod_nonneg fun _ _ => (birgeWeight_pos _ _ _).le)

private theorem toOuterMeasure_iid_birgeWeight_ge_one_le_exp [Finite α]
    {p q₀ q₁ : _root_.PMF α} (hsep : 10 * hellingerDist p q₀ ≤ hellingerDist q₀ q₁) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | 1 ≤ ∏ i, birgeWeight q₀ q₁ (x i)}).toReal ≤
      Real.exp (-(n : ℝ) * hellingerSq q₀ q₁ / 25) := by
  let := Fintype.ofFinite α
  have hexp_base :
      ∑ a, (p a).toReal * birgeWeight q₀ q₁ a ≤ Real.exp (-hellingerSq q₀ q₁ / 25) :=
    (sum_mul_birgeWeight_le_of_mul hsep).trans <| by
      linarith [Real.add_one_le_exp (-hellingerSq q₀ q₁ / 25)]
  have hsum_nonneg : 0 ≤ ∑ a, (p a).toReal * birgeWeight q₀ q₁ a :=
    Finset.sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (birgeWeight_pos _ _ a).le
  calc ((iid p n).toOuterMeasure {x | 1 ≤ ∏ i, birgeWeight q₀ q₁ (x i)}).toReal
      ≤ (∑ a, (p a).toReal * birgeWeight q₀ q₁ a) ^ n :=
        toOuterMeasure_iid_birgeWeight_ge_one_le p q₀ q₁ n
    _ ≤ Real.exp (-hellingerSq q₀ q₁ / 25) ^ n := pow_le_pow_left₀ hsum_nonneg hexp_base n
    _ = Real.exp (-(n : ℝ) * hellingerSq q₀ q₁ / 25) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

open Classical in
/-- Le Cam–Birgé pairwise Hellinger test: outputs `true` (favoring `q₀`) iff
`∏ i, birgeWeight q₀ q₁ (x i) < 1`, and `false` (favoring `q₁`) otherwise. -/
@[expose] noncomputable def leCamBirgeTest {n : ℕ} (q₀ q₁ : _root_.PMF α)
    (x : Fin n → α) : Bool :=
  decide (∏ i, birgeWeight q₀ q₁ (x i) < 1)

/-- Type-I robustness of `leCamBirgeTest`: if `p` is close to `q₀` relative to the separation
`h(q₀, q₁)` (`10 * h(p, q₀) ≤ h(q₀, q₁)`), then `leCamBirgeTest q₀ q₁` rejects `q₀` with
probability at most `Real.exp (-n * h²(q₀, q₁) / 25)`. -/
theorem leCamBirgeTest_false_le [Finite α] {p q₀ q₁ : _root_.PMF α}
    (hsep : 10 * hellingerDist p q₀ ≤ hellingerDist q₀ q₁) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | leCamBirgeTest q₀ q₁ x = false}).toReal ≤
      Real.exp (-(n : ℝ) * hellingerSq q₀ q₁ / 25) := by
  have hevent :
      {x : Fin n → α | leCamBirgeTest q₀ q₁ x = false} =
        {x : Fin n → α | 1 ≤ ∏ i, birgeWeight q₀ q₁ (x i)} := by
    ext x
    simp only [Set.mem_ofPred_eq, leCamBirgeTest, decide_eq_false_iff_not, not_lt]
  rw [hevent]
  exact toOuterMeasure_iid_birgeWeight_ge_one_le_exp hsep n

/-- Type-II robustness of `leCamBirgeTest`: if `10 * h(p, q₁) ≤ h(q₀, q₁)`, then
`leCamBirgeTest q₀ q₁` accepts `q₀` (`= true`) with probability at most
`Real.exp (-n * h²(q₀, q₁) / 25)`. -/
theorem leCamBirgeTest_true_le [Finite α] {p q₀ q₁ : _root_.PMF α}
    (hsep : 10 * hellingerDist p q₁ ≤ hellingerDist q₀ q₁) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | leCamBirgeTest q₀ q₁ x = true}).toReal ≤
      Real.exp (-(n : ℝ) * hellingerSq q₀ q₁ / 25) := by
  have hsub :
      {x : Fin n → α | leCamBirgeTest q₀ q₁ x = true} ⊆
        {x : Fin n → α | 1 ≤ ∏ i, birgeWeight q₁ q₀ (x i)} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, leCamBirgeTest, decide_eq_true_eq] at hx
    have hpos : 0 < ∏ i, birgeWeight q₀ q₁ (x i) :=
      Finset.prod_pos fun i _ => birgeWeight_pos _ _ _
    have hprod_inv : ∏ i, birgeWeight q₁ q₀ (x i) = (∏ i, birgeWeight q₀ q₁ (x i))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact birgeWeight_symm q₀ q₁ (x i)
    rw [Set.mem_ofPred_eq, hprod_inv]
    exact (one_le_inv₀ hpos).mpr hx.le
  refine (toOuterMeasure_toReal_mono _ hsub).trans ?_
  rw [hellingerSq_comm q₀ q₁]
  exact toOuterMeasure_iid_birgeWeight_ge_one_le_exp
    (by simpa only [hellingerDist_comm q₀ q₁] using hsep) n

private theorem leCamBirgeTest_radius_helper {p q q₀ q₁ : _root_.PMF α} {r : ℝ}
    (hr : 0 ≤ r) (hp : hellingerDist p q ≤ r) (hsep : 10 * r ≤ hellingerDist q₀ q₁) (n : ℕ) :
    10 * hellingerDist p q ≤ hellingerDist q₀ q₁ ∧
      Real.exp (-(n : ℝ) * hellingerSq q₀ q₁ / 25) ≤ Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  refine ⟨by linarith, Real.exp_le_exp.mpr ?_⟩
  have hsq : 100 * r ^ 2 ≤ hellingerSq q₀ q₁ := by
    rw [← hellingerDist_sq]
    exact (show (10 * r) ^ 2 = 100 * r ^ 2 by ring) ▸ sq_le_sq' (by linarith) hsep
  nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

/-- Radius specialization of `leCamBirgeTest_false_le`: if `h(p, q₀) ≤ r` and
`10 * r ≤ h(q₀, q₁)`, the rejection probability is at most `Real.exp (-4 * n * r ^ 2)`. -/
theorem leCamBirgeTest_false_le_of_radius [Finite α] {p q₀ q₁ : _root_.PMF α} {r : ℝ}
    (hr : 0 ≤ r) (hp : hellingerDist p q₀ ≤ r) (hsep : 10 * r ≤ hellingerDist q₀ q₁) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | leCamBirgeTest q₀ q₁ x = false}).toReal ≤
      Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  obtain ⟨hmul, hexp⟩ := leCamBirgeTest_radius_helper hr hp hsep n
  exact (leCamBirgeTest_false_le hmul n).trans hexp

/-- Radius specialization of `leCamBirgeTest_true_le`: if `h(p, q₁) ≤ r` and
`10 * r ≤ h(q₀, q₁)`, the false-acceptance probability is at most `Real.exp (-4 * n * r ^ 2)`. -/
theorem leCamBirgeTest_true_le_of_radius [Finite α] {p q₀ q₁ : _root_.PMF α} {r : ℝ}
    (hr : 0 ≤ r) (hp : hellingerDist p q₁ ≤ r) (hsep : 10 * r ≤ hellingerDist q₀ q₁) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | leCamBirgeTest q₀ q₁ x = true}).toReal ≤
      Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  obtain ⟨hmul, hexp⟩ := leCamBirgeTest_radius_helper hr hp hsep n
  exact (leCamBirgeTest_true_le hmul n).trans hexp

end HellingerTest

section ScheffeTest

section ScheffeBasic

variable [Fintype α]

/-- The Scheffé witness set `{a | q₁ a < q₀ a}` separating two distributions `q₀` and `q₁`. -/
@[expose] noncomputable def scheffeSet (q₀ q₁ : _root_.PMF α) : Finset α :=
  Finset.univ.filter fun a => (q₁ a).toReal < (q₀ a).toReal

/-- A distribution's Scheffé set against itself is empty. -/
theorem scheffeSet_self (q : _root_.PMF α) : scheffeSet q q = ∅ := by
  ext a
  simp [scheffeSet]

/-- Scheffé's identity: the probability gap on `scheffeSet q₀ q₁` equals `dist q₀ q₁`. -/
theorem scheffeSet_sub_eq_dist (q₀ q₁ : _root_.PMF α) :
    (q₀.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal -
        (q₁.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal =
      dist q₀ q₁ := by
  classical
  rw [toOuterMeasure_apply_toReal, toOuterMeasure_apply_toReal, dist_eq_sum_filter_lt]
  simp only [← Finset.sum_sub_distrib, Finset.mem_coe, scheffeSet, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

end ScheffeBasic

/-- Empirical mass assigned to `A : Finset α` by a sample tuple `x : Fin n → α`. -/
@[expose] noncomputable def empiricalMass [DecidableEq α] (A : Finset α) {n : ℕ}
    (x : Fin n → α) : ℝ :=
  (∑ j : Fin n, if x j ∈ A then (1 : ℝ) else 0) / n

private theorem empiricalMass_hoeffding_prep [DecidableEq α] (p : _root_.PMF α)
    (A : Finset α) (n : ℕ) :
    ∀ (_ : Fin n) (a : α), a ∈ p.support → (if a ∈ A then (1 : ℝ) else 0) ∈ Set.Icc 0 1 := by
  intro _ a _
  split_ifs <;> constructor <;> norm_num

private theorem sum_indicator_mean [Fintype α] [DecidableEq α] (p : _root_.PMF α) (A : Finset α)
    (n : ℕ) :
    ∑ _i : Fin n, ∑ a : α, (p a).toReal * (if a ∈ A then (1 : ℝ) else 0) =
      n * (p.toOuterMeasure (A : Set α)).toReal := by
  classical
  rw [toOuterMeasure_apply_toReal, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

section ScheffeHoeffding

variable [Finite α] [DecidableEq α]

omit [Finite α] [DecidableEq α] in
private theorem toOuterMeasure_empiricalMass_tail_le (p : _root_.PMF α) (n : ℕ) (γ : ℝ)
    (P S : (Fin n → α) → Prop)
    (hiff : 0 < n → ∀ x : Fin n → α, P x ↔ S x)
    (hpi : ((iid p n).toOuterMeasure {x | S x}).toReal ≤ Real.exp (-2 * (n : ℝ) * γ ^ 2)) :
    ((iid p n).toOuterMeasure {x | P x}).toReal ≤ Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (toOuterMeasure_toReal_le_one _ _).trans_eq ?_
    simp
  have hevent : {x : Fin n → α | P x} = {x : Fin n → α | S x} := by
    ext x
    exact hiff hn x
  rwa [hevent]

/-- Lower-tail Hoeffding concentration for `empiricalMass A x`. -/
theorem toOuterMeasure_empiricalMass_le_sub_le (p : _root_.PMF α) (A : Finset α) (n : ℕ)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    ((iid p n).toOuterMeasure
      {x | empiricalMass A x ≤ (p.toOuterMeasure (A : Set α)).toReal - γ}).toReal ≤
        Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  let := Fintype.ofFinite α
  refine toOuterMeasure_empiricalMass_tail_le p n γ _
    (fun x => ∑ i : Fin n, (if x i ∈ A then (1 : ℝ) else 0) ≤
      n * (p.toOuterMeasure (A : Set α)).toReal - n * γ)
    (fun hn x => by
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      simp only [empiricalMass, div_le_iff₀ hnR]
      constructor <;> intro hx <;> linarith) ?_
  have h := pi_sum_le_mean_sub_card_mul (fun _ : Fin n => p)
    (fun _ a => if a ∈ A then (1 : ℝ) else 0) (empiricalMass_hoeffding_prep p A n) hγ
  rwa [Fintype.card_fin, sum_indicator_mean, ← iid_eq_pi] at h

/-- Upper-tail Hoeffding concentration for `empiricalMass A x`. -/
theorem toOuterMeasure_add_le_empiricalMass_le (p : _root_.PMF α) (A : Finset α) (n : ℕ)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    ((iid p n).toOuterMeasure
      {x | (p.toOuterMeasure (A : Set α)).toReal + γ ≤ empiricalMass A x}).toReal ≤
        Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  let := Fintype.ofFinite α
  refine toOuterMeasure_empiricalMass_tail_le p n γ _
    (fun x => n * (p.toOuterMeasure (A : Set α)).toReal + n * γ ≤
      ∑ i : Fin n, (if x i ∈ A then (1 : ℝ) else 0))
    (fun hn x => by
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      simp only [empiricalMass, le_div_iff₀ hnR]
      constructor <;> intro hx <;> linarith) ?_
  have h := pi_sum_ge_mean_add_card_mul (fun _ : Fin n => p)
    (fun _ a => if a ∈ A then (1 : ℝ) else 0) (empiricalMass_hoeffding_prep p A n) hγ
  rwa [Fintype.card_fin, sum_indicator_mean, ← iid_eq_pi] at h

/-- Two-sided Hoeffding concentration for `empiricalMass A x`:
`P^{\otimes n}(γ ≤ |empiricalMass A x - p(A)|) ≤ 2 * Real.exp (-2 * n * γ ^ 2)`. -/
theorem abs_empiricalMass_sub_ge_le (p : _root_.PMF α) (A : Finset α) (n : ℕ)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    ((iid p n).toOuterMeasure
      {x | γ ≤ |empiricalMass A x - (p.toOuterMeasure (A : Set α)).toReal|}).toReal ≤
        2 * Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  refine (toOuterMeasure_abs_sub_ge_toReal_le (iid p n) (empiricalMass A)
    (p.toOuterMeasure (A : Set α)).toReal γ).trans ?_
  linarith [toOuterMeasure_add_le_empiricalMass_le p A n hγ,
    toOuterMeasure_empiricalMass_le_sub_le p A n hγ]

end ScheffeHoeffding

section ScheffePairwise

variable [Fintype α] [DecidableEq α]

open Classical in
/-- Pairwise Scheffé TV test between `q₀` and `q₁`: outputs `true` (favoring `q₀`) iff the
empirical frequency of `scheffeSet q₀ q₁` is at least `(q₀(A) + q₁(A)) / 2`. -/
@[expose] noncomputable def scheffeTest (q₀ q₁ : _root_.PMF α) {n : ℕ}
    (x : Fin n → α) : Bool :=
  let A := scheffeSet q₀ q₁
  decide
    (((q₀.toOuterMeasure (A : Set α)).toReal + (q₁.toOuterMeasure (A : Set α)).toReal) / 2 ≤
      empiricalMass A x)

omit [DecidableEq α] in
private theorem scheffeTest_mid_sub_le {p q₀ q₁ : _root_.PMF α} {γ : ℝ}
    (hsep : dist p q₀ + γ ≤ dist q₀ q₁ / 2) :
    ((q₀.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal +
        (q₁.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal) / 2 ≤
      (p.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal - γ := by
  have hgap := scheffeSet_sub_eq_dist q₀ q₁
  have hp0 := (abs_le.mp (abs_toOuterMeasure_toReal_sub_le_dist p q₀
    (scheffeSet q₀ q₁ : Set α))).1
  linarith

omit [DecidableEq α] in
private theorem le_scheffeTest_mid {p q₀ q₁ : _root_.PMF α} {γ : ℝ}
    (hsep : dist p q₁ + γ ≤ dist q₀ q₁ / 2) :
    (p.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal + γ ≤
      ((q₀.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal +
        (q₁.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal) / 2 := by
  have hgap := scheffeSet_sub_eq_dist q₀ q₁
  have hp1 := (abs_le.mp (abs_toOuterMeasure_toReal_sub_le_dist p q₁
    (scheffeSet q₀ q₁ : Set α))).2
  linarith

/-- Robust Type-I bound for `scheffeTest`: under any `p` with `dist p q₀ + γ ≤ dist q₀ q₁ / 2`,
the probability of outputting `false` is at most `Real.exp (-2 * n * γ ^ 2)`. -/
theorem scheffeTest_false_le {p q₀ q₁ : _root_.PMF α} {γ : ℝ} (hγ : 0 ≤ γ)
    (hsep : dist p q₀ + γ ≤ dist q₀ q₁ / 2) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | scheffeTest q₀ q₁ x = false}).toReal ≤
      Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  refine (toOuterMeasure_toReal_mono _ fun x hx => ?_).trans
    (toOuterMeasure_empiricalMass_le_sub_le p (scheffeSet q₀ q₁) n hγ)
  simp only [Set.mem_ofPred_eq, scheffeTest, decide_eq_false_iff_not, not_le] at hx
  exact hx.le.trans (scheffeTest_mid_sub_le hsep)

/-- Robust Type-II bound for `scheffeTest`: under any `p` with `dist p q₁ + γ ≤ dist q₀ q₁ / 2`,
the probability of outputting `true` is at most `Real.exp (-2 * n * γ ^ 2)`. -/
theorem scheffeTest_true_le {p q₀ q₁ : _root_.PMF α} {γ : ℝ} (hγ : 0 ≤ γ)
    (hsep : dist p q₁ + γ ≤ dist q₀ q₁ / 2) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | scheffeTest q₀ q₁ x = true}).toReal ≤
      Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  refine (toOuterMeasure_toReal_mono _ fun x hx => ?_).trans
    (toOuterMeasure_add_le_empiricalMass_le p (scheffeSet q₀ q₁) n hγ)
  simp only [Set.mem_ofPred_eq, scheffeTest, decide_eq_true_eq] at hx
  exact (le_scheffeTest_mid hsep).trans hx

end ScheffePairwise

end ScheffeTest

end Cslib.Probability.HypothesisSelection
