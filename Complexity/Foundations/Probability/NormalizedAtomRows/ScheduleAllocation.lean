/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.ActualMoment
public import Complexity.Foundations.Analysis.RowCompression.MomentSchedule

/-!
# Geometric allocation with an exceptional first group

These original numerical bounds use the actual compatible capacity and floor schedules.
A constant positive-prefix envelope receives a horizon-independent payment. An exceptional
first prefix retains its own exact coefficient. No centered-noise rarity is asserted.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib.RowCompression
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The literal rarity root times the tail-growth envelope has summable dyadic decay.
Dropping the factor K+1 only enlarges this numerical upper bound. -/
theorem compatible_rarity_growth {η : ℝ} (hη : 0 < η) (K m j : ℕ) :
    (((2 + 256 / dyadicFloor η m j) / (compatibleCapacity K m j : ℝ)) ^
      (4⁻¹ : ℝ)) * 128 ^ dyadicSlack m j ≤
      (2 + 256 / η) ^ (4⁻¹ : ℝ) * (1 / 64 : ℝ) ^ dyadicSlack m j := by
  let d := dyadicSlack m j
  have hf := dyadicFloor_pos hη m j
  have hcap : (2 : ℝ) ^ (64 * d) ≤ (compatibleCapacity K m j : ℝ) := by
    exact_mod_cast (compatibleCapacity_bounds K m j).2
  have hq : 0 ≤ (2 + 256 / dyadicFloor η m j) / (compatibleCapacity K m j : ℝ) := by
    positivity
  have hb := mean_schedule_budget (ε := 1) hη (by norm_num : (0 : ℝ) ≤ 1) m j
  simp only [mul_one, one_mul, one_pow] at hb
  have ht := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 + 256 / dyadicFloor η m j)
      (by positivity : (0 : ℝ) < 2 ^ (64 * d)) hcap)
    (by positivity : (0 : ℝ) ≤ (128 ^ d) ^ 4)
  have hr := Real.rpow_le_rpow (mul_nonneg hq (by positivity)) (ht.trans hb)
    (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have hroot (x : ℝ) (hx : 0 ≤ x) : (x ^ 4) ^ (4⁻¹ : ℝ) = x := by
    convert Real.pow_rpow_inv_natCast hx (by decide : (4 : ℕ) ≠ 0) using 1
  rw [Real.mul_rpow hq (by positivity), hroot _ (by positivity),
    Real.mul_rpow (by positivity) (by positivity), hroot _ (by positivity)] at hr
  exact hr

/-- The exceptional first rarity weight decays in the actual first dyadic slack,
even after all factor-28 propagation. -/
theorem compatible_first_rarity_decay {η : ℝ} (hη : 0 < η) (K m : ℕ) (hm : 0 < m) :
    (((2 + 256 / dyadicFloor η m 0) / (compatibleCapacity K m 0 : ℝ)) ^
      (4⁻¹ : ℝ)) * 28 ^ m ≤
      (2 + 256 / η) ^ (4⁻¹ : ℝ) * (1 / 64 : ℝ) ^ dyadicSlack m 0 := by
  have hrem : m ≤ dyadicSlack m 0 := by
    have he : m = m - 1 + 1 := by omega
    conv_lhs => rw [he]
    exact Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hg : (28 : ℝ) ^ m ≤ 128 ^ dyadicSlack m 0 :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 128) hrem)
  apply le_trans (mul_le_mul_of_nonneg_left hg ?_) (compatible_rarity_growth hη K m 0)
  exact Real.rpow_nonneg (by
    have hf := (dyadicFloor_pos hη m 0).le
    positivity) _

/-- A deterministic tail with a single exceptional first prefix. The positive-prefix
constant has no group-count factor; the first prefix keeps its actual rarity weight. -/
theorem compatible_mean_tail_le {η a b : ℝ} (hη : 0 < η) (ha : 0 ≤ a)
    (K m : ℕ) (hm : 0 < m) (e : ℕ → ℝ)
    (he : ∀ i < m, e i ≤ a + if i = 0 then b else 0) :
    (∑ j ∈ range m,
      (((2 + 256 / dyadicFloor η m j) / (compatibleCapacity K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * e i) ≤
      (2 + 256 / η) ^ (4⁻¹ : ℝ) * a / 63 +
      (((2 + 256 / dyadicFloor η m 0) / (compatibleCapacity K m 0 : ℝ)) ^
        (4⁻¹ : ℝ)) * 28 ^ m * b := by
  let v := fun j => ((2 + 256 / dyadicFloor η m j) /
    (compatibleCapacity K m j : ℝ)) ^ (4⁻¹ : ℝ)
  have hv (j : ℕ) : 0 ≤ v j := Real.rpow_nonneg (by
    have hf := dyadicFloor_pos hη m j
    positivity) _
  have hs := sum_propagation_mul_dyadic_decay_le (C := 1) (q := (1 / 64 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) m
  norm_num only [one_pow, one_mul] at hs
  have hs' : (∑ j ∈ range m, v j * (a * 128 ^ dyadicSlack m j)) ≤
      (2 + 256 / η) ^ (4⁻¹ : ℝ) * a / 63 := by
    calc
      _ ≤ ∑ j ∈ range m, a * ((2 + 256 / η) ^ (4⁻¹ : ℝ) *
          (1 / 64 : ℝ) ^ dyadicSlack m j) := by
        apply sum_le_sum
        intro j _
        have ht := mul_le_mul_of_nonneg_left (compatible_rarity_growth hη K m j) ha
        dsimp only [v]
        nlinarith [ht]
      _ = a * (2 + 256 / η) ^ (4⁻¹ : ℝ) *
          ∑ j ∈ range m, (1 / 64 : ℝ) ^ dyadicSlack m j := by
        simp only [mul_assoc, mul_sum]
      _ ≤ a * (2 + 256 / η) ^ (4⁻¹ : ℝ) * (1 / 63) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        convert hs using 1
      _ = _ := by ring
  calc
    _ ≤ ∑ j ∈ range m, v j * ∑ i ∈ Ico j m,
        (28 : ℝ) ^ (m - i) * (a + if i = 0 then b else 0) := by
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hv j)
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (he i (mem_Ico.mp hi).2) (by positivity)
    _ = (∑ j ∈ range m, v j * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a) +
        v 0 * 28 ^ m * b := by
      simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_Ico,
        Nat.le_zero, hm, and_true, Nat.sub_zero, mem_range, ↓reduceIte]
      ring
    _ ≤ _ := by
      change _ ≤ (2 + 256 / η) ^ (4⁻¹ : ℝ) * a / 63 + v 0 * 28 ^ m * b
      apply add_le_add _ le_rfl
      apply le_trans _ hs'
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (hv j)
      exact mean_tail_growth ha m j (mem_range.mp hj) (fun _ => a)
        (fun i _ _ => le_mul_of_one_le_right ha
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))

/-- False-charge sums with a constant later moment and one exceptional first moment.
The first contribution is exact; it is not spread over all groups. -/
theorem compatible_false_charge_le {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a)
    (K m : ℕ) {R : ℝ} (b : ℝ) (hm : 0 < m) (e : ℕ → ℝ)
    (he : ∀ i < m, e i ≤ a + if i = 0 then b else 0) :
    (∑ i ∈ range m, (64 * K * R ^ 4 /
      ((compatibleCapacity K m i : ℝ) * dyadicFloor η m i ^ 4)) * e i) ≤
      (64 * K * R ^ 4 / η ^ 4) * a / 63 +
      (64 * K * R ^ 4 / ((compatibleCapacity K m 0 : ℝ) *
        dyadicFloor η m 0 ^ 4)) * b := by
  let w := fun i => 64 * (K : ℝ) * R ^ 4 /
    ((compatibleCapacity K m i : ℝ) * dyadicFloor η m i ^ 4)
  have hw (i : ℕ) : 0 ≤ w i := by dsimp only [w]; positivity
  have hs := false_schedule_sum_capacity (ε := 1) (R := R) (K := (K : ℝ)) hη
    (Nat.cast_nonneg K) m (compatibleCapacity K m)
    (fun i _ => (compatibleCapacity_bounds K m i).2)
  simp only [one_mul, one_pow, mul_one] at hs
  have hs' : (∑ i ∈ range m, w i) ≤ 64 * (K : ℝ) * R ^ 4 / η ^ 4 / 63 := by
    apply le_trans _ hs
    apply sum_le_sum
    intro i _
    exact le_mul_of_one_le_right (hw i)
      (one_le_pow₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  calc
    _ ≤ ∑ i ∈ range m, w i * (a + if i = 0 then b else 0) := by
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (he i (mem_range.mp hi)) (hw i)
    _ = a * (∑ i ∈ range m, w i) + w 0 * b := by
      simp only [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_range,
        hm, ↓reduceIte, ← sum_mul]
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs' ha]

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
