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

/-- The exact compatible capacity retains its `K + 1` gain. The floor costs ten
binary exponents while capacity supplies sixty-four, before taking the fourth root. -/
theorem compatible_rarity_decay {η : ℝ} (hη : 0 < η) (K m j : ℕ) :
    (((2 + 256 / dyadicFloor η m j) / (compatibleCapacity K m j : ℝ)) ^
      (4⁻¹ : ℝ)) ≤ ((2 + 256 / η) / (K + 1)) ^ (4⁻¹ : ℝ) *
        (2 : ℝ) ^ (-(27 : ℝ) * dyadicSlack m j / 2) := by
  let d := dyadicSlack m j
  have hpow : (1 : ℝ) ≤ 1024 ^ d := one_le_pow₀ (by norm_num)
  have hnum : 2 + 256 / dyadicFloor η m j ≤ (2 + 256 / η) * 1024 ^ d := by
    change 2 + 256 / (η * (1 / 1024) ^ d) ≤ _
    rw [one_div_pow]
    have hid : 256 / (η * (1 / (1024 : ℝ) ^ d)) = (256 / η) * 1024 ^ d := by
      field_simp
    rw [hid]
    nlinarith
  have hden : 0 < ((K : ℝ) + 1) * (2 : ℝ) ^ (64 * d) := by positivity
  have he : (1024 : ℝ) ^ d / (2 : ℝ) ^ (64 * d) =
      (2 : ℝ) ^ (-(54 : ℝ) * d) := by
    rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, ← pow_mul,
      ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring_nf
  have hq : (2 + 256 / dyadicFloor η m j) / (compatibleCapacity K m j : ℝ) ≤
      ((2 + 256 / η) / (K + 1)) * (2 : ℝ) ^ (-(54 : ℝ) * d) := by
    rw [compatibleCapacity, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat]
    change (2 + 256 / dyadicFloor η m j) / (((K : ℝ) + 1) * 2 ^ (64 * d)) ≤ _
    apply (div_le_div_of_nonneg_right hnum hden.le).trans_eq
    rw [← he]
    field_simp
  have hf := dyadicFloor_pos hη m j
  have hr := Real.rpow_le_rpow (by positivity :
    0 ≤ (2 + 256 / dyadicFloor η m j) / (compatibleCapacity K m j : ℝ)) hq
    (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hr
  convert hr using 1
  congr 1
  dsimp only [d]
  ring_nf

/-- Slope-one deterministic prefix costs have a summable literal tail, even when early
slacks grow. The comparison uses `d_i ≤ d_j` inside each first-overflow tail. -/
theorem compatible_growing_mean_tail_le {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E)
    (K m : ℕ) (e : ℕ → ℝ)
    (he : ∀ i < m, e i ≤ E * (2 : ℝ) ^ dyadicSlack m i) :
    (∑ j ∈ range m,
      (((2 + 256 / dyadicFloor η m j) / (compatibleCapacity K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * e i) ≤
      (2 + 256 / η) ^ (4⁻¹ : ℝ) * E / 63 := by
  have hs := sum_propagation_mul_dyadic_decay_le (C := 1) (q := (1 / 64 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) m
  norm_num only [one_pow, one_mul] at hs
  calc
    _ ≤ ∑ j ∈ range m, E * ((2 + 256 / η) ^ (4⁻¹ : ℝ) *
        (1 / 64 : ℝ) ^ dyadicSlack m j) := by
      apply sum_le_sum
      intro j hj
      have hf := dyadicFloor_pos hη m j
      have hg := mean_tail_growth hE m j (mem_range.mp hj) e (fun i _ hi => he i hi)
      have hr := mul_le_mul_of_nonneg_left (compatible_rarity_growth hη K m j) hE
      apply (mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (by positivity) _)).trans
      nlinarith only [hr]
    _ = ((2 + 256 / η) ^ (4⁻¹ : ℝ) * E) *
        ∑ j ∈ range m, (1 / 64 : ℝ) ^ dyadicSlack m j := by
      simp only [mul_sum]
      apply sum_congr rfl
      intros
      ring_nf
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hs (by positivity :
        0 ≤ (2 + 256 / η) ^ (4⁻¹ : ℝ) * E)
      convert hh using 1
      ring_nf

/-- Stationary means with slope-one endpoint growth have no horizon loss. The
literal floor is retained; the resulting dyadic ratio is exactly `1 / 512`. -/
theorem compatible_growing_mean_pre_le {η E : ℝ} (hη : 0 ≤ η) (hE : 0 ≤ E)
    (m : ℕ) (e : ℕ → ℝ)
    (he : ∀ i < m, e i ≤ E * (2 : ℝ) ^ dyadicSlack m i) :
    (∑ i ∈ range m, dyadicFloor η m i * e i) ≤ η * E / 511 := by
  apply le_trans _ (pre_schedule_sum hη hE m)
  exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
    (he i (mem_range.mp hi)) (dyadicFloor_nonneg hη m i)

/-- Exact false-event coefficient, before charging its actual postincrement prefix.
The capacity gain `K + 1` and the floor's fourth power remain visible. -/
theorem compatible_false_weight_eq (η : ℝ) (K m j : ℕ) (R : ℝ) :
    64 * (K : ℝ) * R ^ 4 /
      ((compatibleCapacity K m j : ℝ) * dyadicFloor η m j ^ 4) =
      (64 * (K : ℝ) * R ^ 4 / ((K + 1) * η ^ 4)) *
        (1 / 16777216 : ℝ) ^ dyadicSlack m j := by
  let d := dyadicSlack m j
  have hp : (2 : ℝ) ^ (64 * d) = ((2 : ℝ) ^ 64) ^ d := by rw [pow_mul]
  change _ = _ * (1 / 16777216 : ℝ) ^ d
  rw [compatibleCapacity, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
    Nat.cast_ofNat]
  change 64 * (K : ℝ) * R ^ 4 /
    ((((K : ℝ) + 1) * 2 ^ (64 * d)) * (η * (1 / 1024) ^ d) ^ 4) = _
  have hfour : (((1 / 1024 : ℝ) ^ d) ^ 4) = ((1 / 1024 : ℝ) ^ 4) ^ d := by
    rw [← pow_mul, Nat.mul_comm d 4, pow_mul]
  rw [mul_pow, hp, hfour,
    show (1 / 16777216 : ℝ) = ((2 : ℝ) ^ 64 * (1 / 1024) ^ 4)⁻¹ by norm_num,
    inv_pow, mul_pow]
  field_simp

/-- Fourth-moment endpoint growth is absorbed by the actual raw false-event weight.
This statement uses `e j` for the prefix `j + 1`, exactly as the literal decoder does. -/
theorem compatible_growing_mean_raw_le {η E : ℝ} (hη : 0 < η)
    (K m : ℕ) (R : ℝ) (e : ℕ → ℝ)
    (he : ∀ i < m, 0 ≤ e i ∧ e i ≤ E * (2 : ℝ) ^ dyadicSlack m i) :
    (∑ i ∈ range m, (64 * (K : ℝ) * R ^ 4 /
      ((compatibleCapacity K m i : ℝ) * dyadicFloor η m i ^ 4)) * e i ^ 4) ≤
      (64 * (K : ℝ) * R ^ 4 / ((K + 1) * η ^ 4)) * E ^ 4 / 63 := by
  have hs := false_schedule_sum (K := (K : ℝ) / (K + 1)) (ε := E) (R := R)
    hη (by positivity) m
  have hs' : _ ≤ (64 * (K : ℝ) * R ^ 4 / ((K + 1) * η ^ 4)) * E ^ 4 / 63 :=
    hs.trans_eq (by field_simp)
  apply le_trans _ hs'
  apply sum_le_sum
  intro i hi
  have hf := dyadicFloor_pos hη m i
  have hb := (he i (mem_range.mp hi))
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.1 hb.2 4) (by positivity)).trans_eq
  rw [compatibleCapacity, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
    Nat.cast_ofNat]
  field_simp

/-- Unconditional centered-noise allocations use the actual floor, capacity and
postincrement weights. Factor-28 tail propagation is paid without a rarity factor;
all prefixes and events may be correlated. The envelope constant precedes the horizon. -/
theorem compatible_sixteenth_noise_schedule {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E)
    (K m : ℕ) (R : ℝ) (e : ℕ → ℝ)
    (he : ∀ i < m, 0 ≤ e i ∧ e i ≤ E * (1 / 16 : ℝ) ^ dyadicSlack m i) :
    (∑ i ∈ range m, dyadicFloor η m i * e i) ≤ η * E / 511 ∧
    (∀ i < m, e i ≤ E / 16) ∧
    (∑ i ∈ range m, (28 : ℝ) ^ (m - i) * e i) ≤ E * (1792 / 57) ∧
    (∑ i ∈ range m, (64 * (K : ℝ) * R ^ 4 /
      ((compatibleCapacity K m i : ℝ) * dyadicFloor η m i ^ 4)) * e i ^ 4) ≤
        (64 * (K : ℝ) * R ^ 4 / ((K + 1) * η ^ 4)) * E ^ 4 / 63 := by
  have hg (i : ℕ) (hi : i < m) : e i ≤ E * (2 : ℝ) ^ dyadicSlack m i :=
    (he i hi).2.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 16 : ℝ) ≤ 2) _) hE)
  refine ⟨compatible_growing_mean_pre_le hη.le hE m e hg, ?_, ?_,
    compatible_growing_mean_raw_le hη K m R e (fun i hi => ⟨(he i hi).1, hg i hi⟩)⟩
  · intro i hi
    have hd : 1 ≤ dyadicSlack m i := Nat.one_le_pow _ _ (by decide)
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (1 / 16 : ℝ) ≤ 1) hd
    simpa only [pow_one, mul_one_div] using
      (he i hi).2.trans (mul_le_mul_of_nonneg_left hp hE)
  · apply le_trans (sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
      (he i (mem_range.mp hi)).2 (by positivity : (0 : ℝ) ≤ 28 ^ (m - i)))
    calc
      _ = E * ∑ i ∈ range m, (28 : ℝ) ^ (m - i) *
          (1 / 16 : ℝ) ^ dyadicSlack m i := by
        simp only [mul_sum]
        apply sum_congr rfl
        intros
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_propagation_mul_sixteenth_le m) hE

/-- Unconditional centered-noise allocations use the actual floor, capacity and
postincrement weights. Factor-28 tail propagation is paid without a rarity factor;
all prefixes and events may be correlated. The envelope constant precedes the horizon. -/
theorem compatible_quarter_noise_schedule {η E : ℝ} (hη : 0 < η) (hE : 0 ≤ E)
    (K m : ℕ) (R : ℝ) (e : ℕ → ℝ)
    (he : ∀ i < m, 0 ≤ e i ∧ e i ≤ E * (1 / 4 : ℝ) ^ dyadicSlack m i) :
    (∑ i ∈ range m, dyadicFloor η m i * e i) ≤ η * E / 511 ∧
    (∀ i < m, e i ≤ E / 4) ∧
    (∑ i ∈ range m, (28 : ℝ) ^ (m - i) * e i) ≤ E * (458752 / 57) ∧
    (∑ i ∈ range m, (64 * (K : ℝ) * R ^ 4 /
      ((compatibleCapacity K m i : ℝ) * dyadicFloor η m i ^ 4)) * e i ^ 4) ≤
        (64 * (K : ℝ) * R ^ 4 / ((K + 1) * η ^ 4)) * E ^ 4 / 63 := by
  have hg (i : ℕ) (hi : i < m) : e i ≤ E * (2 : ℝ) ^ dyadicSlack m i :=
    (he i hi).2.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 4 : ℝ) ≤ 2) _) hE)
  refine ⟨compatible_growing_mean_pre_le hη.le hE m e hg, ?_, ?_,
    compatible_growing_mean_raw_le hη K m R e (fun i hi => ⟨(he i hi).1, hg i hi⟩)⟩
  · intro i hi
    have hd : 1 ≤ dyadicSlack m i := Nat.one_le_pow _ _ (by decide)
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) hd
    simpa only [pow_one, mul_one_div] using
      (he i hi).2.trans (mul_le_mul_of_nonneg_left hp hE)
  · apply le_trans (sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
      (he i (mem_range.mp hi)).2 (by positivity : (0 : ℝ) ≤ 28 ^ (m - i)))
    calc
      _ = E * ∑ i ∈ range m, (28 : ℝ) ^ (m - i) *
          (1 / 4 : ℝ) ^ dyadicSlack m i := by
        simp only [mul_sum]
        apply sum_congr rfl
        intros
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_propagation_mul_quarter_le m) hE

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

/-- The literal false-charge weight retains exponential decay at the first group.
This estimate pays the inverse fourth power of the floor, before multiplying any moment. -/
theorem compatible_false_weight_decay {η : ℝ} (hη : 0 < η) (K m j : ℕ) (R : ℝ) :
    64 * (K : ℝ) * R ^ 4 /
      ((compatibleCapacity K m j : ℝ) * dyadicFloor η m j ^ 4) ≤
      (64 * (K : ℝ) * R ^ 4 / η ^ 4) *
        (1 / 1048576 : ℝ) ^ dyadicSlack m j := by
  let d := dyadicSlack m j
  have hn : (0 : ℝ) ≤ 64 * K * R ^ 4 := by positivity
  have hc : (2 : ℝ) ^ (64 * d) ≤ (compatibleCapacity K m j : ℝ) := by
    exact_mod_cast (compatibleCapacity_bounds K m j).2
  have hf := dyadicFloor_pos hη m j
  have he := false_schedule_identity (ε := 1) η d
  simp only [one_mul, one_pow] at he
  calc
    _ ≤ (64 * (K : ℝ) * R ^ 4) /
        ((2 : ℝ) ^ (64 * d) * dyadicFloor η m j ^ 4) := by
      apply div_le_div_of_nonneg_left hn (by positivity)
      exact mul_le_mul_of_nonneg_right hc (pow_nonneg hf.le 4)
    _ ≤ (64 * (K : ℝ) * R ^ 4) *
        ((2 ^ d) ^ 4 / ((2 : ℝ) ^ (64 * d) * dyadicFloor η m j ^ 4)) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact le_mul_of_one_le_right hn (one_le_pow₀ (one_le_pow₀ (by norm_num)))
    _ = _ := by
      change (64 * (K : ℝ) * R ^ 4) *
        ((2 ^ d) ^ 4 / ((2 : ℝ) ^ (64 * d) * (η * (1 / 1024) ^ d) ^ 4)) = _
      rw [he]
      ring

/-- Two width factors are paid even for the exceptional false-charge weight, provided
its first slack dominates the retained depth. The early moment still needs its own bound. -/
theorem compatible_first_false_width {η : ℝ} (hη : 0 < η) (K m P n : ℕ) (R : ℝ)
    (hP : P ≤ 2 ^ (n + 1)) (hn : n ≤ dyadicSlack m 0) :
    (64 * (K : ℝ) * R ^ 4 /
      ((compatibleCapacity K m 0 : ℝ) * dyadicFloor η m 0 ^ 4)) * (P : ℝ) ^ 2 ≤
      (64 * (K : ℝ) * R ^ 4 / η ^ 4) * 4 * (1 / 262144 : ℝ) ^ n := by
  have hc : 0 ≤ 64 * (K : ℝ) * R ^ 4 / η ^ 4 := by positivity
  have hd : (1 / 1048576 : ℝ) ^ dyadicSlack m 0 ≤ (1 / 1048576 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hp : (P : ℝ) ^ 2 ≤ 4 * (4 : ℝ) ^ n := by
    have hh : (P : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast hP
    apply (pow_le_pow_left₀ (Nat.cast_nonneg P) hh 2).trans_eq
    rw [← pow_mul, Nat.add_mul, Nat.one_mul, pow_add, Nat.mul_comm n 2, pow_mul]
    norm_num
    ring
  calc
    _ ≤ ((64 * (K : ℝ) * R ^ 4 / η ^ 4) *
        (1 / 1048576 : ℝ) ^ n) * (4 * (4 : ℝ) ^ n) := by
      exact mul_le_mul ((compatible_false_weight_decay hη K m 0 R).trans
        (mul_le_mul_of_nonneg_left hd hc)) hp (by positivity) (by positivity)
    _ = _ := by rw [mul_mul_mul_comm, ← mul_pow]; norm_num

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
