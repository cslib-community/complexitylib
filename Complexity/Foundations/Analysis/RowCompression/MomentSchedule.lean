/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.NoiseDecay

/-!
# Dyadic mean, preloss and false-event moment payments

The floor has base 1/1024 and capacities dominate 2^(64*dyadicSlack). These elementary
finite-sum estimates absorb factor-28 propagation and growing mean envelopes without a
row-width or horizon factor. The capacity comparison bounds numerical denominators only;
it supplies no monotonicity of compression outputs or events.
-/

public section
open Finset
open scoped BigOperators

namespace Cslib.RowCompression
open Finset
open scoped BigOperators

open Classical in
/-- Capacity exponent 64 absorbs the inverse floor and fourth powers of mean growth
with slope seven, leaving at least fourth powers of 1/64 decay. -/
lemma mean_schedule_term {η M ε : ℝ} (hη : 0 < η) (hM : 0 ≤ M) (d : ℕ) :
    ((2 + 256 * M / (η * (1 / 1024) ^ d)) / (2 : ℝ) ^ (64 * d)) * (ε * 128 ^ d) ^ 4 ≤
      (2 + 256 * M / η) * ε ^ 4 * ((1 / 64 : ℝ) ^ d) ^ 4 := by
  have hid : ((2 + 256 * M / (η * (1 / 1024) ^ d)) / (2 : ℝ) ^ (64 * d)) * (ε * 128 ^ d) ^ 4 =
      ε ^ 4 * (2 * ((1 / 68719476736 : ℝ) ^ d) + (256 * M / η) * (1 / 67108864 : ℝ) ^ d) := by
    rw [mul_pow, show (2 : ℝ) ^ (64 * d) = ((2 : ℝ) ^ 64) ^ d by rw [pow_mul],
      show ((128 : ℝ) ^ d) ^ 4 = ((128 : ℝ) ^ 4) ^ d by rw [←pow_mul, Nat.mul_comm, pow_mul]]
    norm_num only [show (2 : ℝ) ^ 64 = 18446744073709551616 by norm_num,
      show (128 : ℝ) ^ 4 = 268435456 by norm_num]
    simp only [div_pow, one_pow]
    field_simp
    calc
      _ = η * ε ^ 4 * (67108864 : ℝ) ^ d * ((268435456 : ℝ) ^ d * (68719476736 : ℝ) ^ d) * 2 +
          M * ε ^ 4 * (68719476736 : ℝ) ^ d * ((1024 : ℝ) ^ d * (67108864 : ℝ) ^ d * (268435456 :
            ℝ) ^ d)
 * 256 := by ring
      _ = _ := by norm_num [←mul_pow]; ring
  rw [hid]
  have h1 : (1 / 68719476736 : ℝ) ^ d ≤ (1 / 16777216 : ℝ) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h2 : (1 / 67108864 : ℝ) ^ d ≤ (1 / 16777216 : ℝ) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left h2 (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) hM) hη.le))
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ ε ^ 4 by positivity)
  have he : ((1 / 64 : ℝ) ^ d) ^ 4 = (1 / 16777216 : ℝ) ^ d := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [he]
  nlinarith [hh]
open Classical in
/-- A slope-one prefix mean envelope pays for the actual factor-28 tail propagation.
This deliberately coarse estimate has no horizon or row-width factor. -/
lemma mean_tail_growth {ε : ℝ} (hε : 0 ≤ ε) (m j : ℕ) (hj : j < m)
    (e : ℕ → ℝ) (he : ∀ i, j ≤ i → i < m → e i ≤ ε * 2 ^ dyadicSlack m i) :
    ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * e i ≤ ε * 128 ^ dyadicSlack m j := by
  let d := dyadicSlack m j
  have hrem : m - j ≤ d := by
    have hcount : m - j = m - (j + 1) + 1 := by omega
    rw [hcount]
    exact Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hd : (m - j : ℕ) ≤ 2 ^ d := hrem.trans (Nat.le_of_lt Nat.lt_two_pow_self)
  have ht (i : ℕ) (hi : i ∈ Ico j m) : (28 : ℝ) ^ (m - i) * e i ≤ ε * 64 ^ d := by
    have hji := (mem_Ico.mp hi).1
    have him := (mem_Ico.mp hi).2
    have hdi : dyadicSlack m i ≤ d := by
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      omega
    have hr : (28 : ℝ) ^ (m - i) ≤ 32 ^ d :=
      (pow_le_pow_left₀ (by norm_num) (by norm_num) _).trans
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 32) (by omega : m - i ≤ d))
    have hm := mul_le_mul_of_nonneg_left (he i hji him) (by positivity : (0 : ℝ) ≤ 28 ^ (m - i))
    have hg := mul_le_mul hr (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdi) hε)
      (by positivity : (0 : ℝ) ≤ ε * 2 ^ dyadicSlack m i) (by positivity : (0 : ℝ) ≤ 32 ^ d)
    apply hm.trans (hg.trans_eq ?_)
    rw [mul_left_comm, ←mul_pow]
    norm_num
  calc
    _ ≤ ∑ _i ∈ Ico j m, ε * 64 ^ d := sum_le_sum ht
    _ = (m - j : ℕ) * (ε * 64 ^ d) := by simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ d * (ε * 64 ^ d) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hd
    _ = ε * 128 ^ d := by rw [mul_left_comm, ←mul_pow]; norm_num

open Classical in
/-- The concrete floor/capacity/mean schedule supplies a summable fourth-moment budget,
with no convergence premise or configurable floor framework. -/
lemma mean_schedule_budget {η M ε : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (m j : ℕ) :
    ((2 + 256 * M / dyadicFloor η m j) / ((2 : ℝ) ^ (64 * dyadicSlack m j))) *
      (ε * 128 ^ dyadicSlack m j) ^ 4 ≤
      (2 + 256 * M / η) * ε ^ 4 * ((1 / 64 : ℝ) ^ dyadicSlack m j) ^ 4 :=
  mean_schedule_term hη hM _

end Cslib.RowCompression
namespace Cslib.RowCompression
open Finset
open scoped BigOperators
open Classical in
/-- The actual false-first-overflow charge is summable with slope-one prefix budgets. -/
lemma false_schedule_identity (η ε : ℝ) (d : ℕ) :
    (ε * 2 ^ d) ^ 4 / ((2 : ℝ) ^ (64 * d) * (η * (1 / 1024) ^ d) ^ 4) =
      ε ^ 4 / η ^ 4 * (1 / 1048576 : ℝ) ^ d := by
  rw [mul_pow, mul_pow, show (2 : ℝ) ^ (64 * d) = ((2 : ℝ) ^ 64) ^ d by rw [pow_mul],
    show ((2 : ℝ) ^ d) ^ 4 = ((2 : ℝ) ^ 4) ^ d by rw [←pow_mul, Nat.mul_comm, pow_mul],
    show (((1 / 1024 : ℝ) ^ d) ^ 4) = ((1 / 1024 : ℝ) ^ 4) ^ d by rw [←pow_mul, Nat.mul_comm,
      pow_mul]]
  norm_num only [show (2 : ℝ) ^ 64 = 18446744073709551616 by norm_num,
    show (2 : ℝ) ^ 4 = 16 by norm_num, show (1 / 1024 : ℝ) ^ 4 = 1 / 1099511627776 by norm_num]
  simp only [div_pow, one_pow]
  field_simp
  calc
    _ = ε ^ 4 * η⁻¹ ^ 4 * ((16 : ℝ) ^ d * (1048576 : ℝ) ^ d * (1099511627776 : ℝ) ^ d) := by ring
    _ = _ := by norm_num [←mul_pow]; ring

open Classical in
lemma false_schedule_sum {η ε R K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) (m : ℕ) :
    ∑ i ∈ range m, (64 * K * R ^ 4 / ((2 : ℝ) ^ (64 * dyadicSlack m i) * dyadicFloor η m i ^ 4)) *
      (ε * 2 ^ dyadicSlack m i) ^ 4 ≤ 64 * K * R ^ 4 / η ^ 4 * ε ^ 4 / 63 := by
  have hs := sum_propagation_mul_dyadic_decay_le (C := 1) (q := (1 / 64 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) m
  norm_num only [one_pow, one_mul, show (1 : ℝ) * (1 / 64) / (1 - 1 * (1 / 64))=1 / 63 by norm_num]
    at hs
  calc
    _ = (64 * K * R ^ 4 / η ^ 4 * ε ^ 4) * ∑ i ∈ range m, (1 / 1048576 : ℝ) ^ dyadicSlack m i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      have hi := false_schedule_identity η ε (dyadicSlack m i)
      change _ = _
      dsimp only [dyadicFloor]
      calc
        _ = (64 * K * R ^ 4) * ((ε * 2 ^ dyadicSlack m i) ^ 4 /
          ((2 : ℝ) ^ (64 * dyadicSlack m i) * (η * (1 / 1024) ^ dyadicSlack m i) ^ 4)) := by ring
        _ = _ := by rw [hi]; ring
    _ ≤ (64 * K * R ^ 4 / η ^ 4 * ε ^ 4) * (1 / 63) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_le_sum fun i _ => pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 1048576 : ℝ) ≤
        1 / 64) _).trans hs
    _ = _ := by ring

open Classical in
/-- The weighted preloss budget has no horizon factor. -/
lemma pre_schedule_sum {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε) (m : ℕ) :
    ∑ i ∈ range m, dyadicFloor η m i * (ε * 2 ^ dyadicSlack m i) ≤ η * ε / 511 := by
  have hs := sum_propagation_mul_dyadic_decay_le (C := 1) (q := (1 / 512 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) m
  norm_num only [one_pow, one_mul, show (1 : ℝ) * (1 / 512) / (1 - 1 * (1 / 512))=1 / 511 by
    norm_num] at hs
  calc
    _ = η * ε * ∑ i ∈ range m, (1 / 512 : ℝ) ^ dyadicSlack m i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      dsimp only [dyadicFloor]
      rw [show (1 / 512 : ℝ) = (1 / 1024) * 2 by norm_num, mul_pow]
      ring
    _ ≤ η * ε * (1 / 511) := mul_le_mul_of_nonneg_left hs (mul_nonneg hη hε)
    _ = _ := by ring
end Cslib.RowCompression
namespace Cslib.RowCompression
open Finset
open scoped BigOperators
open Classical in
/-- A larger actual capacity lowers the numerical false-event charge. No comparison
between outputs of different compression schedules is used. -/
lemma false_schedule_sum_capacity {η ε R K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    (m : ℕ) (n : ℕ → ℕ) (hn : ∀ i < m, 2 ^ (64 * dyadicSlack m i) ≤ n i) :
    ∑ i ∈ range m, (64 * K * R ^ 4 / ((n i : ℝ) * dyadicFloor η m i ^ 4)) *
      (ε * 2 ^ dyadicSlack m i) ^ 4 ≤ 64 * K * R ^ 4 / η ^ 4 * ε ^ 4 / 63 := by
  refine le_trans (sum_le_sum fun i hi => ?_) (false_schedule_sum hη hK m)
  have hf := dyadicFloor_pos hη m i
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast hn i (mem_range.mp hi)
end Cslib.RowCompression
