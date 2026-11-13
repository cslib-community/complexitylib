/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# General polynomial-alphabet parameter certificates

For every integer `k ≥ 1`, the alphabet exponent is `2048 k²`, while the discrepancy
exponent is `1024 k`. Thus the assumed discrepancy is the alphabet size raised to
`-1/(2k)`. The two density losses are `64k` and `32k` in the same base. The statements use
a subtraction-free lower density exponent `a`, with `a + 64k = 2048 k²`.
These deliberately loose constants provide a parameter family for every positive fixed
discrepancy exponent, rather than the sharper parameters of the source theorem.
-/

public section

namespace Cslib.Communication.Lifting

/-- Explicit scalar parameters for the rare-danger theorem, with the speaker density equal
to the target density as needed by the alternating simulation. -/
theorem general_parameter_certificate {B N D : ℝ} {a k : ℕ}
    (hk : 1 ≤ k) (ha : a + 64 * k = 2048 * k ^ 2) (hB : 2 ≤ B)
    (hN : 2 ≤ N) (hNB : N ≤ B) (hD : D ≤ (B ^ (1024 * k))⁻¹) :
    16 * N ^ 2 ≤ B ^ (a + 32 * k) / B ^ a ∧
    N ^ (2 * (16 * k)) ≤ B ^ (a + 32 * k) / B ^ a ∧
    1 ≤ B ^ (128 * k + 1) ∧
    N * B ^ (a + 64 * k) ≤ (B ^ (128 * k + 1)) ^ (16 * k) ∧
    0 < 1 / (4 * B ^ (128 * k + 3)) ∧
    N * (N + 1) * B ^ (128 * k + 1) * (1 / (4 * B ^ (128 * k + 3))) ≤ 1 / 2 ∧
    16384 * ((B ^ (a + 64 * k)) ^ 2 * N ^ 2 / (B ^ a * B ^ (a + 32 * k))) ^ 4 * D ≤
      ((1 / (4 * B ^ (128 * k + 3))) / (2 * N)) ^ 4 := by
  have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hB1 : 1 ≤ B := le_trans (by norm_num) hB
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hgap : B ^ (a + 32 * k) / B ^ a = B ^ (32 * k) := by
    apply (div_eq_iff (pow_ne_zero _ hBp.ne')).2
    rw [← pow_add]
    congr 1
    omega
  have h16 : (16 : ℝ) ≤ B ^ 4 := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hB _
  have hN2 : N ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hNp.le hNB _
  have hgap16 : 16 * N ^ 2 ≤ B ^ (32 * k) := by
    calc
      _ ≤ B ^ 4 * B ^ 2 := mul_le_mul h16 hN2 (by positivity) (by positivity)
      _ = B ^ 6 := by rw [← pow_add]
      _ ≤ _ := pow_le_pow_right₀ hB1 (by omega)
  have hsize : N * B ^ (a + 64 * k) ≤ (B ^ (128 * k + 1)) ^ (16 * k) := by
    calc
      _ ≤ B * B ^ (a + 64 * k) := mul_le_mul_of_nonneg_right hNB (pow_nonneg hBp.le _)
      _ = B ^ (1 + (a + 64 * k)) := by simp only [pow_add, pow_one]
      _ ≤ B ^ ((128 * k + 1) * (16 * k)) := by
        apply pow_le_pow_right₀ hB1
        nlinarith
      _ = _ := pow_mul _ _ _
  have hweight : N * (N + 1) * B ^ (128 * k + 1) * (1 / (4 * B ^ (128 * k + 3))) ≤ 1 / 2 := by
    have hNN : N * (N + 1) ≤ 2 * B ^ 2 := by
      have hp := mul_le_mul hNB (show N + 1 ≤ 2 * B by linarith) (by linarith) hBp.le
      nlinarith
    calc
      _ ≤ (2 * B ^ 2) * B ^ (128 * k + 1) * (1 / (4 * B ^ (128 * k + 3))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNN (by positivity))
          (by positivity)
      _ = 1 / 2 := by
        have he : B ^ (128 * k + 3) = B ^ 2 * B ^ (128 * k + 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [he]
        field_simp
        norm_num
  refine ⟨by simpa only [hgap] using hgap16, ?_, one_le_pow₀ hB1, hsize,
    by positivity, hweight, ?_⟩
  · rw [hgap]
    convert pow_le_pow_left₀ hNp.le hNB (32 * k) using 1; congr 1; omega
  · have hK : (B ^ (a + 64 * k)) ^ 2 * N ^ 2 / (B ^ a * B ^ (a + 32 * k)) =
        B ^ (96 * k) * N ^ 2 := by
      apply (div_eq_iff (mul_ne_zero (pow_ne_zero _ hBp.ne') (pow_ne_zero _ hBp.ne'))).2
      simp only [← pow_mul, ← pow_add]
      ring_nf
    rw [hK]
    have hKle : B ^ (96 * k) * N ^ 2 ≤ B ^ (96 * k + 2) := by
      calc
        _ ≤ B ^ (96 * k) * B ^ 2 := mul_le_mul_of_nonneg_left hN2 (by positivity)
        _ = _ := by rw [← pow_add]
    have hconst : (67108864 : ℝ) ≤ B ^ (104 * k) := by
      calc
        _ = (2 : ℝ) ^ 26 := by norm_num
        _ ≤ B ^ 26 := pow_le_pow_left₀ (by norm_num) hB _
        _ ≤ _ := pow_le_pow_right₀ hB1 (by omega)
    have hbound : 16384 * (B ^ (96 * k + 2)) ^ 4 * (B ^ (1024 * k))⁻¹ ≤
        ((1 / (4 * B ^ (128 * k + 3))) / (2 * B)) ^ 4 := by
      field_simp
      have heq : 16384 * (B ^ (96 * k + 2)) ^ 4 * 4 ^ 4 *
          (B ^ (128 * k + 3)) ^ 4 * 2 ^ 4 * B ^ 4 =
          67108864 * B ^ (896 * k + 24) := by
        simp only [← pow_mul]
        ring_nf
      rw [heq]
      calc
        _ ≤ B ^ (104 * k) * B ^ (896 * k + 24) :=
          mul_le_mul_of_nonneg_right hconst (pow_nonneg hBp.le _)
        _ = B ^ (1000 * k + 24) := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := pow_le_pow_right₀ hB1 (by omega)
    have hfrac : (1 / (4 * B ^ (128 * k + 3))) / (2 * B) ≤
        (1 / (4 * B ^ (128 * k + 3))) / (2 * N) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hNB (by norm_num)
    calc
      _ ≤ 16384 * (B ^ (96 * k) * N ^ 2) ^ 4 * (B ^ (1024 * k))⁻¹ :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      _ ≤ 16384 * (B ^ (96 * k + 2)) ^ 4 * (B ^ (1024 * k))⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hKle 4)
            (by norm_num)) (by positivity)
      _ ≤ ((1 / (4 * B ^ (128 * k + 3))) / (2 * B)) ^ 4 := hbound
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hfrac 4


/-- The adjustable family retains strict density headroom and a query potential factor
`B^(32k-1)`. The lower density exponent `a` may be chosen independently. -/
theorem general_density_ratios {B : ℝ} {a k : ℕ} (hk : 1 ≤ k) (hB : 2 ≤ B) :
    0 < B ^ a ∧ B ^ a < B ^ (a + 32 * k) ∧
      B ^ (a + 32 * k) < B ^ (a + 64 * k) ∧
      B ^ (32 * k - 1) ≤ B ^ (a + 64 * k) / (2 * B ^ (a + 32 * k)) := by
  have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB
  refine ⟨pow_pos hBp _, pow_lt_pow_right₀ hB1 (by omega),
    pow_lt_pow_right₀ hB1 (by omega), ?_⟩
  have heq : B ^ (a + 64 * k) / (2 * B ^ (a + 32 * k)) = B ^ (32 * k) / 2 := by
    field_simp
    simp only [← pow_add]
    congr 1
    omega
  rw [heq]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    _ ≤ B ^ (32 * k - 1) * B := mul_le_mul_of_nonneg_left hB (pow_nonneg hBp.le _)
    _ = B ^ (32 * k) := by
      rw [← pow_succ]
      congr 1
      omega

/-- The subtraction-free density exponent agrees with the polynomial alphabet exponent. -/
theorem general_lowerDensityExponent_add {k : ℕ} (hk : 1 ≤ k) :
    (2048 * k ^ 2 - 64 * k) + 64 * k = 2048 * k ^ 2 := by
  apply Nat.sub_add_cancel
  nlinarith

end Cslib.Communication.Lifting
