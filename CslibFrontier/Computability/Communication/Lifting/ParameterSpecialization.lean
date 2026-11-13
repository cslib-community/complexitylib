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
# A polynomial-alphabet parameter certificate

The elementary fourth-power XOR bound admits a concrete polynomial-size specialization.
For an ambient bound `B ≥ n`, use alphabet size `B^2048`, speaker density `B^1984`, other
speaker density `B^2016`, and target density `B^1984`. Uniform gadget discrepancy at most
`B^(-1024)` suffices. The constants are deliberately loose; this certificate does not claim
the sharper parameters of the original lifting theorem.
-/

public section

namespace Cslib.Communication.Lifting

/-- Explicit scalar parameters for the rare-danger theorem, with the speaker density equal
to the target density as needed by the alternating simulation. -/
theorem polynomial_parameter_certificate {B N D : ℝ} (hB : 2 ≤ B)
    (hN : 2 ≤ N) (hNB : N ≤ B) (hD : D ≤ (B ^ 1024)⁻¹) :
    16 * N ^ 2 ≤ B ^ 2016 / B ^ 1984 ∧
    N ^ (2 * 16) ≤ B ^ 2016 / B ^ 1984 ∧
    1 ≤ B ^ 129 ∧
    N * B ^ 2048 ≤ (B ^ 129) ^ 16 ∧
    0 < 1 / (4 * B ^ 131) ∧
    N * (N + 1) * B ^ 129 * (1 / (4 * B ^ 131)) ≤ 1 / 2 ∧
    16384 * ((B ^ 2048) ^ 2 * N ^ 2 / (B ^ 1984 * B ^ 2016)) ^ 4 * D ≤
      ((1 / (4 * B ^ 131)) / (2 * N)) ^ 4 := by
  have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hB1 : 1 ≤ B := le_trans (by norm_num) hB
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hgap : B ^ 2016 / B ^ 1984 = B ^ 32 := by
    apply (div_eq_iff (pow_ne_zero _ hBp.ne')).2
    rw [← pow_add]
  have h16 : (16 : ℝ) ≤ B ^ 4 := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hB _
  have hN2 : N ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hNp.le hNB _
  have hgap16 : 16 * N ^ 2 ≤ B ^ 32 := by
    calc
      _ ≤ B ^ 4 * B ^ 2 := mul_le_mul h16 hN2 (by positivity) (by positivity)
      _ = B ^ 6 := by rw [← pow_add]
      _ ≤ _ := pow_le_pow_right₀ hB1 (by norm_num)
  have hsize : N * B ^ 2048 ≤ (B ^ 129) ^ 16 := by
    calc
      _ ≤ B * B ^ 2048 := mul_le_mul_of_nonneg_right hNB (pow_nonneg hBp.le _)
      _ = B ^ 2049 := by ring
      _ ≤ B ^ 2064 := pow_le_pow_right₀ hB1 (by norm_num)
      _ = _ := by rw [← pow_mul]
  have hweight : N * (N + 1) * B ^ 129 * (1 / (4 * B ^ 131)) ≤ 1 / 2 := by
    have hNN : N * (N + 1) ≤ 2 * B ^ 2 := by
      have hp := mul_le_mul hNB (show N + 1 ≤ 2 * B by linarith) (by linarith) hBp.le
      nlinarith
    calc
      _ ≤ (2 * B ^ 2) * B ^ 129 * (1 / (4 * B ^ 131)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNN (by positivity))
          (by positivity)
      _ = 1 / 2 := by field_simp; ring
  refine ⟨by simpa only [hgap] using hgap16, ?_, one_le_pow₀ hB1, hsize,
    by positivity, hweight, ?_⟩
  · rw [hgap]
    exact pow_le_pow_left₀ hNp.le hNB _
  · have hK : (B ^ 2048) ^ 2 * N ^ 2 / (B ^ 1984 * B ^ 2016) = B ^ 96 * N ^ 2 := by
      apply (div_eq_iff (mul_ne_zero (pow_ne_zero _ hBp.ne') (pow_ne_zero _ hBp.ne'))).2
      ring
    rw [hK]
    have hKle : B ^ 96 * N ^ 2 ≤ B ^ 98 := by
      calc
        _ ≤ B ^ 96 * B ^ 2 := mul_le_mul_of_nonneg_left hN2 (by positivity)
        _ = _ := by rw [← pow_add]
    have hconst : (67108864 : ℝ) ≤ B ^ 104 := by
      calc
        _ = (2 : ℝ) ^ 26 := by norm_num
        _ ≤ B ^ 26 := pow_le_pow_left₀ (by norm_num) hB _
        _ ≤ _ := pow_le_pow_right₀ hB1 (by norm_num)
    have hbound : 16384 * (B ^ 98) ^ 4 * (B ^ 1024)⁻¹ ≤
        ((1 / (4 * B ^ 131)) / (2 * B)) ^ 4 := by
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hconst (pow_nonneg hBp.le 920)]
    have hfrac : (1 / (4 * B ^ 131)) / (2 * B) ≤
        (1 / (4 * B ^ 131)) / (2 * N) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hNB (by norm_num)
    calc
      _ ≤ 16384 * (B ^ 96 * N ^ 2) ^ 4 * (B ^ 1024)⁻¹ :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      _ ≤ 16384 * (B ^ 98) ^ 4 * (B ^ 1024)⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hKle 4)
            (by norm_num)) (by positivity)
      _ ≤ ((1 / (4 * B ^ 131)) / (2 * B)) ^ 4 := hbound
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hfrac 4

/-- The polynomial parameters leave strict density headroom at both levels, and each query
contributes at least a factor `B^31` to the simulation's potential budget. -/
theorem polynomial_density_ratios {B : ℝ} (hB : 2 ≤ B) :
    0 < B ^ 1984 ∧ B ^ 1984 < B ^ 2016 ∧ B ^ 2016 < B ^ 2048 ∧
      B ^ 31 ≤ B ^ 2048 / (2 * B ^ 2016) := by
  have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB
  refine ⟨pow_pos hBp _, pow_lt_pow_right₀ hB1 (by norm_num),
    pow_lt_pow_right₀ hB1 (by norm_num), ?_⟩
  have heq : B ^ 2048 / (2 * B ^ 2016) = B ^ 32 / 2 := by
    field_simp
  rw [heq]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    _ ≤ B ^ 31 * B := mul_le_mul_of_nonneg_left hB (pow_nonneg hBp.le _)
    _ = _ := by ring

end Cslib.Communication.Lifting
