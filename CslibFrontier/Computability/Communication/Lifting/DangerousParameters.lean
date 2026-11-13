/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Explicit parameters for the dangerous-values argument

These arithmetic bounds support the numerical specialization of the finite witness criterion.
The intended parameters are `L = log₂ n` and `A = ε b |J| + e`, where `e` is the excess entropy
of a supported conditioning value. The threshold uses `A - 2`, ensuring that the two bits
needed by the high-order parity bound are actually paid for. This module proves arithmetic
facts, not the main rare-dangerous-values theorem.
-/

public section

namespace Cslib.Communication.Lifting

/-- A positive integer threshold with both enough eligible high-order parities and the
required entropy slack. This includes the floor rounding explicitly. -/
theorem exists_dangerous_parity_threshold {L A : ℝ} (hL : 1 ≤ L) (hA : 2 * L + 4 ≤ A) :
    ∃ t : ℕ, 1 ≤ t ∧ A ≤ 2 * L * t ∧ (t : ℝ) * L ≤ A - 2 := by
  have hL0 : 0 < L := by linarith
  have hq : 0 ≤ (A - 2) / L := div_nonneg (by linarith) hL0.le
  refine ⟨⌊(A - 2) / L⌋₊, Nat.le_floor ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hL0).mpr
    norm_num
    linarith
  · have h := Nat.lt_floor_add_one ((A - 2) / L)
    have h' := (div_lt_iff₀ hL0).mp h
    nlinarith
  · exact (le_div_iff₀ hL0).mp (Nat.floor_le hq)

/-- A large slice-probability ratio admits an integer threshold that both pays the low-order
count and makes all larger parities eligible. The formulation avoids rounding a real entropy. -/
theorem exists_power_threshold_of_ratio {N R : ℝ} (hN : 2 ≤ N) (hR : 16 * N ^ 2 ≤ R) :
    ∃ t : ℕ, 1 ≤ t ∧ N ^ t ≤ R / 4 ∧ R ≤ N ^ (2 * t) := by
  have hN0 : 0 < N := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hL : 1 ≤ Real.logb 2 N := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hN
    simpa using h
  have h16 : Real.logb 2 16 = 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.logb_pow]
    norm_num
  have hA : 2 * Real.logb 2 N + 4 ≤ Real.logb 2 R := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (by positivity : 0 < 16 * N ^ 2) hR
    rw [Real.logb_mul (by norm_num) (pow_ne_zero _ hN0.ne'), Real.logb_pow, h16] at h
    norm_num at h
    linarith
  obtain ⟨t, ht, hlower, hupper⟩ := exists_dangerous_parity_threshold hL hA
  have hpow (k : ℕ) : (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 N) = N ^ k := by
    rw [mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hN0, Real.rpow_natCast]
  refine ⟨t, ht, ?_, ?_⟩
  · calc
      N ^ t = (2 : ℝ) ^ ((t : ℝ) * Real.logb 2 N) := (hpow t).symm
      _ ≤ 2 ^ (Real.logb 2 R - 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hupper
      _ = R / 4 := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hR0]
        norm_num
  · have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlower
    rw [Real.rpow_logb (by norm_num) (by norm_num) hR0] at h
    have heq : (2 : ℝ) * Real.logb 2 N * t = ((2 * t : ℕ) : ℝ) * Real.logb 2 N := by
      push_cast
      ring
    rw [heq, hpow] at h
    exact h

/-- A generous density-sum margin pays the losses from the fourth-power XOR estimate,
conditioning-witness counting, and the outer geometric sum. All factors are explicit; no
asymptotic notation or unproved probabilistic premise is hidden in this arithmetic lemma. -/
theorem dangerous_density_margin {L b ε η γ δX δY : ℝ}
    (hL : 1 ≤ L) (hb : 0 < b) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : 6 * L ≤ ε * b)
    (hdensity : 2 - η / 4 + γ + 16 * L / (ε * b) ≤ δX + δY) :
    γ * b + 5 * L + 5 + 2 * L * (b + L) / (ε * b) ≤
      (δX + δY - 2 + η / 4) * b - 1 / 2 := by
  have hL0 : 0 ≤ L := by linarith
  have heb : 0 < ε * b := mul_pos hε hb
  have hLb : L ≤ b := by nlinarith [mul_le_mul_of_nonneg_right hε1 hb.le]
  have hfrac : 2 * L * (b + L) / (ε * b) ≤ 4 * L / ε := by
    apply (div_le_iff₀ heb).mpr
    have heq : 4 * L / ε * (ε * b) = 4 * L * b := by field_simp
    rw [heq]
    nlinarith
  have hLε : L ≤ L / ε := by
    apply (le_div_iff₀ hε).mpr
    exact mul_le_of_le_one_right hL0 hε1
  have hmul := mul_le_mul_of_nonneg_right hdensity hb.le
  have heq : (2 - η / 4 + γ + 16 * L / (ε * b)) * b =
      (2 - η / 4 + γ) * b + 16 * (L / ε) := by field_simp
  rw [heq] at hmul
  have hfrac' : 2 * L * (b + L) / (ε * b) ≤ 4 * (L / ε) := by
    simpa only [mul_div_assoc] using hfrac
  nlinarith [hfrac']

end Cslib.Communication.Lifting
