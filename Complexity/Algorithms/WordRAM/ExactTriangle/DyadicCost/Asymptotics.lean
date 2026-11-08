/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicCost
public import Complexity.Foundations.Data.Nat.LogRpow
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorbing the complete cubic logarithmic box coefficient

The finite native ledger has degree three in tensor depth. A single threshold per fixed
original weight exponent absorbs that full coefficient into every positive real input power.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicCost

open Filter Cslib.Matrix Cslib.Algorithms.ExactTriangle
open ParameterChoice

/-- Degree-three logarithmic coefficient retaining the finite native box charges. -/
@[expose] noncomputable def costCoefficient (κ : ℝ) (n : ℕ) : ℝ :=
  238169 + 16 * (Nat.log 2 n : ℝ) +
    125829120 * ((21 * level n + 1 : ℕ) : ℝ) ^ 2 * ((level n + 1 : ℕ) : ℝ) +
      (140 * falsePositiveConst + 140) * κ * Real.log n

/-- Increasing the original weight exponent increases only the charged scan allowance. -/
theorem costCoefficient_mono {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (h : a ≤ b) :
    costCoefficient a n ≤ costCoefficient b n := by
  have hC : 0 ≤ falsePositiveConst := (by norm_num : (0 : ℝ) ≤ 1).trans one_le_falsePositiveConst
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (140 * falsePositiveConst + 140) * Real.log (n : ℝ) by positivity)
  unfold costCoefficient
  nlinarith only [hm]

private noncomputable def logCoefficient (κ : ℝ) : ℝ :=
  238169 + 16 + 441 * 125829120 + (140 * falsePositiveConst + 140) * κ

private theorem logCoefficient_pos {κ : ℝ} (hκ : 1 ≤ κ) : 0 < logCoefficient κ := by
  have hC : 0 ≤ falsePositiveConst := (by norm_num : (0 : ℝ) ≤ 1).trans one_le_falsePositiveConst
  have hk : 0 ≤ κ := by linarith
  unfold logCoefficient
  positivity

private theorem coefficient_le_log_cube {n : ℕ} {κ : ℝ} (hn : 1 ≤ n) (hκ : 1 ≤ κ) :
    costCoefficient κ n ≤ logCoefficient κ * ((Nat.log 2 n : ℝ) + 1) ^ 3 := by
  let L : ℝ := (Nat.log 2 n : ℝ) + 1
  have hL : 1 ≤ L := by
    dsimp only [L]
    have h := Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)
    linarith only [h]
  have hLcube : L ≤ L ^ 3 := le_self_pow₀ hL (by decide)
  have hunit : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n).le
  have hl : Real.log (n : ℝ) ≤ L * Real.log 2 := by
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one, L] using Real.log_le_log hn0 hpow
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hlog : Real.log (n : ℝ) ≤ L ^ 3 :=
    (hl.trans ((mul_le_mul_of_nonneg_left htwo (by positivity)).trans_eq (mul_one L))).trans hLcube
  have hlevel : (level n : ℝ) ≤ Nat.log 2 n := by exact_mod_cast level_le_log n
  have hleft : ((21 * level n + 1 : ℕ) : ℝ) ≤ 21 * L := by
    push_cast
    dsimp only [L]
    linarith only [hlevel]
  have hright : ((level n + 1 : ℕ) : ℝ) ≤ L := by
    push_cast
    dsimp only [L]
    linarith only [hlevel]
  have hdepth : ((21 * level n + 1 : ℕ) : ℝ) ^ 2 * ((level n + 1 : ℕ) : ℝ) ≤
      441 * L ^ 3 := by
    calc
      _ ≤ (21 * L) ^ 2 * L :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hleft 2) hright (by positivity) (by positivity)
      _ = _ := by ring
  have hprod := mul_le_mul_of_nonneg_left hdepth (by norm_num : (0 : ℝ) ≤ 125829120)
  have hconst := mul_le_mul_of_nonneg_left hunit (by norm_num : (0 : ℝ) ≤ 238169)
  have hlinear : 16 * (Nat.log 2 n : ℝ) ≤ 16 * L ^ 3 := by
    have hsmall : (Nat.log 2 n : ℝ) ≤ L := by dsimp only [L]; linarith
    exact mul_le_mul_of_nonneg_left (hsmall.trans hLcube) (by norm_num)
  have hC : 0 ≤ falsePositiveConst := (by norm_num : (0 : ℝ) ≤ 1).trans one_le_falsePositiveConst
  have hk : 0 ≤ κ := by linarith
  have hscan := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ (140 * falsePositiveConst + 140) * κ by positivity)
  dsimp only [costCoefficient, logCoefficient]
  change _ ≤ _ * L ^ 3
  nlinarith only [hprod, hconst, hlinear, hscan]

/-- Every fixed positive power eventually absorbs the complete degree-three coefficient. -/
theorem costCoefficient_eventually_le_rpow {κ ε : ℝ} (hκ : 1 ≤ κ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, costCoefficient κ n ≤ (n : ℝ) ^ ε := by
  have h := Nat.eventually_mul_log_add_pow_le_rpow (by decide : 1 < (2 : ℕ))
    0 1 3 (K := logCoefficient κ) (logCoefficient_pos hκ) hε
  filter_upwards [h, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hpos
  exact (coefficient_le_log_cube hpos hκ).trans
    (by simpa only [Nat.add_zero, Nat.cast_one] using hn)

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicCost
