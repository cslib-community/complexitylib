/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicCost
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform strict-subcubic component budgets

Mathlib's logarithm-versus-real-power theorem absorbs the logarithmic coefficient of the
computed dyadic native budgets. The resulting threshold depends only on the original weight
exponent; it is shared by all matrices, selected primes and reference memories.

This is an asymptotic theorem about the existing proved component charges. It does not assemble
an execution, account for the callable adapter or dispatch small inputs, and does not assert
the source's tuned 3SUM exponent.

## Main results

* `costCoefficient_mono`: monotonicity in the original-weight exponent.
* `costCoefficient_eventually_le_rpow`: reusable coefficient absorption for concrete native callers.

* `exists_components_subcubic_threshold`: beyond one threshold, the actual component allowance
  is at most `4*n^(3-1/1296)`, uniformly over original weights bounded by `n^κ`.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicCost

open Filter Cslib.Matrix Cslib.Algorithms.ExactTriangle
open ParameterChoice

/-- The explicit coefficient in the proved dyadic component allowance. This is a numerical
upper estimate, not an execution contract supplied to an algorithm. -/
@[expose] noncomputable def costCoefficient (κ : ℝ) (n : ℕ) : ℝ :=
  238169 + 12 * (Nat.log 2 n : ℝ) + 138412032 * ((19 * level n + 1 : ℕ) : ℝ) +
    (140 * falsePositiveConst + 140) * κ * Real.log n

/-- The component coefficient is monotone in its weight exponent for positive dimensions. -/
theorem costCoefficient_mono {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (h : a ≤ b) :
    costCoefficient a n ≤ costCoefficient b n := by
  have hC : 0 ≤ falsePositiveConst := (by norm_num : (0 : ℝ) ≤ 1).trans one_le_falsePositiveConst
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (140 * falsePositiveConst + 140) * Real.log (n : ℝ) by positivity)
  unfold costCoefficient
  nlinarith only [hm]

private noncomputable def logCoefficient (κ : ℝ) : ℝ :=
  238169 + 138412032 + (12 + 19 * 138412032) / Real.log 2 +
    (140 * falsePositiveConst + 140) * κ

private theorem logCoefficient_pos {κ : ℝ} (hκ : 1 ≤ κ) : 0 < logCoefficient κ := by
  have hC : 0 ≤ falsePositiveConst := (by norm_num : (0 : ℝ) ≤ 1).trans one_le_falsePositiveConst
  have hk : 0 ≤ κ := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold logCoefficient
  positivity

private theorem coefficient_le_log {n : ℕ} {κ : ℝ} (hn : 16 ≤ n) :
    costCoefficient κ n ≤ logCoefficient κ * Real.log n := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 ≤ Real.log n :=
    (Real.le_log_iff_exp_le (by linarith)).mpr
      (Real.exp_one_lt_three.le.trans (by linarith))
  have hl : (level n : ℝ) ≤ Nat.log 2 n := by exact_mod_cast level_le_log n
  have hb : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb n 2
  unfold costCoefficient logCoefficient
  push_cast
  have hlevel := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 19 * 138412032)
  have hconstant := mul_le_mul_of_nonneg_left hlog1
    (by norm_num : (0 : ℝ) ≤ 238169 + 138412032)
  calc
    _ ≤ (238169 + 138412032) + (12 + 19 * 138412032) * (Nat.log 2 n : ℝ) +
        (140 * falsePositiveConst + 140) * κ * Real.log n := by nlinarith only [hlevel]
    _ ≤ (238169 + 138412032) + (12 + 19 * 138412032) * (Real.log n / Real.log 2) +
        (140 * falsePositiveConst + 140) * κ * Real.log n :=
      by gcongr
    _ ≤ (238169 + 138412032) * Real.log n +
        (12 + 19 * 138412032) * (Real.log n / Real.log 2) +
        (140 * falsePositiveConst + 140) * κ * Real.log n :=
      by
        gcongr
        simpa only [mul_one] using hconstant
    _ = _ := by ring

/-- The complete component coefficient, including all logarithmic terms, is eventually at
most any fixed positive real power. Its threshold is chosen before original matrix data. -/
theorem costCoefficient_eventually_le_rpow {κ ε : ℝ} (hκ : 1 ≤ κ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, costCoefficient κ n ≤ (n : ℝ) ^ ε := by
  have hc := logCoefficient_pos hκ
  have hlog : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ ε) :=
    (isLittleO_log_rpow_atTop hε).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (16 : ℕ), hlog.bound (inv_pos.mpr hc)] with n hn hsmall
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hpow0 : 0 ≤ (n : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg n) ε
  rw [Real.norm_eq_abs, abs_of_nonneg hlog0, Real.norm_eq_abs, abs_of_nonneg hpow0] at hsmall
  calc
    _ ≤ logCoefficient κ * Real.log n := coefficient_le_log hn
    _ ≤ logCoefficient κ * ((logCoefficient κ)⁻¹ * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left hsmall hc.le
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

-- Permit the fixed 1296-bit fast-threshold numeral during filter transport.
set_option exponentiation.threshold 1296 in
private theorem components_eventually_le {κ ε : ℝ} (hκ : 1 ≤ κ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 0 < n) (values : List ℤ) (mem : ℕ → ℕ) (p : ℕ),
      WeightsBoundedBy
        (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
        (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
        (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) ((n : ℝ) ^ κ) →
      IsSelectedPrime
        (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
        (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
        (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) (window n) p →
      ((12 * Nat.log 2 n + 36 + (PrimeSelection.timeBound n (window n) + 16) +
          FixedPrime.timeBound (m := level n) hn (groups n) p values mem : ℕ) : ℝ) ≤
        4 * (n : ℝ) ^ (3 - 1 / 648 + ε : ℝ) := by
  filter_upwards [costCoefficient_eventually_le_rpow hκ hε,
    eventually_ge_atTop (2 ^ 1296 : ℕ)] with n hc hfast
  intro hn values mem p hv hp
  have hf := (blocks_pos_iff n).mpr hfast
  have hb := components_timeBound_le hf hκ values mem hv hp
  change (_ : ℝ) ≤ costCoefficient κ n * ((n : ℝ) ^ 3 / groups n) at hb
  calc
    _ ≤ costCoefficient κ n * ((n : ℝ) ^ 3 / groups n) := hb
    _ ≤ (n : ℝ) ^ ε * ((n : ℝ) ^ 3 / groups n) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (n : ℝ) ^ ε * (4 * (n : ℝ) ^ (3 - 1 / 648 : ℝ)) :=
      mul_le_mul_of_nonneg_left (cubic_div_groups_le hn) (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add (by exact_mod_cast hn)]
      congr 2
      ring

/-- A single threshold for each original weight exponent bounds all actual component charges
strictly below cubic. It is independent of the original matrices, chosen prime, reference
memory and physical width. The existing budget's positive-input proof is explicit; positivity
also follows from the threshold. This does not assert an execution of a composed solver. -/
theorem exists_components_subcubic_threshold {κ : ℝ} (hκ : 1 ≤ κ) :
    ∃ N : ℕ, 2 ^ 1296 ≤ N ∧
      ∀ n ≥ N, ∀ (hn : 0 < n) (values : List ℤ) (mem : ℕ → ℕ) (p : ℕ),
        WeightsBoundedBy
          (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
          (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
          (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) ((n : ℝ) ^ κ) →
        IsSelectedPrime
          (fun u v : Fin n => values.getD (pairIndex (u, v)) 0)
          (fun u v => values.getD (n * n + pairIndex (u, v)) 0)
          (fun u v => values.getD (2 * (n * n) + pairIndex (u, v)) 0) (window n) p →
        ((12 * Nat.log 2 n + 36 + (PrimeSelection.timeBound n (window n) + 16) +
            FixedPrime.timeBound (m := level n) hn (groups n) p values mem : ℕ) : ℝ) ≤
          4 * (n : ℝ) ^ (3 - 1 / 1296 : ℝ) := by
  have h := components_eventually_le hκ (by norm_num : (0 : ℝ) < 1 / 1296)
  rw [show (3 - 1 / 648 + 1 / 1296 : ℝ) = 3 - 1 / 1296 by norm_num] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max N (2 ^ 1296), le_max_right _ _, ?_⟩
  intro n hn
  exact hN n ((le_max_left _ _).trans hn)

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicCost
