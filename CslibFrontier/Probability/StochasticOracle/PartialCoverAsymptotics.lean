/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCoverGreedy
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-!
# Asymptotic factors for the source greedy multicover

The numerical factor in `Multicover.greedy_risk_bill` is the actual factor of
[Wang2027], Theorem 4 (PDF pp. 10–11). For fixed failure budget it is quadratic
in the logarithm of the ground-set size; polynomially shrinking failure budgets
give a single logarithm. These are approximation-factor statements, not native
machine time/space certificates or Set Cover hardness results.

## Main results

* `fixed_failure`: the actual greedy factor is `O(log² n)` for fixed reliability/target.
* `polynomial_failure`: the factor is `O(log n)` for a polynomial failure-budget window.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.PartialCover.Asymptotics
open Instance Cslib.Algorithms.Lean.Multicover Filter

/-- The factor already proved for the executable greedy batch against every
risk-feasible benchmark; `δ` is the source's `1-η`. -/
@[expose] def factor (q δ : ℝ) (n : ℕ) : ℝ :=
  (1 + Real.log (n * repetitions q (δ / n))) *
    repeatFactor (repetitions q δ) (repetitions q (δ / n))

private theorem threshold_bounds {q δ : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (hδone : δ < 1) :
    0 < repetitions q δ ∧
      Real.log (1 / δ) / Real.log (1 / q) ≤ repetitions q δ ∧
      (repetitions q δ : ℝ) ≤ Real.log (1 / δ) / Real.log (1 / q) + 1 := by
  have hqlog : 0 < Real.log (1 / q) := Real.log_pos ((one_lt_div hq).mpr hqone)
  have hδlog : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ).mpr hδone)
  have hpos := div_pos hδlog hqlog
  unfold repetitions
  exact ⟨Nat.ceil_pos.mpr hpos, Nat.le_ceil _, (Nat.ceil_lt_add_one hpos.le).le⟩

private theorem repeatFactor_le {s r m : ℕ} (hs : 0 < s) (h : r ≤ m * s) :
    repeatFactor s r ≤ m := by
  rw [repeatFactor, Nat.div_le_iff_le_mul hs]
  omega

private theorem factor_le {q δ : ℝ} {n m : ℕ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (hδone : δ < 1) (hn : 2 ≤ n)
    (hm : repetitions q (δ / n) ≤ m * repetitions q δ) :
    factor q δ n ≤ (1 + Real.log n + repetitions q (δ / n)) * m := by
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < δ / n := div_pos hδ (by positivity)
  have hdone : δ / n < 1 := (div_lt_one (by positivity)).mpr (hδone.trans hnreal)
  have hr := (threshold_bounds hq hqone hd hdone).1
  have hs := (threshold_bounds hq hqone hδ hδone).1
  have hrreal : (0 : ℝ) < repetitions q (δ / n) := by exact_mod_cast hr
  have hlog : 1 + Real.log (n * repetitions q (δ / n)) ≤
      1 + Real.log n + repetitions q (δ / n) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hrreal)]
    have := Real.log_le_sub_one_of_pos hrreal
    linarith
  have hnonneg : 0 ≤ 1 + Real.log (n * repetitions q (δ / n)) := by
    have hmul : (1 : ℝ) ≤ n * repetitions q (δ / n) := by
      have : (1 : ℝ) ≤ repetitions q (δ / n) := by exact_mod_cast hr
      nlinarith
    exact add_nonneg zero_le_one (Real.log_nonneg hmul)
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast repeatFactor_le hs hm) hnonneg).trans
    (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg m))

private theorem log_budget {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    Real.log (1 / (δ / n)) = Real.log n + Real.log (1 / δ) := by
  rw [one_div_div, Real.log_div (by positivity) hδ.ne',
    Real.log_div one_ne_zero hδ.ne', Real.log_one]
  ring

private theorem repetitions_le_log {q δ : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (hδone : δ < 1) {n : ℕ} (hn : 2 ≤ n) :
    (repetitions q (δ / n) : ℝ) ≤
      (1 / Real.log (1 / q) +
        (Real.log (1 / δ) / Real.log (1 / q) + 1) / Real.log 2) * Real.log n := by
  have hnpos : 0 < n := by omega
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log (1 / q) := Real.log_pos ((one_lt_div hq).mpr hqone)
  have hdlog : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ).mpr hδone)
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hu := (threshold_bounds hq hqone (div_pos hδ (by positivity))
    ((div_lt_one (by positivity)).mpr (hδone.trans hnreal))).2.2
  rw [log_budget hδ hnpos] at hu
  have hscale := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ (Real.log (1 / δ) / Real.log (1 / q) + 1) / Real.log 2 by positivity)
  rw [div_mul_cancel₀ _ hL.ne'] at hscale
  calc
    _ ≤ Real.log n / Real.log (1 / q) +
        (Real.log (1 / δ) / Real.log (1 / q) + 1) / Real.log 2 * Real.log n := by
      rw [add_div] at hu
      linarith
    _ = _ := by ring

private theorem factor_nonneg {q δ : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (hδone : δ < 1) {n : ℕ} (hn : 2 ≤ n) : 0 ≤ factor q δ n := by
  unfold factor
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hrpos := (threshold_bounds hq hqone (div_pos hδ (by positivity))
    ((div_lt_one (by positivity)).mpr (hδone.trans hnreal))).1
  have hmul : (1 : ℝ) ≤ n * repetitions q (δ / n) := by
    have : (1 : ℝ) ≤ repetitions q (δ / n) := by exact_mod_cast hrpos
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  exact mul_nonneg (add_nonneg zero_le_one (Real.log_nonneg hmul)) (Nat.cast_nonneg _)

/-- A fixed source failure budget gives the stated squared-logarithmic factor.
The constants may depend on the fixed oracle reliability and success target. -/
theorem fixed_failure {q δ : ℝ} (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (hδone : δ < 1) :
    (fun n : ℕ => factor q δ n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
  let K := 1 / Real.log (1 / q) +
    (Real.log (1 / δ) / Real.log (1 / q) + 1) / Real.log 2
  have hc : 0 < Real.log (1 / q) := Real.log_pos ((one_lt_div hq).mpr hqone)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdlog : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ).mpr hδone)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply _root_.Asymptotics.IsBigO.of_bound ((1 / Real.log 2 + 1 + K) * K)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hl : 0 ≤ Real.log n := hL.le.trans hlog
  have hr := repetitions_le_log hq hqone hδ hδone hn
  change (repetitions q (δ / n) : ℝ) ≤ K * Real.log n at hr
  have hs := (threshold_bounds hq hqone hδ hδone).1
  have hf := factor_le hq hqone hδ hδone hn
    (Nat.le_mul_of_pos_right (repetitions q (δ / n)) hs)
  have hfirst : 1 + Real.log n + repetitions q (δ / n) ≤
      (1 / Real.log 2 + 1 + K) * Real.log n := by
    have hscale : 1 ≤ Real.log n / Real.log 2 :=
      (le_div_iff₀ hL).mpr (by simpa using hlog)
    have hone : 1 ≤ (1 / Real.log 2) * Real.log n := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hscale
    nlinarith
  have hnonneg := factor_nonneg hq hqone hδ hδone hn
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (1 + Real.log n + repetitions q (δ / n)) * repetitions q (δ / n) := hf
    _ ≤ ((1 / Real.log 2 + 1 + K) * Real.log n) * (K * Real.log n) := by
      exact mul_le_mul hfirst hr (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- The source's polynomially shrinking failure regime. The window is stated
on `log (1/δ n)`: fixed positive multiples of `log n`, equivalently
`δ n = n^(-Θ(1))`. No repetition-ratio or approximation conclusion is assumed. -/
theorem polynomial_failure {q : ℝ} (hq : 0 < q) (hqone : q < 1)
    (δ : ℕ → ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hδ : ∀ᶠ n in atTop, 0 < δ n ∧ δ n < 1 ∧
      A * Real.log n ≤ Real.log (1 / δ n) ∧ Real.log (1 / δ n) ≤ B * Real.log n) :
    (fun n => factor q (δ n) n) =O[atTop] (fun n => Real.log n) := by
  let c := Real.log (1 / q)
  let K := (1 + B) / c + 1 / Real.log 2
  let m := ⌈K * c / A⌉₊
  have hc : 0 < c := Real.log_pos ((one_lt_div hq).mpr hqone)
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm : K * c / A ≤ (m : ℝ) := Nat.le_ceil _
  apply _root_.Asymptotics.IsBigO.of_bound ((1 / Real.log 2 + 1 + K) * m)
  filter_upwards [hδ, eventually_ge_atTop 2] with n hd hn
  obtain ⟨hd, hdone, hlo, hhi⟩ := hd
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hl : 0 ≤ Real.log n := hL.le.trans hlog
  have hone : 1 ≤ (1 / Real.log 2) * Real.log n := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      ((le_div_iff₀ hL).mpr (by simpa using hlog) : (1 : ℝ) ≤ Real.log n / Real.log 2)
  have hu := (threshold_bounds hq hqone (div_pos hd (by positivity))
    ((div_lt_one (by positivity)).mpr (hdone.trans hnreal))).2.2
  rw [log_budget hd (by omega)] at hu
  have hr : (repetitions q (δ n / n) : ℝ) ≤ K * Real.log n := by
    have hdiv := (div_le_div_iff_of_pos_right hc).mpr hhi
    change Real.log (1 / δ n) / c ≤ _ at hdiv
    change repetitions q (δ n / n) ≤ (Real.log n + Real.log (1 / δ n)) / c + 1 at hu
    rw [add_div] at hu
    calc
      _ ≤ Real.log n / c + (B * Real.log n) / c + 1 := by linarith
      _ ≤ Real.log n / c + (B * Real.log n) / c +
          (1 / Real.log 2) * Real.log n := add_le_add_right hone _
      _ = _ := by dsimp only [K]; ring
  have hs := (threshold_bounds hq hqone hd hdone).2.1
  have hlower : A * Real.log n / c ≤ repetitions q (δ n) :=
    ((div_le_div_iff_of_pos_right hc).mpr hlo).trans hs
  have hratio : K * Real.log n ≤ (m : ℝ) * repetitions q (δ n) := by
    have hm' : K * c ≤ (m : ℝ) * A := (div_le_iff₀ hA).mp hm
    have hmc : K ≤ (m : ℝ) * A / c := (le_div_iff₀ hc).mpr hm'
    calc
      _ ≤ ((m : ℝ) * A / c) * Real.log n := mul_le_mul_of_nonneg_right hmc hl
      _ = (m : ℝ) * (A * Real.log n / c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg m)
  have hrnat : repetitions q (δ n / n) ≤ m * repetitions q (δ n) := by
    exact_mod_cast hr.trans hratio
  have hf := factor_le hq hqone hd hdone hn hrnat
  have hfirst : 1 + Real.log n + repetitions q (δ n / n) ≤
      (1 / Real.log 2 + 1 + K) * Real.log n := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (factor_nonneg hq hqone hd hdone hn),
    Real.norm_eq_abs, abs_of_nonneg hl]
  calc
    _ ≤ (1 + Real.log n + repetitions q (δ n / n)) * m := hf
    _ ≤ ((1 / Real.log 2 + 1 + K) * Real.log n) * m :=
      mul_le_mul_of_nonneg_right hfirst (Nat.cast_nonneg m)
    _ = _ := by ring

end Cslib.Probability.StochasticOracle.PartialCover.Asymptotics
