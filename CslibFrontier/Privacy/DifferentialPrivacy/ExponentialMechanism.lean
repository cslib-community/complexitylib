/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Basic
public import CslibFrontier.Privacy.DifferentialPrivacy.Sensitivity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The exponential mechanism

Fix a finite nonempty range `R` and a utility score `u : D → R → ℝ` whose sensitivity in the
dataset argument is at most `Δ > 0`: `|u x r - u y r| ≤ Δ` for adjacent `x`, `y` and every `r`
(`PointwiseSensitivity Adj u Δ`).
The exponential mechanism outputs `r` with probability proportional to `exp (ε u(x, r) / (2 Δ))`
[DworkRoth2014, Definition 3.4] (`exponentialMechanism`). It is `(ε, 0)`-differentially private
[DworkRoth2014, Theorem 3.10] (`differentiallyPrivate_exponentialMechanism`).

Its utility guarantee compares the utility of the output with the optimum
`OPT = max_r u(x, r)`: for every `t`, the output has utility at most
`OPT - (2 Δ / ε) (ln (|R| / |R_OPT|) + t)` with probability at most `exp (-t)`, where `R_OPT` is the
set of optimal outputs [DworkRoth2014, Theorem 3.11]
(`exponentialMechanism_toOuterMeasure_utility_le_opt_sub`); replacing `|R| / |R_OPT|` by `|R|`
gives [DworkRoth2014, Corollary 3.12]. Both follow from the bound
`Pr[u(x, M x) ≤ c] ≤ |R| / |R_OPT| · exp (ε (c - OPT) / (2 Δ))`
(`exponentialMechanism_toOuterMeasure_utility_le`).

The range must not depend on the dataset; it is the type `R`. The mechanism is stated through
its output law; the cost of sampling it is not modelled.

## Main definitions

* `Cslib.Privacy.exponentialMechanism`: the exponential mechanism.

## Main results

* `Cslib.Privacy.differentiallyPrivate_exponentialMechanism`: `(ε, 0)`-privacy.
* `Cslib.Privacy.exponentialMechanism_toOuterMeasure_utility_le_opt_sub`: Theorem 3.11.
* `Cslib.Privacy.exponentialMechanism_toOuterMeasure_utility_le_opt_sub_log_card`:
  Corollary 3.12.

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

variable {D R : Type*} [Fintype R] [Nonempty R]

/-- The exponential mechanism with privacy parameter `ε` for a utility score `u` of sensitivity
`Δ`: on dataset `x` it outputs `r` with probability proportional to `exp (ε u(x, r) / (2 Δ))`
[DworkRoth2014, Definition 3.4]. -/
noncomputable def exponentialMechanism (u : D → R → ℝ) (Δ ε : ℝ) (x : D) : PMF R :=
  PMF.ofFintype
    (fun r => ENNReal.ofReal (Real.exp (ε * u x r / (2 * Δ)) /
      ∑ r', Real.exp (ε * u x r' / (2 * Δ)))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => div_nonneg (Real.exp_pos _).le
        (Finset.sum_nonneg fun r' _ => (Real.exp_pos _).le)), ← Finset.sum_div,
      div_self (Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty).ne',
      ENNReal.ofReal_one])

/-- The probability that the exponential mechanism outputs `r`. -/
theorem exponentialMechanism_apply (u : D → R → ℝ) (Δ ε : ℝ) (x : D) (r : R) :
    exponentialMechanism u Δ ε x r =
      ENNReal.ofReal (Real.exp (ε * u x r / (2 * Δ)) /
        ∑ r', Real.exp (ε * u x r' / (2 * Δ))) := by
  rfl

private theorem exp_le_exp_half_mul_exp {Δ ε a b : ℝ} (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    (hab : a - b ≤ Δ) :
    Real.exp (ε * a / (2 * Δ)) ≤ Real.exp (ε / 2) * Real.exp (ε * b / (2 * Δ)) := by
  rw [← Real.exp_add, Real.exp_le_exp, div_add_div _ _ (by norm_num) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hab hε]

/-- The exponential mechanism is `(ε, 0)`-differentially private for every `ε ≥ 0` when the
utility score has sensitivity at most `Δ > 0` [DworkRoth2014, Theorem 3.10]. -/
theorem differentiallyPrivate_exponentialMechanism {Adj : D → D → Prop} {u : D → R → ℝ}
    {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 ≤ ε) (hu : PointwiseSensitivity Adj u Δ) :
    DifferentiallyPrivate Adj (exponentialMechanism u Δ ε) ε 0 := by
  refine DifferentiallyPrivate.of_apply_le fun x y hxy r => ?_
  rw [exponentialMechanism_apply, exponentialMechanism_apply,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  set Zx := ∑ r', Real.exp (ε * u x r' / (2 * Δ))
  set Zy := ∑ r', Real.exp (ε * u y r' / (2 * Δ))
  have hZx : 0 < Zx := Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
  have hZy : 0 < Zy := Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
  have hw : Real.exp (ε * u x r / (2 * Δ)) ≤ Real.exp (ε / 2) * Real.exp (ε * u y r / (2 * Δ)) :=
    exp_le_exp_half_mul_exp hΔ hε (le_of_abs_le (hu hxy r))
  have hZ : Zy ≤ Real.exp (ε / 2) * Zx := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r' _ => exp_le_exp_half_mul_exp hΔ hε ?_
    have := hu hxy r'
    rw [abs_le] at this
    linarith
  have hεsplit : Real.exp ε = Real.exp (ε / 2) * Real.exp (ε / 2) := by
    rw [← Real.exp_add, add_halves]
  rw [div_le_iff₀ hZx, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hZy, hεsplit]
  calc Real.exp (ε * u x r / (2 * Δ)) * Zy
      ≤ (Real.exp (ε / 2) * Real.exp (ε * u y r / (2 * Δ))) * (Real.exp (ε / 2) * Zx) :=
        mul_le_mul hw hZ hZy.le (by positivity)
    _ = Real.exp (ε / 2) * Real.exp (ε / 2) * Real.exp (ε * u y r / (2 * Δ)) * Zx := by ring

/-- The optimal utility `OPT_u(x) = max_r u(x, r)`. -/
noncomputable def optUtility (u : D → R → ℝ) (x : D) : ℝ :=
  ⨆ r, u x r

omit [Fintype R] [Nonempty R] in
theorem le_optUtility [Finite R] (u : D → R → ℝ) (x : D) (r : R) : u x r ≤ optUtility u x :=
  le_ciSup (Set.finite_range _).bddAbove r

open Classical in
/-- The outputs of optimal utility, `R_OPT = {r | u(x, r) = OPT_u(x)}`; it is nonempty. -/
noncomputable def optSet (u : D → R → ℝ) (x : D) : Finset R :=
  Finset.univ.filter fun r => u x r = optUtility u x

omit [Nonempty R] in
theorem mem_optSet {u : D → R → ℝ} {x : D} {r : R} : r ∈ optSet u x ↔ u x r = optUtility u x := by
  classical simp [optSet]

theorem card_optSet_pos (u : D → R → ℝ) (x : D) : 0 < (optSet u x).card := by
  obtain ⟨r, hr⟩ := exists_eq_ciSup_of_finite (f := u x)
  exact Finset.card_pos.mpr ⟨r, mem_optSet.mpr hr⟩

/-- The probability that the exponential mechanism returns an output of utility at most `c` is at
most `|R| / |R_OPT| · exp (ε (c - OPT) / (2 Δ))`; this is the bound in the proof of
[DworkRoth2014, Theorem 3.11]. -/
theorem exponentialMechanism_toOuterMeasure_utility_le {u : D → R → ℝ} {Δ ε : ℝ} (hΔ : 0 < Δ)
    (hε : 0 ≤ ε) (x : D) (c : ℝ) :
    (exponentialMechanism u Δ ε x).toOuterMeasure {r | u x r ≤ c} ≤
      ENNReal.ofReal (Fintype.card R / (optSet u x).card *
        Real.exp (ε * (c - optUtility u x) / (2 * Δ))) := by
  classical
  set Z := ∑ r', Real.exp (ε * u x r' / (2 * Δ))
  have hZ : 0 < Z := Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
  rw [PMF.toOuterMeasure_apply_fintype]
  have hterm (r : R) : {r | u x r ≤ c}.indicator (exponentialMechanism u Δ ε x) r ≤
      ENNReal.ofReal (Real.exp (ε * c / (2 * Δ)) / Z) := by
    by_cases hr : u x r ≤ c
    · rw [Set.indicator_of_mem (by exact hr), exponentialMechanism_apply]
      refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hZ.le)
      refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ (by positivity))
      exact mul_le_mul_of_nonneg_left hr hε
    · rw [Set.indicator_of_notMem (by exact hr)]
      exact zero_le
  refine (Finset.sum_le_sum fun r _ => hterm r).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hopt : ((optSet u x).card : ℝ) * Real.exp (ε * optUtility u x / (2 * Δ)) ≤ Z := by
    calc ((optSet u x).card : ℝ) * Real.exp (ε * optUtility u x / (2 * Δ))
        = ∑ r ∈ optSet u x, Real.exp (ε * u x r / (2 * Δ)) := by
          rw [Finset.sum_congr rfl fun r hr => by rw [mem_optSet.mp hr], Finset.sum_const,
            nsmul_eq_mul]
      _ ≤ Z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => (Real.exp_pos _).le
  have hcard : (0 : ℝ) < (optSet u x).card := by exact_mod_cast card_optSet_pos u x
  have hsplit : Real.exp (ε * (c - optUtility u x) / (2 * Δ)) =
      Real.exp (ε * c / (2 * Δ)) / Real.exp (ε * optUtility u x / (2 * Δ)) := by
    rw [← Real.exp_sub]
    ring_nf
  rw [hsplit, mul_div_assoc', div_mul_div_comm]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  rw [mul_comm]
  linarith

/-- Utility of the exponential mechanism [DworkRoth2014, Theorem 3.11]: the output has utility at
most `OPT - (2 Δ / ε) (ln (|R| / |R_OPT|) + t)` with probability at most `exp (-t)`. -/
theorem exponentialMechanism_toOuterMeasure_utility_le_opt_sub {u : D → R → ℝ} {Δ ε : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (x : D) (t : ℝ) :
    (exponentialMechanism u Δ ε x).toOuterMeasure
        {r | u x r ≤ optUtility u x -
          2 * Δ / ε * (Real.log (Fintype.card R / (optSet u x).card) + t)} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  refine (exponentialMechanism_toOuterMeasure_utility_le hΔ hε.le x _).trans_eq ?_
  congr 1
  have hcard : (0 : ℝ) < (optSet u x).card := by exact_mod_cast card_optSet_pos u x
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hexp : ε * (optUtility u x - 2 * Δ / ε * (Real.log (Fintype.card R / (optSet u x).card) +
      t) - optUtility u x) / (2 * Δ) = -Real.log (Fintype.card R / (optSet u x).card) + -t := by
    field_simp
    ring
  rw [hexp, Real.exp_add, Real.exp_neg, Real.exp_log (by positivity), ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]

/-- Utility of the exponential mechanism [DworkRoth2014, Corollary 3.12]: the output has utility
at most `OPT - (2 Δ / ε) (ln |R| + t)` with probability at most `exp (-t)`. -/
theorem exponentialMechanism_toOuterMeasure_utility_le_opt_sub_log_card {u : D → R → ℝ}
    {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) (x : D) (t : ℝ) :
    (exponentialMechanism u Δ ε x).toOuterMeasure
        {r | u x r ≤ optUtility u x - 2 * Δ / ε * (Real.log (Fintype.card R) + t)} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  refine le_trans (MeasureTheory.measure_mono fun r hr => ?_)
    (exponentialMechanism_toOuterMeasure_utility_le_opt_sub hΔ hε x t)
  simp only [Set.mem_ofPred_eq] at hr ⊢
  refine hr.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) _)
  have hcard : (1 : ℝ) ≤ (optSet u x).card := by exact_mod_cast card_optSet_pos u x
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  gcongr
  exact div_le_self hR.le hcard

end Cslib.Privacy
