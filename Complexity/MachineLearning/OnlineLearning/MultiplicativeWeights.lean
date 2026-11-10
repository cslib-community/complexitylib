/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.OnlineLearning.MultiplicativeUpdate
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Complexity.Foundations.Analysis.SpecialFunctions.ExpLogQuadratic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# The multiplicative weights algorithm

The *multiplicative weights* (MW) algorithm with learning rate `η` multiplies the weight of an
expert with loss `x` by `1 - η x` (`mwFactor`) [AroraHazanKale2012, §2, Figure 1]; this is the
*prod* algorithm of Cesa-Bianchi, Mansour and Stoltz [CesaBianchiMansourStoltz2007]. For losses in
`[-1, 1]` and `0 < η ≤ 1 / 2`, its total expected loss exceeds the total loss of every expert `i`
by at most `η ∑ t, |ℓ t i| + ln n / η` (`mw_regret_le`, [AroraHazanKale2012, Theorem 2.1]).
Averaging over a distribution on the experts gives the same bound against mixed strategies
(`mw_regret_le_stdSimplex`, [AroraHazanKale2012, Corollary 2.2]), and with `η = √(ln n / T)` the
regret is at most `2 √(T ln n)` (`mw_regret_le_sqrt`).

The proof combines the potential inequality `sum_log_le_log_card_add` with two estimates. The
expected update factor is `1 - η` times the expected loss, and `log (1 - x) ≤ -x`. For the factor of
expert `i`, `log (1 - y) ≥ -y - y ^ 2` for `y ≤ 1 / 2` (`Real.neg_sub_sq_le_log_one_sub`); this
gives the second-order bound `η ∑ t, ℓ t i ^ 2` in place of `η ∑ t, |ℓ t i|` under the one-sided
hypothesis `η ℓ ≤ 1 / 2` alone (`mw_regret_le_sq`). [AroraHazanKale2012, proof of Theorem 2.1] uses
the two convexity bounds `(1 - η) ^ x ≤ 1 - η x` on `[0, 1]` and `(1 + η) ^ (-x) ≤ 1 - η x` on
`[-1, 0]` instead, followed by the same logarithm estimates at `x = ±1`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.mwFactor`: the update factor `1 - η x`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.mw_regret_le_sq`: the second-order regret bound.
* `Cslib.MachineLearning.OnlineLearning.Experts.mw_regret_le`: [AroraHazanKale2012, Theorem 2.1].
* `Cslib.MachineLearning.OnlineLearning.Experts.mw_regret_le_stdSimplex`:
  [AroraHazanKale2012, Corollary 2.2].
* `Cslib.MachineLearning.OnlineLearning.Experts.mw_regret_le_sqrt`: regret `2 √(T ln n)` with the
  tuned learning rate.

## References

* [S. Arora, E. Hazan, S. Kale, *The Multiplicative Weights Update Method: a Meta-Algorithm and
  Applications*][AroraHazanKale2012]
* [N. Cesa-Bianchi, Y. Mansour, G. Stoltz, *Improved second-order bounds for prediction with expert
  advice*][CesaBianchiMansourStoltz2007]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real

variable {ι : Type*} [Fintype ι] {ℓ : ℕ → ι → ℝ} {t T : ℕ}

/-- The update factor `1 - η x` of the multiplicative weights algorithm with learning rate `η`
[AroraHazanKale2012, (2.1)]. -/
def mwFactor (η x : ℝ) : ℝ := 1 - η * x

@[simp] theorem mwFactor_apply (η x : ℝ) : mwFactor η x = 1 - η * x := by rw [mwFactor]

/-- The expected MW update factor is `1 - η` times the expected loss. -/
theorem sum_prob_mul_mwFactor [Nonempty ι] {η : ℝ} (hφ : ∀ s < t, ∀ i, 0 < mwFactor η (ℓ s i)) :
    ∑ i, prob (mwFactor η) ℓ t i * mwFactor η (ℓ t i) =
      1 - η * ∑ i, prob (mwFactor η) ℓ t i * ℓ t i := by
  simp only [mwFactor_apply, mul_sub, mul_one, sum_sub_distrib, sum_prob hφ, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ => by ring

/-- **Second-order regret of multiplicative weights**: if `0 < η` and `η ℓ ≤ 1 / 2` for all
losses, then for every expert `i` the total expected loss is at most
`∑ t, ℓ t i + η ∑ t, ℓ t i ^ 2 + ln n / η`. Compare [CesaBianchiMansourStoltz2007] and
[AroraHazanKale2012, Theorem 2.1]. -/
theorem mw_regret_le_sq {η : ℝ} (hη : 0 < η) (hℓ : ∀ s < T, ∀ i, η * ℓ s i ≤ 1 / 2) (i : ι) :
    ∑ t ∈ range T, ∑ j, prob (mwFactor η) ℓ t j * ℓ t j ≤
      ∑ t ∈ range T, ℓ t i + η * ∑ t ∈ range T, ℓ t i ^ 2 + log (Fintype.card ι) / η := by
  have : Nonempty ι := ⟨i⟩
  have hφ : ∀ s < T, ∀ j, 0 < mwFactor η (ℓ s j) := fun s hs j => by
    rw [mwFactor_apply]; linarith [hℓ s hs j]
  have hmaster := sum_log_le_log_card_add hφ i
  have hlow : -(η * ∑ t ∈ range T, ℓ t i) - η ^ 2 * ∑ t ∈ range T, ℓ t i ^ 2 ≤
      ∑ t ∈ range T, log (mwFactor η (ℓ t i)) := by
    calc -(η * ∑ t ∈ range T, ℓ t i) - η ^ 2 * ∑ t ∈ range T, ℓ t i ^ 2
        = ∑ t ∈ range T, (-(η * ℓ t i) - (η * ℓ t i) ^ 2) := by
          simp only [sum_sub_distrib, sum_neg_distrib, mul_sum, mul_pow]
      _ ≤ ∑ t ∈ range T, log (mwFactor η (ℓ t i)) := sum_le_sum fun t ht => by
          rw [mwFactor_apply]
          exact neg_sub_sq_le_log_one_sub (hℓ t (mem_range.mp ht) i)
  have hup : ∑ t ∈ range T, log (∑ j, prob (mwFactor η) ℓ t j * mwFactor η (ℓ t j)) ≤
      -(η * ∑ t ∈ range T, ∑ j, prob (mwFactor η) ℓ t j * ℓ t j) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun t ht => ?_
    have ht' := mem_range.mp ht
    have hpos := sum_prob_mul_pos (φ := mwFactor η) (ℓ := ℓ) (t := t)
      fun s hs => hφ s (by omega)
    rw [sum_prob_mul_mwFactor fun s hs => hφ s (by omega)] at hpos ⊢
    linarith [log_le_sub_one_of_pos hpos]
  have key : η * ∑ t ∈ range T, ∑ j, prob (mwFactor η) ℓ t j * ℓ t j ≤
      η * (∑ t ∈ range T, ℓ t i + η * ∑ t ∈ range T, ℓ t i ^ 2 + log (Fintype.card ι) / η) := by
    rw [mul_add, mul_add, mul_div_cancel₀ _ hη.ne']
    nlinarith
  exact le_of_mul_le_mul_left key hη

/-- **Regret of multiplicative weights** [AroraHazanKale2012, Theorem 2.1]: for losses in
`[-1, 1]` and `0 < η ≤ 1 / 2`, for every expert `i`,
`∑ t, ⟨p t, ℓ t⟩ ≤ ∑ t, ℓ t i + η ∑ t, |ℓ t i| + ln n / η`. -/
theorem mw_regret_le {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1)
    (i : ι) :
    ∑ t ∈ range T, ∑ j, prob (mwFactor η) ℓ t j * ℓ t j ≤
      ∑ t ∈ range T, ℓ t i + η * ∑ t ∈ range T, |ℓ t i| + log (Fintype.card ι) / η := by
  refine (mw_regret_le_sq hη (fun s hs j => ?_) i).trans ?_
  · have h := (abs_le.mp (hℓ s hs j)).2
    nlinarith
  · gcongr with t ht
    have h := hℓ t (mem_range.mp ht) i
    rw [← sq_abs]
    nlinarith [abs_nonneg (ℓ t i)]

/-- **Regret against mixed strategies** [AroraHazanKale2012, Corollary 2.2]: for losses in
`[-1, 1]`, `0 < η ≤ 1 / 2` and every distribution `q` on the experts,
`∑ t, ⟨p t, ℓ t⟩ ≤ ∑ t, ⟨q, ℓ t + η |ℓ t|⟩ + ln n / η`. -/
theorem mw_regret_le_stdSimplex {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2)
    (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1) (q : Convexity.StdSimplex ℝ ι) :
    ∑ t ∈ range T, ∑ j, prob (mwFactor η) ℓ t j * ℓ t j ≤
      ∑ t ∈ range T, ∑ j, q.weights j * (ℓ t j + η * |ℓ t j|) + log (Fintype.card ι) / η := by
  have hq := q.total_of_fintype
  calc ∑ t ∈ range T, ∑ j, prob (mwFactor η) ℓ t j * ℓ t j
      = ∑ i, q.weights i * ∑ t ∈ range T, ∑ j, prob (mwFactor η) ℓ t j * ℓ t j := by
        rw [← sum_mul, hq, one_mul]
    _ ≤ ∑ i, q.weights i * (∑ t ∈ range T, ℓ t i + η * ∑ t ∈ range T, |ℓ t i| +
          log (Fintype.card ι) / η) :=
        sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (mw_regret_le hη hη' hℓ i) (q.weights_nonneg i)
    _ = _ := by
        simp only [mul_add, mul_sum, sum_add_distrib, ← sum_mul, hq, one_mul]
        rw [sum_comm (s := univ), sum_comm (s := univ)]

/-- **Tuned regret of multiplicative weights**: for `n ≥ 2` experts, losses in `[-1, 1]` and
`T ≥ 4 ln n` rounds, MW with learning rate `η = √(ln n / T)` has regret at most `2 √(T ln n)`
against every expert. The condition `T ≥ 4 ln n` is `η ≤ 1 / 2`. -/
theorem mw_regret_le_sqrt (hn : 2 ≤ Fintype.card ι) (hT : 4 * log (Fintype.card ι) ≤ T)
    (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1) (i : ι) :
    ∑ t ∈ range T, ∑ j, prob (mwFactor √(log (Fintype.card ι) / T)) ℓ t j * ℓ t j ≤
      ∑ t ∈ range T, ℓ t i + 2 * √(T * log (Fintype.card ι)) := by
  set L := log (Fintype.card ι) with hLdef
  have hL : 0 < L := log_pos (by exact_mod_cast hn)
  have hT0 : (0 : ℝ) < T := by linarith
  have hη : 0 < √(L / T) := sqrt_pos.mpr (div_pos hL hT0)
  have hη' : √(L / T) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = √(1 / 4) by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by rw [div_le_iff₀ hT0]; linarith)
  refine (mw_regret_le hη hη' hℓ i).trans ?_
  have habs : ∑ t ∈ range T, |ℓ t i| ≤ T := by
    calc ∑ t ∈ range T, |ℓ t i| ≤ ∑ t ∈ range T, (1 : ℝ) :=
          sum_le_sum fun t ht => hℓ t (mem_range.mp ht) i
      _ = T := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [← sqrt_div_mul_add_div_sqrt_div hL hT0]
  nlinarith [mul_le_mul_of_nonneg_left habs hη.le]

end Cslib.MachineLearning.OnlineLearning.Experts
