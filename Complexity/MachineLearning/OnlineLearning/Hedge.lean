/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.OnlineLearning.MultiplicativeUpdate
public import Mathlib.Analysis.SpecialFunctions.Exp
import Complexity.Foundations.Analysis.SpecialFunctions.ExpLogQuadratic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The Hedge algorithm

The *Hedge* algorithm of Freund and Schapire [FreundSchapire1997] with learning rate `η`
multiplies the weight of an expert with loss `x` by `exp (-η x)` (`hedgeFactor`)
[AroraHazanKale2012, §2.1, (2.6)]. For losses in `[-1, 1]` and `0 < η ≤ 1`, its total expected
loss exceeds the total loss of every expert `i` by at most `η ∑ t, ⟨p t, ℓ t ^ 2⟩ + ln n / η`
(`hedge_regret_le`, [AroraHazanKale2012, Theorem 2.3]). Here the second-order term is the
learner's expected squared loss, not the expert's.

[AroraHazanKale2012] states Theorem 2.3 without proof, indicating only that the analysis follows
that of Theorem 2.1 with the estimate `exp (-η x) ≤ 1 - η x + η ^ 2 x ^ 2` for `|η x| ≤ 1`. The
proof here is that argument, carried out from the potential inequality `sum_log_le_log_card_add`.
The factor of expert `i` contributes exactly `-η ℓ t i` to the logarithm. The expected update
factor is at most `1 - η ⟨p t, ℓ t⟩ + η ^ 2 ⟨p t, ℓ t ^ 2⟩` by
`Real.exp_neg_le_one_sub_add_sq` (which needs only `η x ≥ -1`), and `log (1 + x) ≤ x`. The
hypothesis is thus one-sided (`hedge_regret_le_of_neg_one_le`).

Since the learner's expected squared loss is at most `1` for losses in `[-1, 1]`, the learning
rate `η = √(ln n / T)` gives regret at most `2 √(T ln n)` once `T ≥ ln n`
(`hedge_regret_le_sqrt`), by the balancing identity `sqrt_div_mul_add_div_sqrt_div`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.hedgeFactor`: the update factor `exp (-η x)`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.hedge_regret_le_of_neg_one_le`: the regret bound
  for losses with `η ℓ ≥ -1`.
* `Cslib.MachineLearning.OnlineLearning.Experts.hedge_regret_le`:
  [AroraHazanKale2012, Theorem 2.3].
* `Cslib.MachineLearning.OnlineLearning.Experts.hedge_regret_le_sqrt`: regret `2 √(T ln n)` with
  the tuned learning rate.

## References

* [S. Arora, E. Hazan, S. Kale, *The Multiplicative Weights Update Method: a Meta-Algorithm and
  Applications*][AroraHazanKale2012]
* [Y. Freund, R. E. Schapire, *A decision-theoretic generalization of on-line learning and an
  application to boosting*][FreundSchapire1997]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real

variable {ι : Type*} [Fintype ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}

/-- The update factor `exp (-η x)` of the Hedge algorithm with learning rate `η`
[AroraHazanKale2012, (2.6)]. -/
noncomputable def hedgeFactor (η x : ℝ) : ℝ := exp (-(η * x))

@[simp] theorem hedgeFactor_apply (η x : ℝ) : hedgeFactor η x = exp (-(η * x)) := by
  rw [hedgeFactor]

/-- **Regret of Hedge** for losses with `η ℓ ≥ -1`: for `0 < η` and every expert `i`,
`∑ t, ⟨p t, ℓ t⟩ ≤ ∑ t, ℓ t i + η ∑ t, ⟨p t, ℓ t ^ 2⟩ + ln n / η`. -/
theorem hedge_regret_le_of_neg_one_le {η : ℝ} (hη : 0 < η)
    (hℓ : ∀ s < T, ∀ i, -1 ≤ η * ℓ s i) (i : ι) :
    ∑ t ∈ range T, ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j ≤
      ∑ t ∈ range T, ℓ t i + η * ∑ t ∈ range T, ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j ^ 2 +
        log (Fintype.card ι) / η := by
  have : Nonempty ι := ⟨i⟩
  have hφ : ∀ s < T, ∀ j, 0 < hedgeFactor η (ℓ s j) := fun _ _ _ => exp_pos _
  have hmaster := sum_log_le_log_card_add hφ i
  simp only [hedgeFactor_apply, log_exp] at hmaster
  have hup : ∀ t ∈ range T, log (∑ j, prob (hedgeFactor η) ℓ t j * exp (-(η * ℓ t j))) ≤
      -(η * ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j) +
        η ^ 2 * ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j ^ 2 := by
    intro t ht
    have ht' := mem_range.mp ht
    have hφt : ∀ s < t, ∀ j, 0 < hedgeFactor η (ℓ s j) := fun _ _ _ => exp_pos _
    have hpos : 0 < ∑ j, prob (hedgeFactor η) ℓ t j * exp (-(η * ℓ t j)) :=
      sum_prob_mul_pos (φ := hedgeFactor η) fun _ _ _ => exp_pos _
    have hle : ∑ j, prob (hedgeFactor η) ℓ t j * exp (-(η * ℓ t j)) ≤
        ∑ j, prob (hedgeFactor η) ℓ t j * (1 - η * ℓ t j + (η * ℓ t j) ^ 2) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (exp_neg_le_one_sub_add_sq (hℓ t ht' j)) (prob_nonneg hφt j)
    have heq : ∑ j, prob (hedgeFactor η) ℓ t j * (1 - η * ℓ t j + (η * ℓ t j) ^ 2) =
        1 - η * ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j +
          η ^ 2 * ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j ^ 2 := by
      simp only [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, sum_prob hφt,
        mul_sum]
      congr 1
      · congr 1
        exact sum_congr rfl fun j _ => by ring
      · exact sum_congr rfl fun j _ => by ring
    linarith [log_le_sub_one_of_pos hpos]
  have hup' := sum_le_sum hup
  rw [sum_add_distrib, sum_neg_distrib, ← mul_sum, ← mul_sum] at hup'
  have hlhs : ∑ s ∈ range T, -(η * ℓ s i) = -(η * ∑ t ∈ range T, ℓ t i) := by
    rw [sum_neg_distrib, mul_sum]
  rw [hlhs] at hmaster
  have key : η * ∑ t ∈ range T, ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j ≤
      η * (∑ t ∈ range T, ℓ t i + η * ∑ t ∈ range T, ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j ^ 2 +
        log (Fintype.card ι) / η) := by
    rw [mul_add, mul_add, mul_div_cancel₀ _ hη.ne']
    nlinarith
  exact le_of_mul_le_mul_left key hη

/-- **Regret of Hedge** [AroraHazanKale2012, Theorem 2.3]: for losses in `[-1, 1]` and
`0 < η ≤ 1`, for every expert `i`,
`∑ t, ⟨p t, ℓ t⟩ ≤ ∑ t, ℓ t i + η ∑ t, ⟨p t, ℓ t ^ 2⟩ + ln n / η`. -/
theorem hedge_regret_le {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1) (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1)
    (i : ι) :
    ∑ t ∈ range T, ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j ≤
      ∑ t ∈ range T, ℓ t i + η * ∑ t ∈ range T, ∑ j, prob (hedgeFactor η) ℓ t j * ℓ t j ^ 2 +
        log (Fintype.card ι) / η :=
  hedge_regret_le_of_neg_one_le hη (fun s hs j => by
    have h := (abs_le.mp (hℓ s hs j)).1
    nlinarith) i

/-- **Tuned regret of Hedge**: for `n ≥ 2` experts, losses in `[-1, 1]` and `T ≥ ln n` rounds,
Hedge with learning rate `η = √(ln n / T)` has regret at most `2 √(T ln n)` against every expert.
The condition `T ≥ ln n` is `η ≤ 1`, and the learner's expected squared loss is at most `1` in
every round. -/
theorem hedge_regret_le_sqrt (hn : 2 ≤ Fintype.card ι) (hT : log (Fintype.card ι) ≤ T)
    (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1) (i : ι) :
    ∑ t ∈ range T, ∑ j, prob (hedgeFactor √(log (Fintype.card ι) / T)) ℓ t j * ℓ t j ≤
      ∑ t ∈ range T, ℓ t i + 2 * √(T * log (Fintype.card ι)) := by
  have : Nonempty ι := ⟨i⟩
  set L := log (Fintype.card ι) with hLdef
  have hL : 0 < L := log_pos (by exact_mod_cast hn)
  have hT0 : (0 : ℝ) < T := by linarith
  have hη : 0 < √(L / T) := sqrt_pos.mpr (div_pos hL hT0)
  have hη' : √(L / T) ≤ 1 :=
    calc √(L / T) ≤ √1 := sqrt_le_sqrt (by rw [div_le_one hT0]; exact hT)
      _ = 1 := sqrt_one
  refine (hedge_regret_le hη hη' hℓ i).trans ?_
  have hsq : ∑ t ∈ range T, ∑ j, prob (hedgeFactor √(L / T)) ℓ t j * ℓ t j ^ 2 ≤ T := by
    calc ∑ t ∈ range T, ∑ j, prob (hedgeFactor √(L / T)) ℓ t j * ℓ t j ^ 2
        ≤ ∑ t ∈ range T, (1 : ℝ) := sum_le_sum fun t ht => by
          have hφ : ∀ s < t, ∀ j, 0 < hedgeFactor √(L / T) (ℓ s j) := fun _ _ _ => exp_pos _
          calc ∑ j, prob (hedgeFactor √(L / T)) ℓ t j * ℓ t j ^ 2
              ≤ ∑ j, prob (hedgeFactor √(L / T)) ℓ t j := sum_le_sum fun j _ => by
                have h := hℓ t (mem_range.mp ht) j
                have h2 : ℓ t j ^ 2 ≤ 1 := by
                  rw [← sq_abs]
                  nlinarith [abs_nonneg (ℓ t j)]
                exact mul_le_of_le_one_right (prob_nonneg hφ j) h2
            _ = 1 := sum_prob hφ
      _ = T := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [← sqrt_div_mul_add_div_sqrt_div hL hT0]
  nlinarith [mul_le_mul_of_nonneg_left hsq hη.le]

end Cslib.MachineLearning.OnlineLearning.Experts
