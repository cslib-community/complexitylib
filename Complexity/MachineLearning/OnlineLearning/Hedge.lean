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

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.hedgeFactor`: the update factor `exp (-η x)`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.hedge_regret_le_of_neg_one_le`: the regret bound for
  losses with `η ℓ ≥ -1`.
* `Cslib.MachineLearning.OnlineLearning.hedge_regret_le`: [AroraHazanKale2012, Theorem 2.3].

## References

* [S. Arora, E. Hazan, S. Kale, *The Multiplicative Weights Update Method: a Meta-Algorithm and
  Applications*][AroraHazanKale2012]
* [Y. Freund, R. E. Schapire, *A decision-theoretic generalization of on-line learning and an
  application to boosting*][FreundSchapire1997]
-/

@[expose] public section

namespace Cslib.MachineLearning.OnlineLearning

open Finset Real

variable {ι : Type*} [Fintype ι] {ℓ : ℕ → ι → ℝ} {T : ℕ}

/-- The update factor `exp (-η x)` of the Hedge algorithm with learning rate `η`
[AroraHazanKale2012, (2.6)]. -/
noncomputable def hedgeFactor (η x : ℝ) : ℝ := exp (-(η * x))

@[simp] theorem hedgeFactor_apply (η x : ℝ) : hedgeFactor η x = exp (-(η * x)) := rfl

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

end Cslib.MachineLearning.OnlineLearning
