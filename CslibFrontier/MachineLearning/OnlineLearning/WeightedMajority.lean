/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MultiplicativeWeights
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpLogQuadratic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The weighted majority algorithm

In *prediction from expert advice* [LittlestoneWarmuth1994], [AroraHazanKale2012, §1.1], each
round `t` the experts `ι` give binary advice `advice t i`, the learner predicts a bit, and then the
outcome `outcome t` is revealed. The *weighted majority* algorithm with parameter `η` keeps a
weight for each expert, starting at `1` and multiplied by `1 - η` whenever the expert errs
[AroraHazanKale2012, (1.1)]. It predicts the bit advised by the larger total weight. These are the
multiplicative weights for the losses `expertLoss`, `1` for a wrong expert and `0` otherwise, so
the weight of expert `i` in round `t` is `(1 - η) ^ mᵢ(t)`, where `mᵢ(t)` counts its mistakes
(`weight_mwFactor_expertLoss`).

For `0 < η ≤ 1 / 2`, the number of mistakes `M(T)` of weighted majority, with ties broken
arbitrarily, satisfies `M(T) ≤ 2 (1 + η) mᵢ(T) + 2 ln n / η` for every expert `i` (`wm_mistakes_le`,
[AroraHazanKale2012, Theorem 1.1]). Tie-breaking is a hypothesis on the predictions (the advice they
reject never outweighs the advice they follow), so the theorem covers every tie-breaking rule. The
rule `weightedMajority`, which breaks ties towards `true`, satisfies it
(`weightedMajority_mistakes_le`).

The proof is that of [AroraHazanKale2012]: in a round with a mistake, the experts that agreed with
the prediction were wrong and carry at least half of the weight, so the learner's expected loss is
at least `1 / 2` and the potential shrinks by the factor `1 - η / 2`. It is phrased through the
potential inequality `sum_log_le_log_card_add`, with `-ln (1 - η) ≤ η + η ^ 2`
(`Real.neg_sub_sq_le_log_one_sub`).

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.expertLoss`: the mistake indicator of an expert.
* `Cslib.MachineLearning.OnlineLearning.Experts.weightedMajority`: the weighted majority prediction.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.weight_mwFactor_expertLoss`: the weights are
  `(1 - η) ^ mᵢ(t)`.
* `Cslib.MachineLearning.OnlineLearning.Experts.wm_mistakes_le`: [AroraHazanKale2012, Theorem 1.1],
  for any tie-breaking.
* `Cslib.MachineLearning.OnlineLearning.Experts.weightedMajority_mistakes_le`: the same bound for
  `weightedMajority`.

## References

* [N. Littlestone, M. K. Warmuth, *The weighted majority algorithm*][LittlestoneWarmuth1994]
* [S. Arora, E. Hazan, S. Kale, *The Multiplicative Weights Update Method: a Meta-Algorithm and
  Applications*][AroraHazanKale2012]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real

variable {ι : Type*} [Fintype ι] {T : ℕ}

section

variable (advice : ℕ → ι → Bool) (outcome : ℕ → Bool)

/-- The loss of expert `i` in round `t`: `1` if its advice is wrong, `0` otherwise. -/
noncomputable def expertLoss (t : ℕ) (i : ι) : ℝ := if advice t i ≠ outcome t then 1 else 0

/-- The weighted majority prediction in round `t`: the bit advised by the larger total weight,
with ties broken towards `true`. -/
noncomputable def weightedMajority (η : ℝ) (t : ℕ) : Bool :=
  decide (∑ i with advice t i = false, weight (mwFactor η) (expertLoss advice outcome) t i ≤
    ∑ i with advice t i = true, weight (mwFactor η) (expertLoss advice outcome) t i)

omit [Fintype ι] in
/-- The weight of expert `i` in round `t` is `(1 - η) ^ mᵢ(t)`, where `mᵢ(t)` is the number of its
mistakes before round `t` [AroraHazanKale2012, (1.1)]. -/
theorem weight_mwFactor_expertLoss (η : ℝ) (t : ℕ) (i : ι) :
    weight (mwFactor η) (expertLoss advice outcome) t i =
      (1 - η) ^ #{s ∈ range t | advice s i ≠ outcome s} := by
  have h : ∀ s, mwFactor η (expertLoss advice outcome s i) =
      if advice s i ≠ outcome s then 1 - η else 1 := fun s => by
    simp only [mwFactor_apply, expertLoss]
    split_ifs <;> ring
  simp only [weight, h, prod_ite, prod_const_one, mul_one, prod_const]

end

variable {advice : ℕ → ι → Bool} {outcome : ℕ → Bool}

/-- **The weighted majority algorithm** [AroraHazanKale2012, Theorem 1.1]: let `0 < η ≤ 1 / 2`,
and let `pred` be weighted majority predictions with arbitrary tie-breaking, that is, in each round
`t < T` the weight of the experts advising against `pred t` is at most that of the experts advising
`pred t`. Then for every expert `i`, the number of mistakes is
`M(T) ≤ 2 (1 + η) mᵢ(T) + 2 ln n / η`. -/
theorem wm_mistakes_le {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) (pred : ℕ → Bool)
    (hpred : ∀ t < T,
      ∑ i with advice t i ≠ pred t, weight (mwFactor η) (expertLoss advice outcome) t i ≤
        ∑ i with advice t i = pred t, weight (mwFactor η) (expertLoss advice outcome) t i)
    (i : ι) :
    (#{t ∈ range T | pred t ≠ outcome t} : ℝ) ≤
      2 * (1 + η) * #{t ∈ range T | advice t i ≠ outcome t} + 2 * log (Fintype.card ι) / η := by
  have : Nonempty ι := ⟨i⟩
  set ℓ := expertLoss advice outcome with hℓdef
  have hℓ01 : ∀ s j, ℓ s j = 0 ∨ ℓ s j = 1 := fun s j => by
    simp only [hℓdef, expertLoss]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hηℓ : ∀ s j, η * ℓ s j ≤ 1 / 2 := fun s j => by
    rcases hℓ01 s j with h | h <;> rw [h] <;> linarith
  have hφ : ∀ s < T, ∀ j, 0 < mwFactor η (ℓ s j) := fun s _ j => by
    rw [mwFactor_apply]; linarith [hηℓ s j]
  have hmaster := sum_log_le_log_card_add hφ i
  -- the factors of expert `i`: `log (1 - η) ≥ -(η + η ^ 2)` per mistake
  have hcount_i : ∑ t ∈ range T, ℓ t i = #{t ∈ range T | advice t i ≠ outcome t} := by
    simp only [hℓdef, expertLoss]
    rw [sum_boole]
  have hlow : -((η + η ^ 2) * ∑ t ∈ range T, ℓ t i) ≤
      ∑ t ∈ range T, log (mwFactor η (ℓ t i)) := by
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun t _ => ?_
    rw [mwFactor_apply]
    have h := neg_sub_sq_le_log_one_sub (hηℓ t i)
    rcases hℓ01 t i with h0 | h0 <;> rw [h0] at h ⊢ <;> nlinarith
  -- in a round with a mistake, the learner's expected loss is at least `1 / 2`
  have hhalf : ∀ t < T, pred t ≠ outcome t →
      1 / 2 ≤ ∑ j, prob (mwFactor η) ℓ t j * ℓ t j := by
    intro t ht hne
    have hφt : ∀ s < t, ∀ j, 0 < mwFactor η (ℓ s j) := fun s hs => hφ s (by omega)
    have hΦ := potential_pos hφt
    have hsplit := sum_filter_add_sum_filter_not univ (fun j => advice t j = pred t)
      (weight (mwFactor η) ℓ t)
    have hfilt : ∑ j, prob (mwFactor η) ℓ t j * ℓ t j =
        (∑ j with advice t j = pred t, weight (mwFactor η) ℓ t j) / potential (mwFactor η) ℓ t := by
      rw [sum_filter, sum_div]
      refine sum_congr rfl fun j _ => ?_
      simp only [prob, hℓdef, expertLoss]
      have hb : (advice t j ≠ outcome t) ↔ advice t j = pred t := by
        revert hne; cases advice t j <;> cases pred t <;> cases outcome t <;> simp
      by_cases h : advice t j = pred t
      · simp only [h, ne_eq, hne, not_false_eq_true, ite_true, mul_one]
      · have h' : ¬ advice t j ≠ outcome t := fun h' => h (hb.mp h')
        simp only [h', h, ite_false, mul_zero, zero_div]
    rw [hfilt, le_div_iff₀ hΦ]
    have := hpred t ht
    simp only [ne_eq] at this
    unfold potential
    linarith
  -- so the potential shrinks by `1 - η / 2` in every round with a mistake
  have hup : ∑ t ∈ range T, log (∑ j, prob (mwFactor η) ℓ t j * mwFactor η (ℓ t j)) ≤
      -(η / 2 * #{t ∈ range T | pred t ≠ outcome t}) := by
    rw [← sum_boole, mul_sum, ← sum_neg_distrib]
    refine sum_le_sum fun t ht => ?_
    have ht' := mem_range.mp ht
    have hφt : ∀ s < t, ∀ j, 0 < mwFactor η (ℓ s j) := fun s hs => hφ s (by omega)
    have hpos := sum_prob_mul_pos (φ := mwFactor η) (ℓ := ℓ) (t := t)
      fun s hs => hφ s (by omega)
    rw [sum_prob_mul_mwFactor hφt] at hpos ⊢
    have hlog := log_le_sub_one_of_pos hpos
    have hnn : 0 ≤ ∑ j, prob (mwFactor η) ℓ t j * ℓ t j :=
      sum_nonneg fun j _ => mul_nonneg (prob_nonneg hφt j)
        (by rcases hℓ01 t j with h | h <;> simp only [h, le_refl, zero_le_one])
    split_ifs with hm
    · have := hhalf t ht' hm
      nlinarith
    · nlinarith
  rw [hcount_i] at hlow
  have key : η * (#{t ∈ range T | pred t ≠ outcome t} : ℝ) ≤
      η * (2 * (1 + η) * #{t ∈ range T | advice t i ≠ outcome t} +
        2 * log (Fintype.card ι) / η) := by
    rw [mul_add, mul_div_assoc', mul_comm η (2 * log _), mul_div_assoc, div_self hη.ne', mul_one]
    nlinarith
  exact le_of_mul_le_mul_left key hη

/-- `weightedMajority` follows the advice of the larger total weight. -/
theorem weightedMajority_spec (η : ℝ) (t : ℕ) :
    ∑ i with advice t i ≠ weightedMajority advice outcome η t,
        weight (mwFactor η) (expertLoss advice outcome) t i ≤
      ∑ i with advice t i = weightedMajority advice outcome η t,
        weight (mwFactor η) (expertLoss advice outcome) t i := by
  unfold weightedMajority
  by_cases h : ∑ i with advice t i = false, weight (mwFactor η) (expertLoss advice outcome) t i ≤
      ∑ i with advice t i = true, weight (mwFactor η) (expertLoss advice outcome) t i
  · rw [decide_eq_true h]
    simpa only [ne_eq, Bool.not_eq_true] using h
  · rw [decide_eq_false h]
    simp only [ne_eq, Bool.not_eq_false]
    exact (not_le.mp h).le

/-- **The weighted majority algorithm** [AroraHazanKale2012, Theorem 1.1], for the rule
`weightedMajority`: for `0 < η ≤ 1 / 2` and every expert `i`,
`M(T) ≤ 2 (1 + η) mᵢ(T) + 2 ln n / η`. -/
theorem weightedMajority_mistakes_le {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 2) (i : ι) :
    (#{t ∈ range T | weightedMajority advice outcome η t ≠ outcome t} : ℝ) ≤
      2 * (1 + η) * #{t ∈ range T | advice t i ≠ outcome t} + 2 * log (Fintype.card ι) / η :=
  wm_mistakes_le hη hη' _ (fun t _ => weightedMajority_spec η t) i

end Cslib.MachineLearning.OnlineLearning.Experts
