/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Multiplicative updates for learning with experts

A learner chooses among the experts `ι` (a nonempty finite type) in rounds `t = 0, 1, …`. In round
`t` it plays a distribution on `ι`; then the loss vector `ℓ t : ι → ℝ` is revealed and the learner
pays the expected loss `∑ i, prob φ ℓ t i * ℓ t i`. A *multiplicative update* with factor `φ`
gives expert `i` the weight `∏ s < t, φ (ℓ s i)` (`weight`), and plays the weights normalized by
their sum, the *potential* (`potential`, `prob`) [AroraHazanKale2012, §2]. The distribution in
round `t` depends only on the losses of the rounds before `t` (`prob_congr`), so the learner is
online. The factors `1 - η x` (multiplicative weights) and `exp (-η x)` (Hedge) are the instances
studied in the files `MultiplicativeWeights` and `Hedge`.

All bounds below hold for every loss sequence `ℓ`. They therefore cover an adaptive adversary,
whose loss vector in each round depends on the learner's current distribution: such an adversary
`adv` produces the loss sequence `adaptiveLoss φ adv`, which satisfies
`adaptiveLoss φ adv t = adv t (prob φ (adaptiveLoss φ adv) t)` (`adaptiveLoss_eq`).

The analysis rests on one potential inequality (`sum_log_le_log_card_add`): the potential starts
at `n = card ι`, is at least the weight of any single expert, and is multiplied in round `t` by
the expected update factor `∑ i, prob φ ℓ t i * φ (ℓ t i)`. Taking logarithms, for every expert
`i`,
`∑ s < t, log φ (ℓ s i) ≤ log n + ∑ s < t, log (∑ j, prob φ ℓ s j * φ (ℓ s j))`.
This is the argument of [AroraHazanKale2012, proof of Theorem 2.1], stated once for every
positive factor.

The tuned learning rate `η = √(L / T)` balances the two terms `η T + L / η` of the regret bounds
at `2 √(T L)` (`sqrt_div_mul_add_div_sqrt_div`).

The declarations of the experts setting live in the namespace
`Cslib.MachineLearning.OnlineLearning.Experts`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.weight`,
  `Cslib.MachineLearning.OnlineLearning.Experts.potential`,
  `Cslib.MachineLearning.OnlineLearning.Experts.prob`: the weights, their sum and the learner's
  distribution under a multiplicative update.
* `Cslib.MachineLearning.OnlineLearning.Experts.adaptiveLoss`: the losses produced by an adaptive
  adversary against a multiplicative update.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.sum_prob`: the learner plays a distribution.
* `Cslib.MachineLearning.OnlineLearning.Experts.prob_congr`: the distribution in round `t`
  depends only on the losses before round `t`.
* `Cslib.MachineLearning.OnlineLearning.Experts.log_potential`: the potential is `n` times the
  product of the expected update factors.
* `Cslib.MachineLearning.OnlineLearning.Experts.sum_log_le_log_card_add`: the potential
  inequality.
* `Cslib.MachineLearning.OnlineLearning.Experts.adaptiveLoss_eq`: adaptive adversaries.
* `Cslib.MachineLearning.OnlineLearning.Experts.sqrt_div_mul_add_div_sqrt_div`: the tuned
  learning rate.

## References

* [S. Arora, E. Hazan, S. Kale, *The Multiplicative Weights Update Method: a Meta-Algorithm and
  Applications*][AroraHazanKale2012]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real

variable {ι : Type*} [Fintype ι]

/-- The weight of expert `i` in round `t` under the multiplicative update with factor `φ`, against
the losses `ℓ`: the product of the factors `φ (ℓ s i)` of the rounds `s < t`. -/
@[expose] noncomputable def weight (φ : ℝ → ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  ∏ s ∈ range t, φ (ℓ s i)

/-- The potential in round `t`: the total weight of the experts. -/
@[expose] noncomputable def potential (φ : ℝ → ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∑ i, weight φ ℓ t i

/-- The learner's distribution in round `t`: the weights normalized by the potential. -/
@[expose] noncomputable def prob (φ : ℝ → ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  weight φ ℓ t i / potential φ ℓ t

variable {φ : ℝ → ℝ} {ℓ : ℕ → ι → ℝ} {t : ℕ}

omit [Fintype ι] in
/-- Every expert starts with weight `1`. -/
@[simp] theorem weight_zero (φ : ℝ → ℝ) (ℓ : ℕ → ι → ℝ) (i : ι) : weight φ ℓ 0 i = 1 := by
  simp only [weight, range_zero, prod_empty]

omit [Fintype ι] in
/-- The weight is multiplied by the factor of the current loss. -/
theorem weight_succ (φ : ℝ → ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    weight φ ℓ (t + 1) i = weight φ ℓ t i * φ (ℓ t i) :=
  prod_range_succ _ _

/-- The potential starts at the number of experts. -/
@[simp] theorem potential_zero (φ : ℝ → ℝ) (ℓ : ℕ → ι → ℝ) :
    potential φ ℓ 0 = Fintype.card ι := by
  simp only [potential, weight_zero, sum_const, card_univ, nsmul_eq_mul, mul_one]

omit [Fintype ι] in
/-- The weights in round `t` depend only on the losses before round `t`. -/
theorem weight_congr {ℓ' : ℕ → ι → ℝ} (h : ∀ s < t, ℓ s = ℓ' s) :
    weight φ ℓ t = weight φ ℓ' t := by
  funext i
  exact prod_congr rfl fun s hs => by rw [h s (mem_range.mp hs)]

/-- The learner's distribution in round `t` depends only on the losses before round `t`. -/
theorem prob_congr {ℓ' : ℕ → ι → ℝ} (h : ∀ s < t, ℓ s = ℓ' s) : prob φ ℓ t = prob φ ℓ' t := by
  funext i
  simp only [prob, potential, weight_congr h]

omit [Fintype ι] in
/-- With positive factors, every weight is positive. -/
theorem weight_pos (hφ : ∀ s < t, ∀ i, 0 < φ (ℓ s i)) (i : ι) : 0 < weight φ ℓ t i :=
  prod_pos fun s hs => hφ s (mem_range.mp hs) i

/-- With positive factors, the potential is positive. -/
theorem potential_pos [Nonempty ι] (hφ : ∀ s < t, ∀ i, 0 < φ (ℓ s i)) : 0 < potential φ ℓ t :=
  sum_pos (fun i _ => weight_pos hφ i) univ_nonempty

/-- With positive factors, the learner's probabilities are nonnegative. -/
theorem prob_nonneg (hφ : ∀ s < t, ∀ i, 0 < φ (ℓ s i)) (i : ι) : 0 ≤ prob φ ℓ t i :=
  div_nonneg (weight_pos hφ i).le (sum_nonneg fun j _ => (weight_pos hφ j).le)

/-- With positive factors, the learner plays a probability distribution. -/
theorem sum_prob [Nonempty ι] (hφ : ∀ s < t, ∀ i, 0 < φ (ℓ s i)) : ∑ i, prob φ ℓ t i = 1 := by
  simp only [prob]
  rw [← sum_div]
  exact div_self (potential_pos hφ).ne'

/-- The potential is multiplied by the expected update factor. -/
theorem potential_succ [Nonempty ι] (hφ : ∀ s < t, ∀ i, 0 < φ (ℓ s i)) :
    potential φ ℓ (t + 1) = potential φ ℓ t * ∑ i, prob φ ℓ t i * φ (ℓ t i) := by
  have hΦ := (potential_pos hφ).ne'
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [weight_succ, prob]
  field_simp

/-- With positive factors, the expected update factor is positive. -/
theorem sum_prob_mul_pos [Nonempty ι] (hφ : ∀ s < t + 1, ∀ i, 0 < φ (ℓ s i)) :
    0 < ∑ i, prob φ ℓ t i * φ (ℓ t i) := by
  have hφ' : ∀ s < t, ∀ i, 0 < φ (ℓ s i) := fun s hs => hφ s (by omega)
  have h := potential_pos hφ
  rw [potential_succ hφ'] at h
  exact pos_of_mul_pos_right h (potential_pos hφ').le

/-- The logarithm of the potential: `log n` plus the logarithms of the expected update factors. -/
theorem log_potential [Nonempty ι] (hφ : ∀ s < t, ∀ i, 0 < φ (ℓ s i)) :
    log (potential φ ℓ t) =
      log (Fintype.card ι) + ∑ s ∈ range t, log (∑ i, prob φ ℓ s i * φ (ℓ s i)) := by
  induction t with
  | zero => simp only [potential_zero, range_zero, sum_empty, add_zero]
  | succ t ih =>
    have hφ' : ∀ s < t, ∀ i, 0 < φ (ℓ s i) := fun s hs => hφ s (by omega)
    rw [potential_succ hφ', log_mul (potential_pos hφ').ne' (sum_prob_mul_pos hφ).ne', ih hφ',
      sum_range_succ, add_assoc]

/-- **The potential inequality** [AroraHazanKale2012, proof of Theorem 2.1]: the weight of any
expert is at most the potential, so for every expert `i`, the logarithms of its update factors sum
to at most `log n` plus the logarithms of the learner's expected update factors. -/
theorem sum_log_le_log_card_add [Nonempty ι] (hφ : ∀ s < t, ∀ i, 0 < φ (ℓ s i)) (i : ι) :
    ∑ s ∈ range t, log (φ (ℓ s i)) ≤
      log (Fintype.card ι) + ∑ s ∈ range t, log (∑ j, prob φ ℓ s j * φ (ℓ s j)) := by
  rw [← log_potential hφ, ← log_prod (fun s hs => (hφ s (mem_range.mp hs) i).ne')]
  exact log_le_log (weight_pos hφ i)
    (single_le_sum (fun j _ => (weight_pos hφ j).le) (mem_univ i))

/-- The tuned learning rate `η = √(L / T)` balances the two terms `η T + L / η` of a regret bound:
their sum is then `2 √(T L)`. -/
theorem sqrt_div_mul_add_div_sqrt_div {L T : ℝ} (hL : 0 < L) (hT : 0 < T) :
    √(L / T) * T + L / √(L / T) = 2 * √(T * L) := by
  rw [sqrt_div hL.le, sqrt_mul hT.le]
  have ha := sqrt_pos.mpr hL
  have hb := sqrt_pos.mpr hT
  have hL' := sq_sqrt hL.le
  have hT' := sq_sqrt hT.le
  field_simp
  nlinarith [hL', hT']

/-! ### Adaptive adversaries -/

/-- The weights against an adaptive adversary `adv`, which chooses the loss vector of round `t` as
`adv t p` from the learner's current distribution `p`. -/
@[expose] noncomputable def adaptiveWeight (φ : ℝ → ℝ) (adv : ℕ → (ι → ℝ) → ι → ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun i => adaptiveWeight φ adv t i *
      φ (adv t (fun j => adaptiveWeight φ adv t j / ∑ k, adaptiveWeight φ adv t k) i)

/-- The loss sequence produced by the adaptive adversary `adv` against the multiplicative update
with factor `φ`. -/
@[expose] noncomputable def adaptiveLoss (φ : ℝ → ℝ) (adv : ℕ → (ι → ℝ) → ι → ℝ) (t : ℕ) : ι → ℝ :=
  adv t fun j => adaptiveWeight φ adv t j / ∑ k, adaptiveWeight φ adv t k

/-- The weights against `adaptiveLoss φ adv` are the adaptive weights. -/
theorem weight_adaptiveLoss (φ : ℝ → ℝ) (adv : ℕ → (ι → ℝ) → ι → ℝ) (t : ℕ) :
    weight φ (adaptiveLoss φ adv) t = adaptiveWeight φ adv t := by
  induction t with
  | zero =>
    funext i
    rw [weight_zero]
    rfl
  | succ t ih =>
    funext i
    rw [weight_succ, ih]
    rfl

/-- Against `adaptiveLoss φ adv`, the loss vector of round `t` is the adversary's response to the
learner's distribution in round `t`. So the regret bounds, which hold for every loss sequence,
hold against adaptive adversaries. -/
theorem adaptiveLoss_eq (φ : ℝ → ℝ) (adv : ℕ → (ι → ℝ) → ι → ℝ) (t : ℕ) :
    adaptiveLoss φ adv t = adv t (prob φ (adaptiveLoss φ adv) t) := by
  have h : prob φ (adaptiveLoss φ adv) t =
      fun j => adaptiveWeight φ adv t j / ∑ k, adaptiveWeight φ adv t k := by
    funext j
    rw [prob, potential, weight_adaptiveLoss]
  rw [h]
  rfl

end Cslib.MachineLearning.OnlineLearning.Experts
