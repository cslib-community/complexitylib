/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.MachineLearning.OnlineLearning.MultiplicativeUpdate
public import Cslib.MachineLearning.PACLearning.VersionSpace

/-!
# AdaBoost

AdaBoost [FreundSchapire1997] on a finite labelled sample `S : Fin m → α × Bool`, with a weak
learner `A : (Fin m → ℝ) → α → Bool` that maps weights on the sample to a hypothesis. Round `t`
(a `Round`: weights and hypothesis) has weights `Dₜ`, weighted error `εₜ` and vote weight
`wₜ = ½ log ((1 - εₜ) / εₜ)`; the next weights multiply `Dₜ i` by `exp (-wₜ yᵢ hₜ(xᵢ))` (signs
`±1`, via `BitString.signVal`) and renormalize (`rounds_weights_succ`). The output is the sign of
the weighted vote `∑ₜ wₜ hₜ`.

The weights are the multiplicative-update distribution of the experts setting
(`CslibFrontier/MachineLearning/OnlineLearning/MultiplicativeUpdate.lean`) with the sample points
as experts, update factor `exp`, and the adaptive loss sequence chosen by the weak learner. The
proof of the training-error bound is the potential argument of that file: each misclassified point
has weight at least `1`, and the potential is `m` times the product of the normalizers, each equal
to `2 √(εₜ (1 - εₜ))`.

## Main definitions

* `Round`: the state of a round (weights and weak hypothesis), with `Round.error` and
  `Round.vote`.
* `rounds S A t`: round `t` of AdaBoost.
* `score S A T`: the weighted vote of the first `T` rounds.
* `adaBoost S A T`: the output of `T` rounds.
* `IsWeakLearner S A γ`: on every positive distribution on `S`, `A` has weighted error at most
  `1/2 - γ`.

## Main results

* `rounds_weights_succ`: the AdaBoost reweighting step.
* `sum_mul_exp_pointLoss`: the normalizer of a round is `2 √(ε (1 - ε))`.
* `empiricalMiscount_adaBoost_le_prod`: the training error is at most `∏ₜ 2 √(εₜ (1 - εₜ))`.
* `empiricalMiscount_adaBoost_le_exp_sum`: the training error is at most
  `exp (-2 ∑ₜ (1/2 - εₜ)²)`.
* `empiricalMiscount_adaBoost_le_exp`: if every `εₜ ≤ 1/2 - γ`, the training error is at most
  `exp (-2 γ² T)`.
* `IsWeakLearner.empiricalMiscount_adaBoost_eq_zero`: with a weak learner of edge `γ` and
  `log m < 2 γ² T`, the output is consistent with the sample.

## Model and differences from the sources

[ShalevShwartzBenDavid2014, Theorem 10.2] states the `exp (-2 γ² T)` bound and proves the product
form on pp. 135–137; [MohriRostamizadehTalwalkar2018, Theorem 7.2] states both through
`exp (-2 ∑ₜ (1/2 - εₜ)²)` and proves the product form. Differences:

* A round with `εₜ = 0` makes `wₜ` infinite in the sources. Here AdaBoost stops at the first such
  round and returns its hypothesis, which is consistent with the sample.
* The product form assumes `εₜ < 1` (at `εₜ = 1` the factor vanishes but the vote weight in Lean
  is `log 0 / 2 = 0`).
* A tie in the vote predicts `false`. This misclassifies no more points than the sources' count,
  which treats a tie as an error.
* The weak learner is deterministic, with the edge as a hypothesis on the rounds (or on all
  positive distributions in `IsWeakLearner`); SSBD's weak learner may fail with probability `δ`
  (Remark 10.2), which a union bound handles outside this statement.
* Generalization of the output (SSBD Section 10.3, MRT Corollary 7.5) is not covered.

## References

* [FreundSchapire1997]
* [ShalevShwartzBenDavid2014]
* [MohriRostamizadehTalwalkar2018]
-/

public section

namespace Cslib.MachineLearning.Boosting

open Finset Real PACLearning BitString

variable {α : Type*} {m : ℕ}

/-- The weighted error of `h` on the sample `S` under the weights `D`: the total weight of the
sample points that `h` labels incorrectly. -/
@[expose] noncomputable def weightedError (S : Fin m → α × Bool) (D : Fin m → ℝ) (h : α → Bool) :
    ℝ :=
  ∑ i with h (S i).1 ≠ (S i).2, D i

/-- The vote weight `½ log ((1 - ε) / ε)` of a weak hypothesis with weighted error `ε`. -/
@[expose] noncomputable def voteWeight (ε : ℝ) : ℝ := log ((1 - ε) / ε) / 2

/-- The exponential loss of `h` at the labelled point `z` with vote weight `w`: `-w` if `h` labels
`z` correctly and `w` otherwise, written with the signs `signVal` of the prediction and the label.
AdaBoost multiplies the weight of `z` by `exp` of this loss. -/
noncomputable def pointLoss (w : ℝ) (h : α → Bool) (z : α × Bool) : ℝ :=
  -(w * (signVal (h z.1) * signVal z.2))

/-- One round of AdaBoost: the weights on the sample and the weak hypothesis chosen for them. -/
structure Round (α : Type*) (m : ℕ) where
  /-- The round's weights on the sample points. -/
  weights : Fin m → ℝ
  /-- The weak hypothesis returned for these weights. -/
  hyp : α → Bool

namespace Round

variable (S : Fin m → α × Bool) (r : Round α m)

/-- The weighted error of the round's hypothesis under the round's weights. -/
noncomputable def error : ℝ := weightedError S r.weights r.hyp

/-- The vote weight of the round's hypothesis. -/
noncomputable def vote : ℝ := voteWeight (r.error S)

end Round

/-- The loss vector that AdaBoost hands to the multiplicative update when the weak learner `A`
answers the weights `D`. -/
noncomputable def roundLoss (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool)
    (D : Fin m → ℝ) (i : Fin m) : ℝ :=
  pointLoss (voteWeight (weightedError S D (A D))) (A D) (S i)

open OnlineLearning.Experts in
/-- The loss sequence that AdaBoost's weak learner `A` produces against the multiplicative update
with factor `exp`. -/
noncomputable def lossSeq (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) : ℕ → Fin m → ℝ :=
  adaptiveLoss exp fun _ => roundLoss S A

open OnlineLearning.Experts in
/-- The rounds of AdaBoost on the sample `S` with the weak learner `A`: round `t` has the weights
of the multiplicative update with factor `exp` against the losses `lossSeq`, which start uniform,
and the hypothesis `A` returns for them. -/
noncomputable def rounds (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) (t : ℕ) :
    Round α m :=
  ⟨prob exp (lossSeq S A) t, A (prob exp (lossSeq S A) t)⟩

section Rounds

open OnlineLearning.Experts

variable (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) (t : ℕ)

/-- The weights of round `t` are the multiplicative-update distribution. -/
theorem rounds_weights : (rounds S A t).weights = prob exp (lossSeq S A) t := by
  rw [rounds]

/-- The hypothesis of round `t` is the weak learner's answer to the round's weights. -/
theorem rounds_hyp : (rounds S A t).hyp = A (rounds S A t).weights := by
  rw [rounds]

/-- The loss of round `t` is the exponential loss of the round's hypothesis with its vote
weight. -/
theorem lossSeq_apply (i : Fin m) :
    lossSeq S A t i = pointLoss ((rounds S A t).vote S) (rounds S A t).hyp (S i) := by
  rw [lossSeq, adaptiveLoss_eq, roundLoss, ← lossSeq, Round.vote, Round.error, rounds_hyp,
    rounds_weights]

/-- AdaBoost's weights are positive. -/
theorem rounds_weights_pos (i : Fin m) : 0 < (rounds S A t).weights i :=
  prob_pos (fun _ _ _ => exp_pos _) i

/-- AdaBoost starts from the uniform weights. -/
theorem rounds_zero_weights (i : Fin m) : (rounds S A 0).weights i = 1 / m := by
  rw [rounds_weights, prob, weight_zero, potential_zero, Fintype.card_fin]

/-- AdaBoost's weights form a distribution on a nonempty sample. -/
theorem sum_rounds_weights [NeZero m] : ∑ i, (rounds S A t).weights i = 1 :=
  sum_prob fun _ _ _ => exp_pos _

/-- **The AdaBoost update** [ShalevShwartzBenDavid2014, Section 10.2]: the weight of a sample point
is multiplied by `exp (-wₜ yᵢ hₜ(xᵢ))`, its exponential loss, and the weights are renormalized. -/
theorem rounds_weights_succ (i : Fin m) :
    (rounds S A (t + 1)).weights i =
      (rounds S A t).weights i * exp (pointLoss ((rounds S A t).vote S) (rounds S A t).hyp (S i)) /
        ∑ j, (rounds S A t).weights j *
          exp (pointLoss ((rounds S A t).vote S) (rounds S A t).hyp (S j)) := by
  simp only [rounds_weights, ← lossSeq_apply]
  exact prob_succ (fun _ _ _ => exp_pos _) i

end Rounds

/-- **The AdaBoost normalizer** [ShalevShwartzBenDavid2014, proof of Theorem 10.2]: under a
distribution `D` on the sample, if the hypothesis `h` has weighted error `ε` with `0 < ε < 1`, then
reweighting by the exponential loss with vote weight `voteWeight ε` multiplies the total weight by
`2 √(ε (1 - ε))`. -/
theorem sum_mul_exp_pointLoss {S : Fin m → α × Bool} {D : Fin m → ℝ} {h : α → Bool}
    (hD : ∑ i, D i = 1) (hε₀ : 0 < weightedError S D h) (hε₁ : weightedError S D h < 1) :
    ∑ i, D i * exp (pointLoss (voteWeight (weightedError S D h)) h (S i)) =
      2 * √(weightedError S D h * (1 - weightedError S D h)) := by
  have hwrong : ∑ i with h (S i).1 ≠ (S i).2, D i = weightedError S D h := rfl
  have hright : ∑ i with ¬h (S i).1 ≠ (S i).2, D i = 1 - weightedError S D h := by
    rw [← hD, ← hwrong, ← sum_filter_add_sum_filter_not univ (fun i => h (S i).1 ≠ (S i).2)]
    ring
  have hterm : ∀ i, D i * exp (pointLoss (voteWeight (weightedError S D h)) h (S i)) =
      if h (S i).1 ≠ (S i).2 then D i * exp (voteWeight (weightedError S D h))
      else D i * (exp (voteWeight (weightedError S D h)))⁻¹ := by
    intro i
    by_cases hi : h (S i).1 = (S i).2
    · rw [ite_eq_right (not_not.mpr hi), pointLoss, signVal_mul_signVal, ite_eq_left hi, mul_one,
        exp_neg]
    · rw [ite_eq_left hi, pointLoss, signVal_mul_signVal, ite_eq_right hi, mul_neg, mul_one,
        neg_neg]
  rw [sum_congr rfl fun i _ => hterm i, sum_ite, ← sum_mul, ← sum_mul, hwrong, hright]
  generalize weightedError S D h = ε at *
  have ha0 : 0 < exp (voteWeight ε) := exp_pos _
  have ha2 : exp (voteWeight ε) * exp (voteWeight ε) = (1 - ε) / ε := by
    rw [← exp_add, voteWeight, add_halves, exp_log (div_pos (by linarith) hε₀)]
  generalize exp (voteWeight ε) = a at *
  have h1 : 1 - ε = ε * (a * a) := by
    rw [ha2]
    field_simp
  have hsq : √(ε * (1 - ε)) = ε * a := by
    rw [sqrt_eq_iff_mul_self_eq (by nlinarith) (by positivity), h1]
    ring
  rw [hsq, h1]
  field_simp
  ring

/-- The weighted vote of the first `T` rounds at `x`: the total vote weight of the hypotheses
predicting `true` minus that of the hypotheses predicting `false` (`signVal true = -1`). -/
noncomputable def score (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) (T : ℕ) (x : α) : ℝ :=
  -∑ t ∈ range T, (rounds S A t).vote S * signVal ((rounds S A t).hyp x)

open Classical in
/-- **AdaBoost** [FreundSchapire1997] run for `T` rounds on the sample `S` with the weak learner
`A`. If some round before `T` has weighted error `0`, the output is the hypothesis of the first
such round (AdaBoost stops there). Otherwise it is the sign of the weighted vote `score`, with ties
going to `false`. -/
noncomputable def adaBoost (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) (T : ℕ) :
    α → Bool :=
  if h : ∃ t < T, (rounds S A t).error S = 0 then (rounds S A (Nat.find h)).hyp
  else fun x => decide (0 < score S A T x)

section Vote

variable (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool)

/-- The cumulative loss at a sample point is the weighted vote times the sign of the label: it is
nonnegative exactly where the vote disagrees with the label. -/
theorem sum_lossSeq (T : ℕ) (i : Fin m) :
    ∑ t ∈ range T, lossSeq S A t i = score S A T (S i).1 * signVal (S i).2 := by
  rw [score, neg_mul, sum_mul, ← sum_neg_distrib]
  refine sum_congr rfl fun t _ => ?_
  rw [lossSeq_apply, pointLoss, mul_assoc]

/-- Where the weighted vote errs, the cumulative loss is nonnegative. -/
theorem sum_lossSeq_nonneg {T : ℕ} {i : Fin m} (hi : decide (0 < score S A T (S i).1) ≠ (S i).2) :
    0 ≤ ∑ t ∈ range T, lossSeq S A t i := by
  rw [sum_lossSeq]
  cases hy : (S i).2
  · rw [hy, ne_eq, Bool.not_eq_false, decide_eq_true_eq] at hi
    rw [signVal_false, mul_one]
    exact hi.le
  · rw [hy, ne_eq, Bool.not_eq_true, decide_eq_false_iff_not, not_lt] at hi
    rw [signVal_true, mul_neg_one]
    exact neg_nonneg.mpr hi

/-- A round with weighted error `0` has a hypothesis consistent with the sample, since every
sample point has positive weight. -/
theorem hyp_eq_of_error_eq_zero {t : ℕ} (h : (rounds S A t).error S = 0) (i : Fin m) :
    (rounds S A t).hyp (S i).1 = (S i).2 := by
  by_contra hi
  have hpos : 0 < (rounds S A t).error S :=
    sum_pos (fun j _ => rounds_weights_pos S A t j) ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  exact hpos.ne' h

open OnlineLearning.Experts in
/-- The number of sample points where the weighted vote errs is at most the potential of the
multiplicative update, since each such point has weight at least `1`. -/
theorem empiricalMiscount_le_potential (T : ℕ) :
    (empiricalMiscount (fun x => decide (0 < score S A T x)) S : ℝ) ≤
      potential exp (lossSeq S A) T := by
  rw [empiricalMiscount, card_filter, Nat.cast_sum, potential]
  refine sum_le_sum fun i _ => ?_
  have hw : 0 < weight exp (lossSeq S A) T i := weight_pos (fun _ _ _ => exp_pos _) i
  split_ifs with hi
  · rw [Nat.cast_one, weight, ← exp_sum]
    exact one_le_exp (sum_lossSeq_nonneg S A hi)
  · rw [Nat.cast_zero]
    exact hw.le

/-- The weighted error of every round is nonnegative. -/
theorem rounds_error_nonneg (t : ℕ) : 0 ≤ (rounds S A t).error S := by
  rw [Round.error]
  exact sum_nonneg fun i _ => (rounds_weights_pos S A t i).le

open OnlineLearning.Experts in
/-- **The AdaBoost training-error bound, product form** ([ShalevShwartzBenDavid2014], proof of
Theorem 10.2; [MohriRostamizadehTalwalkar2018], proof of Theorem 7.2): if every round before `T`
has weighted error `εₜ < 1`, the fraction of sample points that the output of `T` rounds of
AdaBoost misclassifies is at most `∏ₜ 2 √(εₜ (1 - εₜ))`. A round with `εₜ = 0` stops AdaBoost with
a consistent hypothesis. -/
theorem empiricalMiscount_adaBoost_le_prod {T : ℕ} (hlt : ∀ t < T, (rounds S A t).error S < 1) :
    (empiricalMiscount (adaBoost S A T) S : ℝ) / m ≤
      ∏ t ∈ range T, 2 * √((rounds S A t).error S * (1 - (rounds S A t).error S)) := by
  have hprod : 0 ≤ ∏ t ∈ range T,
      2 * √((rounds S A t).error S * (1 - (rounds S A t).error S)) :=
    prod_nonneg fun _ _ => by positivity
  by_cases hz : ∃ t < T, (rounds S A t).error S = 0
  · have h0 : empiricalMiscount (adaBoost S A T) S = 0 := by
      rw [adaBoost, dite_eq_left hz, empiricalMiscount, card_eq_zero, filter_eq_empty_iff]
      exact fun i _ hi => hi (hyp_eq_of_error_eq_zero S A (Nat.find_spec hz).2 i)
    rw [h0, Nat.cast_zero, zero_div]
    exact hprod
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero, div_zero]
    exact hprod
  have : NeZero m := ⟨hm.ne'⟩
  have hstep : ∀ t ∈ range T, ∑ i, prob exp (lossSeq S A) t i * exp (lossSeq S A t i) =
      2 * √((rounds S A t).error S * (1 - (rounds S A t).error S)) := fun t ht => by
    have ht' := mem_range.mp ht
    have hε₀ : 0 < (rounds S A t).error S :=
      (rounds_error_nonneg S A t).lt_of_ne fun h => hz ⟨t, ht', h.symm⟩
    have hε₁ := hlt t ht'
    simp only [lossSeq_apply, ← rounds_weights, Round.vote]
    rw [Round.error] at hε₀ hε₁ ⊢
    exact sum_mul_exp_pointLoss (sum_rounds_weights S A t) hε₀ hε₁
  rw [adaBoost, dite_eq_right hz, div_le_iff₀ (Nat.cast_pos.mpr hm)]
  calc (empiricalMiscount (fun x => decide (0 < score S A T x)) S : ℝ)
      ≤ potential exp (lossSeq S A) T := empiricalMiscount_le_potential S A T
    _ = _ := by
      rw [potential_eq_card_mul_prod (fun _ _ _ => exp_pos _), Fintype.card_fin,
        prod_congr rfl hstep, mul_comm]

/-- The AdaBoost factor of an error `ε` is at most `exp (-2 (1/2 - ε)²)`, since
`4 ε (1 - ε) = 1 - 4 (1/2 - ε)²`. -/
theorem two_mul_sqrt_le_exp (ε : ℝ) : 2 * √(ε * (1 - ε)) ≤ exp (-(2 * (1 / 2 - ε) ^ 2)) := by
  have hsq : exp (-(2 * (1 / 2 - ε) ^ 2)) ^ 2 = exp (-(4 * (1 / 2 - ε) ^ 2)) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 := add_one_le_exp (-(4 * (1 / 2 - ε) ^ 2))
  have hsqrt : √(ε * (1 - ε)) ≤ exp (-(2 * (1 / 2 - ε) ^ 2)) / 2 := by
    rw [sqrt_le_left (by positivity), div_pow, hsq]
    nlinarith
  linarith

/-- **The AdaBoost training-error bound in terms of the edges** [MohriRostamizadehTalwalkar2018,
Theorem 7.2, (7.3)]: if every round before `T` has weighted error `εₜ < 1`, the fraction of sample
points that the output of `T` rounds misclassifies is at most `exp (-2 ∑ₜ (1/2 - εₜ)²)`. -/
theorem empiricalMiscount_adaBoost_le_exp_sum {T : ℕ} (hlt : ∀ t < T, (rounds S A t).error S < 1) :
    (empiricalMiscount (adaBoost S A T) S : ℝ) / m ≤
      exp (-(2 * ∑ t ∈ range T, (1 / 2 - (rounds S A t).error S) ^ 2)) := by
  refine (empiricalMiscount_adaBoost_le_prod S A hlt).trans ?_
  rw [mul_sum, ← sum_neg_distrib, exp_sum]
  exact prod_le_prod₀ (fun _ _ => by positivity) fun t _ => two_mul_sqrt_le_exp _

/-- **The AdaBoost training-error bound, exponential form** [ShalevShwartzBenDavid2014,
Theorem 10.2; MohriRostamizadehTalwalkar2018, Theorem 7.2, (7.4)]: if every round before `T` has
weighted error at most `1/2 - γ` with `γ ≥ 0`, the fraction of sample points that the output of
`T` rounds misclassifies is at most `exp (-2 γ² T)`. -/
theorem empiricalMiscount_adaBoost_le_exp {T : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (hε : ∀ t < T, (rounds S A t).error S ≤ 1 / 2 - γ) :
    (empiricalMiscount (adaBoost S A T) S : ℝ) / m ≤ exp (-(2 * γ ^ 2 * T)) := by
  refine (empiricalMiscount_adaBoost_le_exp_sum S A fun t ht => by linarith [hε t ht]).trans ?_
  have hsum : T * γ ^ 2 ≤ ∑ t ∈ range T, (1 / 2 - (rounds S A t).error S) ^ 2 := by
    have h := sum_le_sum fun t (ht : t ∈ range T) => pow_le_pow_left₀ hγ
      (by linarith [hε t (mem_range.mp ht)] : γ ≤ 1 / 2 - (rounds S A t).error S) 2
    rwa [sum_const, card_range, nsmul_eq_mul] at h
  exact exp_le_exp.mpr (by nlinarith)

end Vote

/-- The weak learner `A` has edge `γ` on the sample `S`: for every distribution on the sample with
positive weights, the hypothesis it returns has weighted error at most `1/2 - γ`. -/
@[expose] def IsWeakLearner (S : Fin m → α × Bool) (A : (Fin m → ℝ) → α → Bool) (γ : ℝ) : Prop :=
  ∀ D : Fin m → ℝ, (∀ i, 0 < D i) → ∑ i, D i = 1 → weightedError S D (A D) ≤ 1 / 2 - γ

namespace IsWeakLearner

variable {S : Fin m → α × Bool} {A : (Fin m → ℝ) → α → Bool} {γ : ℝ}

/-- Against a weak learner with edge `γ`, every round of AdaBoost has weighted error at most
`1/2 - γ`. -/
theorem rounds_error_le [NeZero m] (hA : IsWeakLearner S A γ) (t : ℕ) :
    (rounds S A t).error S ≤ 1 / 2 - γ := by
  rw [Round.error, rounds_hyp]
  exact hA _ (rounds_weights_pos S A t) (sum_rounds_weights S A t)

/-- **Weak learning gives consistency**, a consequence of [ShalevShwartzBenDavid2014, Theorem 10.2]:
against a weak learner with edge `γ ≥ 0`, AdaBoost run for `T` rounds with `log m < 2 γ² T`
returns a hypothesis that is consistent with the sample. -/
theorem empiricalMiscount_adaBoost_eq_zero (hA : IsWeakLearner S A γ) (hγ : 0 ≤ γ) {T : ℕ}
    (hT : log m < 2 * γ ^ 2 * T) : empiricalMiscount (adaBoost S A T) S = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [empiricalMiscount, univ_eq_empty, filter_empty, card_empty]
  have : NeZero m := ⟨hm.ne'⟩
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h := empiricalMiscount_adaBoost_le_exp (T := T) S A hγ fun t _ => hA.rounds_error_le t
  have hlt : exp (-(2 * γ ^ 2 * T)) < 1 / m := by
    rw [one_div, ← exp_log hmR, ← exp_neg]
    exact exp_lt_exp.mpr (by linarith)
  have h1 := (div_lt_div_iff_of_pos_right hmR).mp (h.trans_lt hlt)
  exact Nat.lt_one_iff.mp (by exact_mod_cast h1)

/-- Under the hypotheses of `empiricalMiscount_adaBoost_eq_zero`, the output labels every sample
point correctly. -/
theorem adaBoost_eq (hA : IsWeakLearner S A γ) (hγ : 0 ≤ γ) {T : ℕ} (hT : log m < 2 * γ ^ 2 * T)
    (i : Fin m) : adaBoost S A T (S i).1 = (S i).2 := by
  have h := hA.empiricalMiscount_adaBoost_eq_zero hγ hT
  rw [empiricalMiscount, card_eq_zero, filter_eq_empty_iff] at h
  exact not_not.mp (h (mem_univ i))

end IsWeakLearner

end Cslib.MachineLearning.Boosting
