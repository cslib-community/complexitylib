/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Expect

/-!
# Optimal stopping: independent observations and stopping rules

Observations `X₁, …, Xₙ` arrive one at a time, drawn independently, `Xᵢ` from the `i`-th law of
`laws`; `jointLaw laws` is the law of the whole list. Unlike `Cslib.Probability.PMF.pi` and
`Cslib.Probability.PMF.iid`, the laws may differ, the value type need not be finite, and the
outcome is a list, the form on which backward induction recurses.

A stopping rule `stop : List α → Bool` sees the history, most recent observation first, and
decides whether to stop at the current observation. A reward `reward past future` may depend on
the observations seen when stopping and on those still to come; the secretary problem, for
instance, rewards stopping at the overall best, which depends on the future. `payoff stop reward
past xs` is the reward collected on the remaining observations `xs` after the history `past`, and
`0` if the rule never stops. Rules are deterministic. A randomized rule is a mixture of
deterministic ones, so every bound below on deterministic rules also bounds randomized ones.

`valueFrom reward laws past` is the backward-induction (dynamic programming) value: at each
step, the better of stopping now and continuing optimally. `tsum_payoff_le_valueFrom` shows that
no stopping rule beats it, and `tsum_payoff_optimalRule` that the rule `optimalRule`, which stops
exactly when stopping is at least as good as continuing, attains it (`valueFrom_eq_iSup`).

## Main definitions

* `Cslib.Probability.OptimalStopping.jointLaw`: independent observations as a list.
* `Cslib.Probability.OptimalStopping.payoff`, `Cslib.Probability.OptimalStopping.stopIndex`: the
  reward collected by a rule and the time at which it stops.
* `Cslib.Probability.OptimalStopping.valueFrom`, `Cslib.Probability.OptimalStopping.optimalRule`:
  the backward-induction value and rule.

## Main results

* `Cslib.Probability.OptimalStopping.tsum_jointLaw_cons_mul`: expectations under `jointLaw`
  condition on the first observation.
* `Cslib.Probability.OptimalStopping.payoff_eq_stopIndex`: the payoff is the reward at the
  stopping time.
* `Cslib.Probability.OptimalStopping.tsum_payoff_le_valueFrom`: no rule's expected payoff exceeds
  the backward-induction value.
* `Cslib.Probability.OptimalStopping.tsum_payoff_optimalRule`,
  `Cslib.Probability.OptimalStopping.valueFrom_eq_iSup`: the backward-induction rule attains it,
  so it is the optimal expected payoff.

## References

* [D. V. Lindley, *Dynamic programming and decision theory*][Lindley1961]
-/

public section

namespace Cslib.Probability.OptimalStopping

open scoped ENNReal

variable {α : Type*}

/-- Independent observations, the `i`-th drawn from the `i`-th law, collected into a list. -/
@[expose] noncomputable def jointLaw : List (PMF α) → PMF (List α)
  | [] => PMF.pure []
  | μ :: laws => do
      let x ← μ
      let xs ← jointLaw laws
      return x :: xs

@[simp] theorem jointLaw_nil : jointLaw ([] : List (PMF α)) = PMF.pure [] := rfl

theorem jointLaw_cons (μ : PMF α) (laws : List (PMF α)) :
    jointLaw (μ :: laws) = μ.bind fun x => (jointLaw laws).map (x :: ·) := rfl

/-- Observing two blocks of independent observations, one after the other. -/
theorem jointLaw_append (laws₁ laws₂ : List (PMF α)) :
    jointLaw (laws₁ ++ laws₂) =
      (jointLaw laws₁).bind fun xs => (jointLaw laws₂).map (xs ++ ·) := by
  induction laws₁ with
  | nil => simp only [List.nil_append, jointLaw_nil, PMF.pure_bind]; exact (PMF.map_id _).symm
  | cons μ laws ih =>
    simp only [List.cons_append, jointLaw_cons, ih, PMF.bind_bind, PMF.map_bind, PMF.bind_map]
    congr 1
    funext x
    simp only [Function.comp_def, PMF.map_comp]
    rfl

/-- An expectation under `jointLaw` conditions on the first observation. -/
theorem tsum_jointLaw_cons_mul (μ : PMF α) (laws : List (PMF α)) (k : List α → ℝ≥0∞) :
    ∑' xs, jointLaw (μ :: laws) xs * k xs =
      ∑' x, μ x * ∑' xs, jointLaw laws xs * k (x :: xs) := by
  rw [jointLaw_cons, Cslib.Probability.PMF.tsum_bind_mul]
  refine tsum_congr fun x => ?_
  rw [Cslib.Probability.PMF.tsum_map_mul]

theorem tsum_jointLaw_nil_mul (k : List α → ℝ≥0∞) :
    ∑' xs, jointLaw ([] : List (PMF α)) xs * k xs = k [] := by
  rw [jointLaw_nil, tsum_eq_single []]
  · simp
  · intro xs hxs
    simp [PMF.pure_apply, hxs]

/-- The expectation of a constant is that constant. -/
theorem tsum_pmf_mul_const (μ : PMF α) (c : ℝ≥0∞) : ∑' x, μ x * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The reward collected by the rule `stop` on the remaining observations `xs` after the history
`past` (most recent first): it stops at the first `x` with `stop (x :: past)` and collects
`reward (x :: past) future`, where `future` are the observations after `x`. A rule that never
stops collects `0`. -/
@[expose] noncomputable def payoff (stop : List α → Bool)
    (reward : List α → List α → ℝ≥0∞) : List α → List α → ℝ≥0∞
  | _, [] => 0
  | past, x :: future =>
      if stop (x :: past) then reward (x :: past) future else payoff stop reward (x :: past) future

/-- The position in `xs` at which the rule `stop` stops after the history `past`, if any. -/
@[expose] def stopIndex (stop : List α → Bool) : List α → List α → Option ℕ
  | _, [] => none
  | past, x :: future =>
      if stop (x :: past) then some 0 else (stopIndex stop (x :: past) future).map (· + 1)

theorem stopIndex_lt (stop : List α → Bool) :
    ∀ (past xs : List α) {k : ℕ}, stopIndex stop past xs = some k → k < xs.length
  | _, [], _, h => by simp [stopIndex] at h
  | past, x :: future, k, h => by
      by_cases hs : stop (x :: past)
      · simp only [stopIndex, hs, ite_true, Option.some.injEq] at h
        simp [← h]
      · simp only [stopIndex, hs, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at h
        obtain ⟨j, hj, rfl⟩ := h
        have := stopIndex_lt stop (x :: past) future hj
        simp only [List.length_cons]
        omega

/-- The payoff is the reward at the stopping time, and `0` if the rule never stops. -/
theorem payoff_eq_stopIndex (stop : List α → Bool) (reward : List α → List α → ℝ≥0∞) :
    ∀ (past xs : List α), payoff stop reward past xs =
      (stopIndex stop past xs).elim 0
        fun k => reward ((xs.take (k + 1)).reverse ++ past) (xs.drop (k + 1))
  | _, [] => by simp [payoff, stopIndex]
  | past, x :: future => by
      by_cases hs : stop (x :: past)
      · simp [payoff, stopIndex, hs]
      · simp only [payoff, stopIndex, hs, Bool.false_eq_true, ite_false]
        rw [payoff_eq_stopIndex stop reward (x :: past) future]
        cases stopIndex stop (x :: past) future with
        | none => rfl
        | some k => simp [List.take_succ_cons, List.reverse_cons]

/-- The backward-induction value of the remaining observations with laws `laws` after the history
`past`: on observing `x`, the better of stopping, with expected reward over the remaining
observations, and continuing optimally. -/
@[expose] noncomputable def valueFrom (reward : List α → List α → ℝ≥0∞) :
    List (PMF α) → List α → ℝ≥0∞
  | [], _ => 0
  | μ :: laws, past => ∑' x, μ x *
      max (∑' xs, jointLaw laws xs * reward (x :: past) xs) (valueFrom reward laws (x :: past))

theorem payoff_nil (stop : List α → Bool) (reward : List α → List α → ℝ≥0∞) (past : List α) :
    payoff stop reward past [] = 0 := rfl

theorem payoff_cons (stop : List α → Bool) (reward : List α → List α → ℝ≥0∞)
    (past : List α) (x : α) (future : List α) :
    payoff stop reward past (x :: future) =
      if stop (x :: past) then reward (x :: past) future
      else payoff stop reward (x :: past) future := rfl

theorem valueFrom_nil (reward : List α → List α → ℝ≥0∞) (past : List α) :
    valueFrom reward [] past = 0 := rfl

theorem valueFrom_cons (reward : List α → List α → ℝ≥0∞) (μ : PMF α) (laws : List (PMF α))
    (past : List α) :
    valueFrom reward (μ :: laws) past = ∑' x, μ x *
      max (∑' xs, jointLaw laws xs * reward (x :: past) xs) (valueFrom reward laws (x :: past)) :=
  rfl

/-- **Backward induction**: no stopping rule's expected payoff exceeds the backward-induction
value. -/
theorem tsum_payoff_le_valueFrom (stop : List α → Bool) (reward : List α → List α → ℝ≥0∞) :
    ∀ (laws : List (PMF α)) (past : List α),
      ∑' xs, jointLaw laws xs * payoff stop reward past xs ≤ valueFrom reward laws past
  | [], past => by simp [payoff, valueFrom]
  | μ :: laws, past => by
      rw [tsum_jointLaw_cons_mul, valueFrom]
      refine tsum_le_tsum fun x => ?_
      gcongr
      by_cases h : stop (x :: past)
      · simp only [payoff, h, ite_true]
        exact le_max_left _ _
      · simp only [payoff, h, Bool.false_eq_true, ite_false]
        exact (tsum_payoff_le_valueFrom stop reward laws (x :: past)).trans (le_max_right _ _)

/-- The backward-induction rule for the observation laws `laws`: on the history `h` (most recent
first), with the laws `laws.drop h.length` still to come, stop exactly when stopping is at least
as good as continuing optimally. -/
noncomputable def optimalRule (reward : List α → List α → ℝ≥0∞) (laws : List (PMF α)) :
    List α → Bool := fun h =>
  decide (valueFrom reward (laws.drop h.length) h ≤
    ∑' xs, jointLaw (laws.drop h.length) xs * reward h xs)

/-- `optimalRule` attains the value from every history whose length is the number of laws
already used. -/
private theorem tsum_payoff_optimalRule_aux (reward : List α → List α → ℝ≥0∞) :
    ∀ (rest pre : List (PMF α)) (past : List α), past.length = pre.length →
      ∑' xs, jointLaw rest xs * payoff (optimalRule reward (pre ++ rest)) reward past xs =
        valueFrom reward rest past
  | [], pre, past, _ => by rw [tsum_jointLaw_nil_mul, payoff_nil, valueFrom_nil]
  | μ :: rest, pre, past, hlen => by
      rw [tsum_jointLaw_cons_mul, valueFrom_cons]
      refine tsum_congr fun x => ?_
      congr 1
      have hsplit : pre ++ μ :: rest = (pre ++ [μ]) ++ rest := by simp
      have hdrop : (pre ++ μ :: rest).drop (x :: past).length = rest := by
        rw [hsplit]
        exact List.drop_left' (by simp [hlen])
      simp only [payoff_cons]
      by_cases h : valueFrom reward rest (x :: past) ≤
          ∑' xs, jointLaw rest xs * reward (x :: past) xs
      · have hr : optimalRule reward (pre ++ μ :: rest) (x :: past) = true := by
          rw [optimalRule, hdrop]; exact decide_eq_true h
        simp only [hr, ite_true]
        exact (max_eq_left h).symm
      · have hr : optimalRule reward (pre ++ μ :: rest) (x :: past) = false := by
          rw [optimalRule, hdrop]; exact decide_eq_false h
        simp only [hr, Bool.false_eq_true, ite_false]
        rw [hsplit,
          tsum_payoff_optimalRule_aux reward rest (pre ++ [μ]) (x :: past) (by simp [hlen])]
        exact (max_eq_right (not_le.mp h).le).symm

/-- **Backward induction attains the value**: the rule `optimalRule` collects exactly the
backward-induction value. -/
theorem tsum_payoff_optimalRule (reward : List α → List α → ℝ≥0∞) (laws : List (PMF α)) :
    ∑' xs, jointLaw laws xs * payoff (optimalRule reward laws) reward [] xs =
      valueFrom reward laws [] :=
  tsum_payoff_optimalRule_aux reward laws [] [] rfl

/-- The backward-induction value is the best expected payoff of any stopping rule. -/
theorem valueFrom_eq_iSup (reward : List α → List α → ℝ≥0∞) (laws : List (PMF α)) :
    valueFrom reward laws [] =
      ⨆ stop : List α → Bool, ∑' xs, jointLaw laws xs * payoff stop reward [] xs :=
  le_antisymm ((tsum_payoff_optimalRule reward laws).symm.le.trans
      (le_iSup (fun stop : List α → Bool => ∑' xs, jointLaw laws xs * payoff stop reward [] xs)
        (optimalRule reward laws)))
    (iSup_le fun stop => tsum_payoff_le_valueFrom stop reward laws [])

end Cslib.Probability.OptimalStopping
