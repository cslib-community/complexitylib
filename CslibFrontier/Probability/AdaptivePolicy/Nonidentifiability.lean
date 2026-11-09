/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.AdaptivePolicy.Covariance
import Mathlib.Tactic

/-!
# Nonidentifiability from contextual bandit logs

[Aldridge2027], Proposition 5.2, PDF p. 5, specialized to finite contexts and
actions. Losses in the two constructed instances are deterministic and in
`{0, 1}`. The recorded triple includes context, action and observed loss;
logged propensities are deterministic functions of the recorded context.
`logLaw` is the actual joint probability table and `sampleLaw` is its i.i.d.
product for an arbitrary number of rounds. The construction changes only an
unobserved context/action pair, preserving these complete laws while changing
the policy-minus-open-loop cost. No estimator or desired inequality is assumed.

## Main results

* `finite_nonidentifiability`: equal logged-data laws for every sample count,
  but different adaptivity costs whenever marginal overlap fails.
-/

public section
noncomputable section
open Finset
namespace Cslib.Probability.AdaptivePolicy.FiniteMDP
variable {S A : Type*} [Fintype S] [Fintype A]
variable (M : FiniteMDP S A) (π : MarkovPolicy S A)

/-- Actual bandit-feedback law for a deterministic binary loss table. -/
@[expose] def logLaw (loss : S → A → Bool) (z : S × A × Bool) : ℝ :=
  M.initial z.1 * π.prob 0 z.1 z.2.1 * if z.2.2 = loss z.1 z.2.1 then 1 else 0

/-- Independent repeated logs; the empty log has probability one. -/
@[expose] def sampleLaw (loss : S → A → Bool) (T : ℕ)
    (z : Fin T → S × A × Bool) : ℝ := ∏ t, M.logLaw π loss (z t)

/-- The adaptivity cost of the contextual binary-loss instance. -/
@[expose] def contextualGap (loss : S → A → Bool) : ℝ :=
  (∑ s, ∑ a, M.initial s * π.prob 0 s a * if loss s a then 1 else 0) -
    ∑ s, ∑ a, M.initial s * (∑ x, M.initial x * π.prob 0 x a) *
      if loss s a then 1 else 0

/-- The logged table has nonnegative probabilities. -/
theorem logLaw_nonneg (loss : S → A → Bool) (z : S × A × Bool) :
    0 ≤ M.logLaw π loss z := by
  unfold logLaw
  exact mul_nonneg (mul_nonneg (M.initial_nonneg _) (π.nonneg _ _ _))
    (ite_nonneg (by norm_num) (by norm_num))

/-- The logged table has total mass one. -/
theorem logLaw_sum (loss : S → A → Bool) : ∑ z, M.logLaw π loss z = 1 := by
  classical
  simp only [logLaw, Fintype.sum_prod_type, ← mul_sum]
  simp only [sum_ite_eq', mem_univ, ite_true, mul_one]
  simp only [← mul_sum, π.sum_prob, mul_one, M.initial_sum]

/-- Finite-context form of Proposition 5.2: arbitrary-length complete logs have
identical laws under two bounded cost models with different adaptivity costs. -/
theorem finite_nonidentifiability (E : Finset S) (a₀ : A)
    (hoverlap : ∀ s ∈ E, π.prob 0 s a₀ = 0)
    (hmarginal : 0 < ∑ s, M.initial s * π.prob 0 s a₀)
    (hmass : 0 < ∑ s ∈ E, M.initial s) :
    ∃ loss₀ loss₁ : S → A → Bool,
      (∀ T z, M.sampleLaw π loss₀ T z = M.sampleLaw π loss₁ T z) ∧
      M.contextualGap π loss₁ - M.contextualGap π loss₀ =
        -(∑ s, M.initial s * π.prob 0 s a₀) * (∑ s ∈ E, M.initial s) ∧
      M.contextualGap π loss₁ ≠ M.contextualGap π loss₀ := by
  classical
  let loss₀ : S → A → Bool := fun _ _ => false
  let loss₁ : S → A → Bool := fun s a => decide (s ∈ E ∧ a = a₀)
  have hlog : ∀ z, M.logLaw π loss₀ z = M.logLaw π loss₁ z := by
    rintro ⟨s, a, b⟩
    by_cases h : s ∈ E ∧ a = a₀
    · obtain ⟨hs, rfl⟩ := h
      simp [logLaw, hoverlap s hs]
    · have hl : loss₁ s a = false := decide_eq_false_iff_not.mpr h
      simp only [logLaw, loss₀, hl]
  have hgap : M.contextualGap π loss₁ - M.contextualGap π loss₀ =
      -(∑ s, M.initial s * π.prob 0 s a₀) * (∑ s ∈ E, M.initial s) := by
    have hfirst : (∑ s, ∑ a, M.initial s * π.prob 0 s a *
        if loss₁ s a then 1 else 0) = 0 := by
      apply sum_eq_zero
      intro s _
      apply sum_eq_zero
      intro a _
      by_cases h : s ∈ E ∧ a = a₀
      · obtain ⟨hs, rfl⟩ := h
        simp [hoverlap s hs]
      · simp [loss₁, h]
    have hsecond : (∑ s, ∑ a, M.initial s * (∑ x, M.initial x * π.prob 0 x a) *
        if loss₁ s a then 1 else 0) =
        (∑ s ∈ E, M.initial s) * (∑ x, M.initial x * π.prob 0 x a₀) := by
      simp only [loss₁, decide_eq_true_eq, mul_ite, mul_one, mul_zero]
      simp_rw [ite_and]
      simp only [sum_ite_irrel, sum_ite_eq', mem_univ, ite_true]
      simp only [sum_const_zero]
      rw [← sum_filter]
      simp only [filter_mem_eq_inter, univ_inter]
      rw [sum_mul]
    simp only [contextualGap, loss₀, Bool.false_eq_true, ite_false, mul_zero, sum_const_zero]
    rw [hfirst, hsecond]
    ring
  refine ⟨loss₀, loss₁, ?_, hgap, ?_⟩
  · intro T z
    exact prod_congr rfl fun t _ => hlog (z t)
  · intro heq
    have hneg : -(∑ s, M.initial s * π.prob 0 s a₀) * (∑ s ∈ E, M.initial s) < 0 :=
      mul_neg_of_neg_of_pos (neg_neg_of_pos hmarginal) hmass
    rw [heq, sub_self] at hgap
    linarith

end Cslib.Probability.AdaptivePolicy.FiniteMDP
