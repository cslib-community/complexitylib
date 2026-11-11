/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite-horizon Markov-policy covariance identity

[Aldridge2027], Lemma 3.3 and Theorem 3.4, PDF p. 3, equations (3)–(4).
Time starts at zero. Finite state and action spaces carry nonnegative, normalized
real probability tables; transitions may depend on both state and action.
`stateLaw` is the forward law under the policy being evaluated. `value` and
`actionValue` use backward evaluation under the comparison policy, with zero
terminal cost. The open-loop marginal is computed from the original policy's
forward law, rather than recomputed under the open-loop trajectory law.

## Main results

* `performance_difference`: the finite-horizon performance-difference identity.
* `covariance_characterization`: the general endogenous-dynamics covariance identity.

The information bound, its sharpness, and the auditing sample-complexity theorems
are separate claims and are not supplied by this identity.
-/

public section
noncomputable section
open Finset
namespace Cslib.Probability.AdaptivePolicy
variable {S A : Type*} [Fintype S] [Fintype A]

/-- A finite, time-inhomogeneous Markov decision process with real costs. -/
structure FiniteMDP (S A : Type*) [Fintype S] [Fintype A] where
  /-- Initial state law. -/
  initial : S → ℝ
  /-- Nonnegative initial probabilities. -/
  initial_nonneg : ∀ s, 0 ≤ initial s
  /-- Total initial probability. -/
  initial_sum : ∑ s, initial s = 1
  /-- Controlled transition probabilities. -/
  transition : ℕ → S → A → S → ℝ
  /-- Nonnegative transition probabilities. -/
  transition_nonneg : ∀ t s a s', 0 ≤ transition t s a s'
  /-- Every conditional transition law is normalized. -/
  transition_sum : ∀ t s a, ∑ s', transition t s a s' = 1
  /-- Immediate cost. -/
  cost : ℕ → S → A → ℝ

/-- A randomized Markov policy, with independent conditional action sampling. -/
structure MarkovPolicy (S A : Type*) [Fintype S] [Fintype A] where
  /-- Conditional action probabilities. -/
  prob : ℕ → S → A → ℝ
  /-- Nonnegative conditional probabilities. -/
  nonneg : ∀ t s a, 0 ≤ prob t s a
  /-- Every conditional action law is normalized. -/
  sum_prob : ∀ t s, ∑ a, prob t s a = 1

namespace FiniteMDP
variable (M : FiniteMDP S A)

/-- The actual forward state law, including endogenous transitions. -/
@[expose] def stateLaw (π : MarkovPolicy S A) : ℕ → S → ℝ
  | 0 => M.initial
  | t + 1 => fun s' => ∑ s, ∑ a,
      stateLaw π t s * π.prob t s a * M.transition t s a s'

/-- Backward expected cost with `n` steps remaining, starting at time `t`. -/
@[expose] def value (π : MarkovPolicy S A) : ℕ → ℕ → S → ℝ
  | 0, _t, _s => 0
  | n + 1, t, s => ∑ a, π.prob t s a *
      (M.cost t s a + ∑ s', M.transition t s a s' * value π n (t + 1) s')

/-- Expected total cost, evaluated from the actual forward state laws. -/
@[expose] def totalCost (π : MarkovPolicy S A) (H : ℕ) : ℝ :=
  ∑ t ∈ range H, ∑ s, ∑ a, M.stateLaw π t s * π.prob t s a * M.cost t s a

/-- The baseline action value at time `t` for horizon `H`. -/
@[expose] def actionValue (μ : MarkovPolicy S A) (H t : ℕ) (s : S) (a : A) : ℝ :=
  M.cost t s a + ∑ s', M.transition t s a s' * M.value μ (H - (t + 1)) (t + 1) s'

/-- Forward laws are nonnegative. -/
theorem stateLaw_nonneg (π : MarkovPolicy S A) (t : ℕ) (s : S) :
    0 ≤ M.stateLaw π t s := by
  induction t generalizing s with
  | zero => exact M.initial_nonneg s
  | succ t ih =>
    exact sum_nonneg fun s _ => sum_nonneg fun a _ =>
      mul_nonneg (mul_nonneg (ih s) (π.nonneg t s a)) (M.transition_nonneg t s a _)

/-- Forward laws remain normalized. -/
theorem stateLaw_sum (π : MarkovPolicy S A) (t : ℕ) :
    ∑ s, M.stateLaw π t s = 1 := by
  induction t with
  | zero => exact M.initial_sum
  | succ t ih =>
    simp only [stateLaw]
    rw [sum_comm]
    simp only [sum_comm (γ := S), ← mul_sum, M.transition_sum, mul_one,
      π.sum_prob, ih]

/-- State-independent action probabilities with the original policy's time marginals. -/
@[expose] def openLoop (π : MarkovPolicy S A) : MarkovPolicy S A where
  prob t _s a := ∑ s, M.stateLaw π t s * π.prob t s a
  nonneg t _s a := sum_nonneg fun s _ => mul_nonneg (M.stateLaw_nonneg π t s) (π.nonneg t s a)
  sum_prob t _s := by
    rw [sum_comm]
    simp only [← mul_sum, π.sum_prob, mul_one, M.stateLaw_sum]

private theorem potential_step (π : MarkovPolicy S A) (V : ℕ → S → ℝ) (t : ℕ) :
    (∑ s, M.stateLaw π t s *
      ((∑ a, π.prob t s a * (M.cost t s a +
        ∑ s', M.transition t s a s' * V (t + 1) s')) - V t s)) =
      (∑ s, ∑ a, M.stateLaw π t s * π.prob t s a * M.cost t s a) +
      (∑ s, M.stateLaw π (t + 1) s * V (t + 1) s) -
      ∑ s, M.stateLaw π t s * V t s := by
  simp only [stateLaw, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib,
    mul_sum, sum_mul, mul_assoc]
  congr 1
  congr 1
  conv_rhs =>
    rw [sum_comm]
    arg 2
    ext s
    rw [sum_comm]

private theorem potential_sum (π : MarkovPolicy S A) (V : ℕ → S → ℝ)
    (H : ℕ) (hV : ∀ s, V H s = 0) :
    (∑ t ∈ range H, ∑ s, M.stateLaw π t s *
      ((∑ a, π.prob t s a * (M.cost t s a +
        ∑ s', M.transition t s a s' * V (t + 1) s')) - V t s)) =
      M.totalCost π H - ∑ s, M.initial s * V 0 s := by
  simp_rw [M.potential_step, sum_sub_distrib, sum_add_distrib]
  have ht : (∑ t ∈ range H, ((∑ s, M.stateLaw π (t + 1) s * V (t + 1) s) -
      ∑ s, M.stateLaw π t s * V t s)) = - ∑ s, M.initial s * V 0 s := by
    have h := sum_range_sub (fun t => ∑ s, M.stateLaw π t s * V t s) H
    simpa [hV, stateLaw] using h
  unfold totalCost
  rw [sum_sub_distrib] at ht
  linarith

private theorem value_bellman (μ : MarkovPolicy S A) {H t : ℕ} (ht : t < H) (s : S) :
    M.value μ (H - t) t s = ∑ a, μ.prob t s a * M.actionValue μ H t s a := by
  have h : H - t = (H - (t + 1)) + 1 := by omega
  rw [h, value]
  rfl

/-- Forward total cost equals the initial expectation of backward evaluation. -/
theorem totalCost_eq_value (μ : MarkovPolicy S A) (H : ℕ) :
    M.totalCost μ H = ∑ s, M.initial s * M.value μ H 0 s := by
  have h := M.potential_sum μ (fun t => M.value μ (H - t) t) H (by simp [value])
  have hz : (∑ t ∈ range H, ∑ s, M.stateLaw μ t s *
      ((∑ a, μ.prob t s a * M.actionValue μ H t s a) - M.value μ (H - t) t s)) = 0 := by
    apply sum_eq_zero
    intro t ht
    apply sum_eq_zero
    intro s _
    rw [M.value_bellman μ (mem_range.mp ht), sub_self, mul_zero]
  change (∑ t ∈ range H, ∑ s, M.stateLaw μ t s *
    ((∑ a, μ.prob t s a * M.actionValue μ H t s a) - M.value μ (H - t) t s)) = _ at h
  simp only [Nat.sub_zero] at h
  linarith

/-- [Aldridge2027], Lemma 3.3: arbitrary comparison Markov policies. -/
theorem performance_difference (π μ : MarkovPolicy S A) (H : ℕ) :
    M.totalCost π H - M.totalCost μ H =
      ∑ t ∈ range H, ∑ s, M.stateLaw π t s *
        ((∑ a, π.prob t s a * M.actionValue μ H t s a) - M.value μ (H - t) t s) := by
  rw [M.totalCost_eq_value μ H]
  exact (M.potential_sum π (fun t => M.value μ (H - t) t) H (by simp [value])).symm

/-- Trace covariance, with expectation under the evaluated policy's state law. -/
@[expose] def traceCovariance (π : MarkovPolicy S A) (t : ℕ) (q : S → A → ℝ) : ℝ :=
  (∑ s, M.stateLaw π t s * ∑ a, π.prob t s a * q s a) -
    ∑ a, (∑ s, M.stateLaw π t s * q s a) *
      (∑ s, M.stateLaw π t s * π.prob t s a)

/-- [Aldridge2027], Theorem 3.4, equation (3), for every finite horizon and Markov policy.
The baseline values incorporate all action-dependent future transitions. -/
theorem covariance_characterization (π : MarkovPolicy S A) (H : ℕ) :
    M.totalCost π H - M.totalCost (M.openLoop π) H =
      ∑ t ∈ range H, M.traceCovariance π t (M.actionValue (M.openLoop π) H t) := by
  rw [M.performance_difference]
  apply sum_congr rfl
  intro t ht
  simp_rw [M.value_bellman (M.openLoop π) (mem_range.mp ht)]
  change (∑ s, M.stateLaw π t s *
    ((∑ a, π.prob t s a * M.actionValue (M.openLoop π) H t s a) -
      ∑ a, (∑ x, M.stateLaw π t x * π.prob t x a) *
        M.actionValue (M.openLoop π) H t s a)) = _
  simp only [traceCovariance, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  calc
    _ = ∑ s, (∑ x, M.stateLaw π t x * π.prob t x a) *
        (M.stateLaw π t s * M.actionValue (M.openLoop π) H t s a) := by
      apply sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [← mul_sum, ← mul_sum]; ring

/-- The covariance is the expectation gap between the joint state/action law and
its product of marginals; no change of the forward state law is made. -/
theorem traceCovariance_eq_joint_sub_product (π : MarkovPolicy S A) (t : ℕ)
    (q : S → A → ℝ) :
    M.traceCovariance π t q =
      (∑ s, ∑ a, (M.stateLaw π t s * π.prob t s a) * q s a) -
        ∑ s, ∑ a, (M.stateLaw π t s *
          (∑ x, M.stateLaw π t x * π.prob t x a)) * q s a := by
  unfold traceCovariance
  congr 1
  · simp only [mul_sum, mul_assoc]
  · simp only [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro a _
    ring

/-- [Aldridge2027], Theorem 3.4, equation (4). -/
theorem joint_product_characterization (π : MarkovPolicy S A) (H : ℕ) :
    M.totalCost π H - M.totalCost (M.openLoop π) H =
      ∑ t ∈ range H,
        ((∑ s, ∑ a, (M.stateLaw π t s * π.prob t s a) *
          M.actionValue (M.openLoop π) H t s a) -
        ∑ s, ∑ a, (M.stateLaw π t s *
          (∑ x, M.stateLaw π t x * π.prob t x a)) *
            M.actionValue (M.openLoop π) H t s a) := by
  rw [M.covariance_characterization]
  exact sum_congr rfl fun t _ => M.traceCovariance_eq_joint_sub_product π t _

/-- State-only baselines cancel from each covariance summand. -/
theorem traceCovariance_sub_state (π : MarkovPolicy S A) (t : ℕ)
    (q : S → A → ℝ) (g : S → ℝ) :
    M.traceCovariance π t (fun s a => q s a - g s) = M.traceCovariance π t q := by
  simp only [traceCovariance, mul_sub, sum_sub_distrib, sub_mul]
  simp only [← mul_sum, ← sum_mul, π.sum_prob]
  rw [sum_comm (f := fun a s => _)]
  simp only [← mul_sum, π.sum_prob, mul_one, M.stateLaw_sum]
  ring_nf

end FiniteMDP
end Cslib.Probability.AdaptivePolicy
