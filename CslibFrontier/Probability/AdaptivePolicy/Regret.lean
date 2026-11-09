/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.AdaptivePolicy.Information
import Mathlib.Tactic

/-!
# Static allocation, adaptivity gaps and information budgets

[Aldridge2027], Corollaries 3.7, 4.4 and 4.5 (PDF p. 4).
Costs are minimized. Optimal policies are quantified by their actual cost against
all Markov policies, or all state-independent Markov policies, respectively.
No optimality or cost bound is inferred from a policy's name. Theorems allow
any optimizers, without requiring uniqueness or supplying a desired gap bound.

## Main results

* `FiniteMDP.regret_decomposition`: covariance, static allocation and adaptivity gap.
* `FiniteMDP.optimal_gap_le_information`: information used by an optimal policy bounds the gap.
* `FiniteMDP.rate_value_tradeoff`: unit-cost bound under individual information budgets.
* `FiniteMDP.constant_rate_value_tradeoff`: the exact triangular horizon constant.
-/

public section
noncomputable section
open Finset
namespace Cslib.Probability.AdaptivePolicy

namespace MarkovPolicy
variable {S A : Type*} [Fintype S] [Fintype A]

/-- A policy ignores the state, at every time. -/
def IsOpenLoop (μ : MarkovPolicy S A) : Prop :=
  ∀ t s s' a, μ.prob t s a = μ.prob t s' a

end MarkovPolicy

namespace FiniteMDP
variable {S A : Type*} [Fintype S] [Fintype A]
variable (M : FiniteMDP S A)

/-- The marginal policy is state independent, including off-support states. -/
theorem openLoop_isOpenLoop (π : MarkovPolicy S A) : (M.openLoop π).IsOpenLoop :=
  fun _ _ _ _ => rfl

/-- Optimality among all randomized Markov policies for a fixed horizon. -/
def IsOptimal (π : MarkovPolicy S A) (H : ℕ) : Prop :=
  ∀ μ, M.totalCost π H ≤ M.totalCost μ H

/-- Optimality among all state-independent randomized Markov policies. -/
def IsOptimalOpenLoop (ν : MarkovPolicy S A) (H : ℕ) : Prop :=
  ν.IsOpenLoop ∧ ∀ μ, μ.IsOpenLoop → M.totalCost ν H ≤ M.totalCost μ H

/-- Corollary 3.6: under action-independent transitions, immediate-cost
covariances give the exact adaptivity cost. -/
theorem exogenous_covariance_characterization (π : MarkovPolicy S A) (H : ℕ)
    (P : ℕ → S → S → ℝ)
    (hP : ∀ t s a s', M.transition t s a s' = P t s s') :
    M.totalCost π H - M.totalCost (M.openLoop π) H =
      ∑ t ∈ range H, M.traceCovariance π t (M.cost t) := by
  rw [M.covariance_characterization]
  apply sum_congr rfl
  intro t _
  let g : S → ℝ := fun s => ∑ s', P t s s' *
    M.value (M.openLoop π) (H-(t+1)) (t+1) s'
  have heq : (fun s a => M.actionValue (M.openLoop π) H t s a - g s) = M.cost t := by
    funext s a
    simp [actionValue, hP, g]
  rw [← M.traceCovariance_sub_state π t (M.actionValue (M.openLoop π) H t) g, heq]

/-- Corollary 3.7: the exact three-part regret decomposition, with both
static allocation and the problem's adaptivity gap nonnegative. -/
theorem regret_decomposition (π πstar νstar : MarkovPolicy S A) (H : ℕ)
    (hπ : M.IsOptimal πstar H) (hν : M.IsOptimalOpenLoop νstar H) :
    M.totalCost π H - M.totalCost πstar H =
      (∑ t ∈ range H, M.traceCovariance π t (M.actionValue (M.openLoop π) H t)) +
      (M.totalCost (M.openLoop π) H - M.totalCost νstar H) +
      (M.totalCost νstar H - M.totalCost πstar H) ∧
    0 ≤ M.totalCost (M.openLoop π) H - M.totalCost νstar H ∧
    0 ≤ M.totalCost νstar H - M.totalCost πstar H := by
  refine ⟨?_, sub_nonneg.mpr (hν.2 _ (M.openLoop_isOpenLoop π)), sub_nonneg.mpr (hπ _)⟩
  rw [← M.covariance_characterization]
  ring

/-- The adaptivity gap is at most the negative adaptivity cost of any optimizer.
Equality holds exactly when its marginal is itself open-loop optimal. -/
theorem optimal_gap_le_neg_adaptivity (πstar νstar : MarkovPolicy S A) (H : ℕ)
    (hν : M.IsOptimalOpenLoop νstar H) :
    M.totalCost νstar H - M.totalCost πstar H ≤
      -(M.totalCost πstar H - M.totalCost (M.openLoop πstar) H) ∧
    (M.totalCost νstar H - M.totalCost πstar H =
      -(M.totalCost πstar H - M.totalCost (M.openLoop πstar) H) ↔
      M.IsOptimalOpenLoop (M.openLoop πstar) H) := by
  have hb := hν.2 _ (M.openLoop_isOpenLoop πstar)
  constructor
  · linarith
  · constructor
    · intro heq
      refine ⟨M.openLoop_isOpenLoop πstar, fun μ hμ => ?_⟩
      have := hν.2 μ hμ
      linarith
    · intro hm
      have := hm.2 νstar hν.1
      linarith

/-- Corollary 4.4: the information used by an optimal policy bounds the
additive adaptivity gap. In fact the inequality holds for every policy. -/
theorem optimal_gap_le_information (πstar νstar : MarkovPolicy S A) (H : ℕ)
    (hν : M.IsOptimalOpenLoop νstar H) :
    M.totalCost νstar H - M.totalCost πstar H ≤
      ∑ t ∈ range H, M.actionSpan πstar t (M.actionValue (M.openLoop πstar) H t) *
        Real.sqrt (M.mutualInformation πstar t / 2) := by
  exact (M.optimal_gap_le_neg_adaptivity πstar νstar H hν).1.trans
    ((neg_le_abs _).trans (M.information_bound πstar H))

/-- A zero-information optimizer forces zero adaptivity gap. -/
theorem optimal_gap_eq_zero (πstar νstar : MarkovPolicy S A) (H : ℕ)
    (hπ : M.IsOptimal πstar H) (hν : M.IsOptimalOpenLoop νstar H)
    (hI : ∀ t < H, M.mutualInformation πstar t = 0) :
    M.totalCost νstar H - M.totalCost πstar H = 0 := by
  have hb := M.optimal_gap_le_information πstar νstar H hν
  have hz : (∑ t ∈ range H, M.actionSpan πstar t (M.actionValue (M.openLoop πstar) H t) *
      Real.sqrt (M.mutualInformation πstar t / 2)) = 0 := by
    apply sum_eq_zero
    intro t ht
    simp [hI t (mem_range.mp ht)]
  rw [hz] at hb
  exact le_antisymm hb (sub_nonneg.mpr (hπ _))

/-- Corollary 4.5: individual information budgets in nats, unit immediate
costs, and the exact remaining-horizon coefficients. -/
theorem rate_value_tradeoff (π νstar : MarkovPolicy S A) (H : ℕ)
    (hν : M.IsOptimalOpenLoop νstar H)
    (hc : ∀ t s a, 0 ≤ M.cost t s a ∧ M.cost t s a ≤ 1)
    (R : ℕ → ℝ) (hR : ∀ t < H, M.mutualInformation π t ≤ R t) :
    M.totalCost νstar H - M.totalCost π H ≤
      ∑ t ∈ range H, (H-t : ℕ) * Real.sqrt (R t / 2) := by
  apply (M.optimal_gap_le_information π νstar H hν).trans
  apply sum_le_sum
  intro t ht
  have hspan := M.actionSpan_le π (t := t) (q := M.actionValue (M.openLoop π) H t)
    (Nat.cast_nonneg (H-t)) (fun s a _ _ => M.actionValue_unit_bounds _ hc (mem_range.mp ht) s a)
  exact mul_le_mul hspan (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
    (hR t (mem_range.mp ht)) (by norm_num))) (Real.sqrt_nonneg _)
      (Nat.cast_nonneg _)

/-- Corollary 4.5: a constant budget has the sharp stated horizon coefficient
`H * (H+1) / 2`, rather than a coarser quadratic bound. -/
theorem constant_rate_value_tradeoff (π νstar : MarkovPolicy S A) (H : ℕ)
    (hν : M.IsOptimalOpenLoop νstar H)
    (hc : ∀ t s a, 0 ≤ M.cost t s a ∧ M.cost t s a ≤ 1)
    (R : ℝ) (hR : ∀ t < H, M.mutualInformation π t ≤ R) :
    M.totalCost νstar H - M.totalCost π H ≤
      (H:ℝ) * (H+1) / 2 * Real.sqrt (R / 2) := by
  have h := M.rate_value_tradeoff π νstar H hν hc (fun _ => R) hR
  have hsum : (∑ t ∈ range H, ((H-t : ℕ):ℝ)) = (H:ℝ) * (H+1) / 2 := by
    clear h hν hR
    induction H with
    | zero => simp
    | succ H ih =>
      rw [sum_range_succ]
      have hs : (∑ t ∈ range H, ((H+1-t : ℕ):ℝ)) =
          (∑ t ∈ range H, ((H-t : ℕ):ℝ)) + H := by
        calc
          _ = ∑ t ∈ range H, (((H-t : ℕ):ℝ) + 1) := by
            apply sum_congr rfl
            intro t ht
            have he : H+1-t = (H-t)+1 := by have := mem_range.mp ht; omega
            rw [he, Nat.cast_add, Nat.cast_one]
          _ = _ := by simp [sum_add_distrib]
      rw [hs, ih]
      have he : H+1-H = 1 := by omega
      rw [he]
      push_cast
      ring
  simpa only [← sum_mul, hsum] using h

end FiniteMDP
end Cslib.Probability.AdaptivePolicy
