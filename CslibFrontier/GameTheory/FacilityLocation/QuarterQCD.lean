/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A counterexample to quarter-QCD

The circle is represented by arclength coordinates in $[0,8)$, with the shorter-arc
metric. For three ordered, distinct reports, `weights` uses the actual opposite arcs:
the middle report has the wrapping arc, and the two outer reports have nonwrapping arcs.
The threshold is the square of a quarter circumference. The expected costs are computed
from these weights, rather than from a separately specified lottery.

## Main results

`quarterQCD_counterexample` proves the improving report and the approximation violation
in [RogowskiDziubinski2027], Remark P.1, PDF pp. 50–51. This is a counterexample to
quarter-QCD, not a formalization of the paper's mechanism search or its other results.
The source's unit circle is scaled by eight, so the weight floor is four.
The original rule is [Meir2019Circle], Definition 3.1;
its strategyproofness and ratio claims are Theorem 3.2 and Proposition 3.3.

## Main definitions

* `circleDist`, `weights`, `cost`: canonical shorter-arc distance and the actual normalized rule.
* `socialCost`, `Strategyproof`: facility cost and the ordered-report incentive contract.

## References

* [RogowskiDziubinski2027], Remark P.1, PDF pp. 50–51.
* [Meir2019Circle], Definition 3.1, Theorem 3.2 and Proposition 3.3.
-/

public section

namespace Cslib.FacilityLocation.QuarterQCD

/-- Shorter-arc distance for canonical coordinates on the circumference-eight circle. -/
@[expose] def circleDist (a b : ℝ) : ℝ := min |a - b| (8 - |a - b|)

/-- The three opposite-arc weights, in increasing report order. -/
@[expose] def weights (a b c : ℝ) : ℝ × ℝ × ℝ :=
  (max ((c - b) ^ 2) 4, max ((8 - (c - a)) ^ 2) 4, max ((b - a) ^ 2) 4)

/-- Expected true-location cost of the normalized quarter-QCD lottery. -/
@[expose] noncomputable def cost (a b c t : ℝ) : ℝ :=
  let w := weights a b c
  (w.1 * circleDist a t + w.2.1 * circleDist b t + w.2.2 * circleDist c t) /
    (w.1 + w.2.1 + w.2.2)

/-- Social cost of placing the facility at `t`. -/
@[expose] def socialCost (a b c t : ℝ) : ℝ :=
  circleDist a t + circleDist b t + circleDist c t

/-- Expected social cost of the lottery, evaluated on the true profile. -/
@[expose] noncomputable def expectedSocialCost (a b c : ℝ) : ℝ :=
  cost a b c a + cost a b c b + cost a b c c

/-- Strategyproofness restricted to ordered distinct reports already fails. -/
@[expose] def Strategyproof : Prop :=
  ∀ a a' b c : ℝ, 0 ≤ a → a < b → b < c → c < 8 →
    0 ≤ a' → a' < b → cost a b c a ≤ cost a' b c a

/-- The actual lotteries have the stated weights and true-location costs. -/
theorem witness_costs :
    weights 0 3 4 = (4, 16, 9) ∧ weights 1 3 4 = (4, 25, 4) ∧
    cost 0 3 4 0 = 84 / 29 ∧ cost 1 3 4 0 = 95 / 33 ∧
    cost 0 3 4 0 - cost 1 3 4 0 = 17 / 957 := by
  norm_num [weights, cost, circleDist]

/-- Every canonical circle location has social cost at least four; location three attains it. -/
theorem witness_optimum :
    socialCost 0 3 4 3 = 4 ∧ ∀ t : ℝ, 0 ≤ t → t < 8 → 4 ≤ socialCost 0 3 4 t := by
  constructor
  · norm_num [socialCost, circleDist]
  · intro t ht ht8
    have h3 : 0 ≤ circleDist 3 t := by
      apply le_min (abs_nonneg _)
      have : |3 - t| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have h04 : 4 ≤ circleDist 0 t + circleDist 4 t := by
      rcases le_total t 4 with h | h
      · simp only [circleDist, zero_sub, abs_neg, abs_of_nonneg ht,
          abs_of_nonneg (show 0 ≤ 4 - t by linarith), min_def]
        split_ifs <;> linarith
      · simp only [circleDist, zero_sub, abs_neg, abs_of_nonneg ht,
          abs_of_nonpos (show 4 - t ≤ 0 by linarith), min_def]
        split_ifs <;> linarith
    unfold socialCost
    linarith

/-- Remark P.1: the published quarter-QCD rule is manipulable and exceeds factor $7/6$. -/
theorem quarterQCD_counterexample :
    ¬ Strategyproof ∧
    cost 1 3 4 0 < cost 0 3 4 0 ∧
    expectedSocialCost 0 3 4 / 4 = 137 / 116 ∧
    (7 : ℝ) / 6 < expectedSocialCost 0 3 4 / 4 := by
  have hc : cost 1 3 4 0 < cost 0 3 4 0 := by norm_num [cost, weights, circleDist]
  refine ⟨?_, hc, ?_, ?_⟩
  · intro h
    have := h 0 1 3 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    linarith
  · norm_num [expectedSocialCost, cost, weights, circleDist]
  · norm_num [expectedSocialCost, cost, weights, circleDist]

end Cslib.FacilityLocation.QuarterQCD
