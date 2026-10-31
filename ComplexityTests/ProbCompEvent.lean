/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Languages.Probabilistic.Event

/-! Shared probabilistic-program success bounds, without a graph-algorithm import. -/

namespace ComplexityTests.ProbCompEvent

open Cslib
open scoped ENNReal

private theorem coin_hit :
    (1 : ℝ≥0∞) / 2 ≤ (ProbComp.uniform Bool).eval.toOuterMeasure {true} := by
  rw [ProbComp.eval_uniform, PMF.toOuterMeasure_apply_singleton,
    Probability.PMF.uniformOfFintype_apply]
  norm_num

-- The first success skips the second draw; a fresh coin recovers after failure. The
-- continuation depends on the first result, and the shared bound gives at least `2 / 3`.
example : (2 : ℝ≥0∞) / 3 ≤ (do
    let a ← ProbComp.uniform Bool
    let b ← (if a then pure false else ProbComp.uniform Bool)
    pure (a || b)).eval.toOuterMeasure {true} := by
  refine ProbComp.two_branch_hit_prob_ge (ProbComp.uniform Bool)
    (fun a => if a then pure false else ProbComp.uniform Bool) (fun a b => a || b)
    {true} {true}
    (s := 2) (by decide) coin_hit ?_ ?_
  · intro a _ ha b _
    change a = true at ha
    subst a
    simp
  · intro a _ ha
    have hfalse : a = false := by cases a <;> simp_all
    subst a
    change (1 : ℝ≥0∞) / 2 ≤ ((ProbComp.uniform Bool).eval.map id).toOuterMeasure {true}
    rw [PMF.map_id]
    exact coin_hit

-- At `s = 1`, a certain first success is retained through any later program. The later
-- program need not succeed when given the unsupported first result `false`.
example (later : Bool → ProbComp Bool) :
    (1 : ℝ≥0∞) ≤ (do
      let a ← (pure true : ProbComp Bool)
      let b ← later a
      pure (a || b)).eval.toOuterMeasure {true} := by
  have h := ProbComp.two_branch_hit_prob_ge (pure true) later (fun a b => a || b)
    {true} {true} (s := 1) (by decide) (by simp) (by
      intro a _ ha b _
      change a = true at ha
      subst a
      simp) (by
      intro a ha hmiss
      have ha' : a = true := OracleComp.eq_of_mem_supportWith_pure ha
      exact False.elim (hmiss ha'))
  have htwo : (2 : ℝ≥0∞) / 2 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
  simpa only [show ((1 + 1 : ℕ) : ℝ≥0∞) = 2 by norm_num, htwo] using h

end ComplexityTests.ProbCompEvent
