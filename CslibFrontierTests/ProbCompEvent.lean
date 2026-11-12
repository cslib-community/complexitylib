/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Languages.Probabilistic.Oracle
public import CslibFrontier.Probability.PMF.TwoBranch

/-! The shared PMF success rule applies directly to probabilistic-program clients, without a
graph-algorithm import or a second ProbComp-specific probability API. -/

public section

namespace CslibFrontierTests.ProbCompEvent

open Cslib
open scoped ENNReal

/-- A uniform Boolean program succeeds with probability one half. -/
theorem coin_hit :
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
  have h := Probability.PMF.two_branch_hit_prob_ge (ProbComp.uniform Bool).eval
    (fun a => (if a then pure false else ProbComp.uniform Bool).eval) (fun a b => a || b)
    {true} {true} (s := 2) (by decide) coin_hit (by
      intro a _ ha b _
      change a = true at ha
      subst a
      simp) (by
      intro a _ ha
      have hfalse : a = false := by cases a <;> simp_all
      subst a
      change (1 : ℝ≥0∞) / 2 ≤ ((ProbComp.uniform Bool).eval.map id).toOuterMeasure {true}
      rw [PMF.map_id]
      exact coin_hit)
  simpa only [ProbComp.eval_bind, ProbComp.eval_pure, ← PMF.bind_pure_comp,
    Function.comp_def, Nat.reduceAdd, Nat.cast_ofNat] using h

-- At `s = 1`, a certain first success is retained through any later program. The later
-- program need not succeed when given the unsupported first result `false`.
example (later : Bool → ProbComp Bool) :
    (1 : ℝ≥0∞) ≤ (do
      let a ← (pure true : ProbComp Bool)
      let b ← later a
      pure (a || b)).eval.toOuterMeasure {true} := by
  have h := Probability.PMF.two_branch_hit_prob_ge (PMF.pure true)
    (fun a => (later a).eval) (fun a b => a || b)
    {true} {true} (s := 1) (by decide) (by simp) (by
      intro a _ ha b _
      change a = true at ha
      subst a
      simp) (by
      intro a ha hmiss
      have ha' : a = true := (PMF.mem_support_pure_iff _ _).mp ha
      exact False.elim (hmiss ha'))
  have htwo : (2 : ℝ≥0∞) / 2 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
  simpa only [show ((1 + 1 : ℕ) : ℝ≥0∞) = 2 by norm_num, htwo,
    ProbComp.eval_bind, ProbComp.eval_pure, ← PMF.bind_pure_comp, Function.comp_def] using h

end CslibFrontierTests.ProbCompEvent
