/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.BestOf
import CslibFrontier.Probability.PMF.Uniform

/-! Nonvacuity checks for best-of-`k` selection of membership-query learners: a learner that
outputs the worst possible hypothesis half of the time is boosted with explicit parameters. -/

namespace CslibFrontierTests.QueryLearnerBestOf

open Cslib Cslib.MachineLearning Cslib.MachineLearning.UniformLearning
  Cslib.MachineLearning.UniformLearning.QueryLearner Cslib.Probability MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weak learner making no queries: on the seed `true` it outputs the target `f`, and on the
seed `false` its negation, which has error `1`. -/
def weak (f : (ι → Bool) → Bool) : QueryLearner ι Bool :=
  fun b => DecisionTree.leaf (if b then f else fun y => !f y)

/-- The weak learner outputs a perfect hypothesis with probability `1/2`. -/
theorem weak_learns (f : (ι → Bool) → Bool) :
    (weak f).Learns (PMF.uniformOfFintype Bool) {f} 0 (1 / 2) := by
  rw [QueryLearner.learns_iff]
  rintro _ rfl
  calc _ ≤ (PMF.uniformOfFintype Bool).toOuterMeasure {false} := by
        refine measure_mono fun b hb => ?_
        cases b
        · rfl
        · simp [weak] at hb
    _ = ENNReal.ofReal (1 / 2) := by
        rw [← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _),
          PMF.toOuterMeasure_uniformOfFintype_toReal]
        simp only [Set.mem_singleton_iff, Finset.filter_eq', Finset.mem_univ, ite_true,
          Finset.card_singleton, Fintype.card_bool]
        norm_num

/-- Selection boosts the weak learner: `6` runs and `1504` sample points give a hypothesis with
error at most `1/4` with probability at least `1/2`. -/
example (f : (ι → Bool) → Bool) :
    (bestOf (weak f) 6 1504).Learns (bestOfSeed (PMF.uniformOfFintype Bool) 6 1504) {f}
      (1 / 2 - 1 / 2 / 2) (1 / 2) := by
  refine learns_bestOf_of_weak (γ := 1 / 2) (p := 1 / 2)
    ((weak_learns f).mono subset_rfl (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) ?_ ?_
  · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 / (1 / 2) by norm_num)
    norm_num at this ⊢
    linarith
  · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 * 6 / (1 / 2) by norm_num)
    norm_num at this ⊢
    linarith

/-- Best-of-`k` selection over the simulation of a learner from `m` random examples makes at
most `k * m + t` queries. -/
example {m k t : ℕ} [NeZero k] (A : PACLearning.Learner (ι → Bool) Bool m) :
    (bestOf (ofLearner A) k t).QueriesAtMost (k * m + t) :=
  queriesAtMost_bestOf (queriesAtMost_ofLearner A)

/-- If every run outputs a hypothesis in `S`, for instance the functions of small circuit
complexity, so does best-of-`k` selection. -/
example {Ω : Type*} {k t : ℕ} [NeZero k] (A : QueryLearner ι Ω) (S : Set ((ι → Bool) → Bool))
    (f : (ι → Bool) → Bool) (hS : ∀ ω, (A ω).eval f ∈ S) (ω : Fin k → Ω)
    (x : Fin t → ι → Bool) : (bestOf A k t (ω, x)).eval f ∈ S := by
  obtain ⟨j, hj⟩ := exists_eval_bestOf_eq A k t f ω x
  exact hj ▸ hS _

end CslibFrontierTests.QueryLearnerBestOf
