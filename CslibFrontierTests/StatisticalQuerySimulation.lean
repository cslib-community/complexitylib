/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.StatisticalQuery.LowDegree
import CslibFrontier.MachineLearning.StatisticalQuery.Simulation
import CslibFrontierTests.StatisticalQuery

/-! Checks for simulating statistical queries from examples and for the low-degree algorithm: the
one-query learner of `CslibFrontierTests.StatisticalQuery` run on concrete blocks of examples, its
simulation as a PAC learner from `40` examples, the uniform realizable family as a special case,
the low-degree algorithm on the parities of at most one of three bits, and the PAC learner it
gives. -/

namespace ComplexityTests.StatisticalQuerySimulation

open Cslib Cslib.MachineLearning Cslib.MachineLearning.StatisticalQuery Cslib.Probability
open ComplexityTests.StatisticalQuery Finset
open scoped NNReal

/-! ### Running a learner on examples -/

/-- On a block of two examples labelled `true` the empirical mean of the sign query is `-1`, and
the one-query learner returns the constant `true`. -/
example : simulate 1 (fun _ _ => ((), true) : Fin 1 → Fin 2 → Unit × Bool) signLearner =
    fun _ => true := by
  have he : empirical signQuery (fun _ => ((), true) : Fin 2 → Unit × Bool) = -1 := by
    simp [empirical, signQuery]
  rw [signLearner, simulate_query_bind, he, simulate_pure]
  funext
  simp

/-- On a block of examples labelled `false` it returns the constant `false`: the simulation
depends on the examples. -/
example : simulate 1 (fun _ _ => ((), false) : Fin 1 → Fin 2 → Unit × Bool) signLearner =
    fun _ => false := by
  have he : empirical signQuery (fun _ => ((), false) : Fin 2 → Unit × Bool) = 1 := by
    simp [empirical, signQuery]
  rw [signLearner, simulate_query_bind, he, simulate_pure]
  funext
  simp

/-- The one-query learner, run on `40` examples, PAC learns the constants on a point with error
`1/4` and confidence `1/2`: `2 exp (-40 (1/2)² / 2) = 2 exp (-5) ≤ 1/2`. -/
example : PACLearning.IsPACLearnerFor (1 * 40) ⟨1 / 4, by norm_num, by norm_num⟩
    ⟨1 / 2, by norm_num, by norm_num⟩ constants (realizable (PMF.pure ()) constants) := by
  refine (signLearner_learns.mono subset_rfl le_rfl (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ≥0))
    |>.isPACLearnerFor signLearner_isQueryBounded (by norm_num) ?_)
  have h5 : (6 : ℝ) ≤ Real.exp 5 := by
    have := Real.add_one_le_exp (5 : ℝ)
    linarith
  have hexp : Real.exp (-((40 : ℕ) * (1 / 2 : ℝ) ^ 2) / 2) = (Real.exp 5)⁻¹ := by
    rw [← Real.exp_neg]
    norm_num
  rw [hexp]
  have : (Real.exp 5)⁻¹ ≤ 1 / 6 := by
    rw [inv_le_comm₀ (Real.exp_pos 5) (by norm_num)]
    linarith
  push_cast
  linarith

/-- Under the uniform distribution the realizable family is the uniform realizable family. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (C : PACLearning.ConceptClass (ι → Bool) Bool) :
    realizable (PMF.uniformOfFintype (ι → Bool)) C = UniformLearning.uniformRealizable C :=
  rfl

/-! ### The low-degree algorithm -/

/-- There are four sets of at most one of three coordinates. -/
theorem card_filter_card_le_one : #{S : Finset (Fin 3) | #S ≤ 1} = 4 := by
  decide

/-- The low-degree algorithm of degree one makes four queries on three bits. -/
example : OracleComp.IsQueryBounded (lowDegree (Fin 3) 1) 4 := by
  simpa only [card_filter_card_le_one] using isQueryBounded_lowDegree (ι := Fin 3) 1

/-- With tolerance `1/4` the low-degree algorithm of degree one learns the parities of at most one
of three bits under the uniform distribution with error `4 (1/4)² = 1/4`. -/
example : Learns (lowDegree (Fin 3) 1) (PMF.uniformOfFintype (Fin 3 → Bool))
    {c | ∃ S : Finset (Fin 3), #S ≤ 1 ∧ c = parityOn S} (1 / 4) (1 / 4) := by
  have h := learns_lowDegree_parityOn (ι := Fin 3) 1 (τ := 1 / 4)
  rw [card_filter_card_le_one] at h
  norm_num at h
  exact h

/-- The class contains a dictator, which is not a constant. -/
example : parityOn {0} ∈ {c | ∃ S : Finset (Fin 3), #S ≤ 1 ∧ c = parityOn S} :=
  ⟨{0}, by decide, rfl⟩

/-- Simulating the low-degree algorithm gives a PAC learner for these parities from `4 m`
examples, whenever `8 exp (-m / 32) ≤ δ`. -/
example (m : ℕ) (ε δ : Set.Ioo (0 : ℝ≥0) 1) (hε : (1 / 4 : ℝ) ≤ ε.val)
    (hm : 4 * (2 * Real.exp (-(m * (1 / 4 : ℝ) ^ 2) / 2)) ≤ δ.val) :
    PACLearning.IsPACLearnerFor (4 * m) ε δ
      {c | ∃ S : Finset (Fin 3), #S ≤ 1 ∧ c = parityOn S}
      (realizable (PMF.uniformOfFintype (Fin 3 → Bool))
        {c | ∃ S : Finset (Fin 3), #S ≤ 1 ∧ c = parityOn S}) := by
  have h := learns_lowDegree_parityOn (ι := Fin 3) 1 (τ := 1 / 4)
  rw [card_filter_card_le_one] at h
  have hq := isQueryBounded_lowDegree (ι := Fin 3) 1
  rw [card_filter_card_le_one] at hq
  refine (h.mono subset_rfl le_rfl ?_).isPACLearnerFor hq (by norm_num) (by exact_mod_cast hm)
  norm_num
  linarith

end ComplexityTests.StatisticalQuerySimulation
