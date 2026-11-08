/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Probability.StochasticOracle.ResidualPolicy
import Mathlib.Tactic

/-!
# Actual residual construction and universal randomized-policy optima

Five nontrivial X3C blocks have two disjoint witness triples and an additional
intersecting triple. The arbitrary-family construction derives its primal/dual
certificates and actual residual. Every admissible randomized competitor has
one-turn cost at least five and two-turn cost at least three. Both bounds are
attained, giving the strict adaptivity ratio 5/3.
-/

noncomputable section
open Finset Cslib.Optimization.OneConstraint
open Cslib.Probability.StochasticOracle.ResidualCover
namespace ComplexityTests.StochasticOracleResidualCover

/-- This is an actual yes-input, with an overlapping unused candidate. -/
def block : Block where
  r := 2
  r_pos := by norm_num
  family := {{0, 1, 2}, {3, 4, 5}, {0, 3, 4}}
  triples := by
    intro A hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl <;> decide
  witness := {{0, 1, 2}, {3, 4, 5}}
  witness_subset := by decide
  witness_disjoint := by
    intro A hA B hB hne
    simp only [mem_coe, mem_insert, mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hne rfl).elim
    · decide
    · decide
    · exact (hne rfl).elim
  witness_covers := by decide

/-- Arbitrarily many candidates per block are permitted in the generic theorems;
this concrete instance has five six-point blocks, not singleton obligations. -/
def blocks : Fin 5 → Block := fun _ => block

/-- Source costs c(n)=1, alpha=2, and a full-support uniform near-cover law. -/
def parameters : Parameters 5 where
  missing :=
    { weight := fun _ => 1 / 5
      nonneg := by intro j; norm_num
      total := by norm_num }
  full_support := by intro j; norm_num
  nearCost := 2
  near_pos := by norm_num
  specialistCost := fun _ => 1
  specialist_pos := by intro j; norm_num

example : Fintype.card (Point blocks) = 30 := by
  rw [universe_card]
  norm_num [blocks, block]

example : block.witness.card = 2 := block.witness_card

/-- The LP value and integral optimum are consequences of the actual input. -/
example :
    (coverInstance blocks (by norm_num)).covered (payload blocks univ) = univ ∧
    (coverInstance blocks (by norm_num)).cost (payload blocks univ) = 1 ∧
    (∀ C, (coverInstance blocks (by norm_num)).covered C = univ →
      1 ≤ (coverInstance blocks (by norm_num)).cost C) :=
  primal_optimum blocks (by norm_num)

example : ∑ e ∈ (coverInstance blocks (by norm_num)).ground,
    (coverInstance blocks (by norm_num)).dual e = 1 := dual_objective blocks (by norm_num)

/-- For every actual near answer, the residual decoder selects exactly its
missing specialist and both sequential responses are locally certified. -/
example (j : Fin 5) :
    residualIndex blocks (by norm_num)
      ((coverInstance blocks (by norm_num)).ground \
        (coverInstance blocks (by norm_num)).covered (payload blocks (univ.erase j))) = j ∧
    (coverInstance blocks (by norm_num)).Certified 1 ∅ (payload blocks (univ.erase j)) ∧
    (coverInstance blocks (by norm_num)).Certified 1
      (payload blocks (univ.erase j)) (specialist blocks j) :=
  ⟨decode_near_residual blocks (by norm_num) j, responses_certified blocks (by norm_num) j⟩

/-- Includes arbitrary first-batch randomization and final extraction, not just
comparison with the named all-specialist upper strategy. -/
example (π : OnePolicy blocks) (hA : π.Admissible parameters)
    (hS : π.success parameters (by norm_num) = 1) : 5 ≤ π.cost parameters := by
  simpa [parameters] using π.lower_cost parameters (by norm_num) hA hS

/-- Includes mixed near/specialist first batches, randomized conditional follow-up,
and randomized extraction. No lower-cost or residual certificate is supplied. -/
example (π : TwoPolicy blocks) (hA : π.Admissible parameters)
    (hS : π.success parameters (by norm_num) = 1) : 3 ≤ π.cost parameters := by
  have h := π.lower_cost parameters (by norm_num) hA hS
  norm_num [parameters, Distribution.mean] at h ⊢
  exact h

example : (allOne (T := blocks)).Admissible parameters ∧
    (allOne (T := blocks)).success parameters (by norm_num) = 1 ∧
    (allOne (T := blocks)).cost parameters = 5 := by
  refine ⟨allOne_admissible parameters, allOne_success parameters (by norm_num), ?_⟩
  rw [allOne_cost]
  norm_num [parameters]

example : (adaptiveTwo (T := blocks)).Admissible parameters ∧
    (adaptiveTwo (T := blocks)).success parameters (by norm_num) = 1 ∧
    (adaptiveTwo (T := blocks)).cost parameters = 3 := by
  refine ⟨adaptiveTwo_admissible parameters, adaptiveTwo_success parameters (by norm_num), ?_⟩
  rw [adaptiveTwo_cost]
  norm_num [parameters, Distribution.mean]

/-- The ratio is between attained universally optimal actual policies. -/
example : ∃ (π : OnePolicy blocks) (σ : TwoPolicy blocks),
    π.Admissible parameters ∧ π.success parameters (by norm_num) = 1 ∧
    σ.Admissible parameters ∧ σ.success parameters (by norm_num) = 1 ∧
    (∀ ψ : OnePolicy blocks, ψ.Admissible parameters →
      ψ.success parameters (by norm_num) = 1 → π.cost parameters ≤ ψ.cost parameters) ∧
    (∀ ψ : TwoPolicy blocks, ψ.Admissible parameters →
      ψ.success parameters (by norm_num) = 1 → σ.cost parameters ≤ ψ.cost parameters) ∧
    π.cost parameters / σ.cost parameters = 5 / 3 := by
  have h := attained_ratio (T := blocks) parameters (by norm_num) 1 2
    (by norm_num) (fun _ => rfl) (by norm_num [parameters])
  norm_num at h ⊢
  exact h

/-- Nontrivial physical deadlines: the first batch is nonempty and the targeted
follow-up is nonempty, so these are exactly one and two physical turns. -/
example (j : Fin 5) : batchLatency (specialistBatch : Batch 5) = 1 ∧
    batchLatency ({none} : Batch 5) + batchLatency {some j} = 2 := by
  have hn : (specialistBatch : Batch 5).Nonempty := ⟨some j, by simp [specialistBatch]⟩
  norm_num [batchLatency, hn]

end ComplexityTests.StochasticOracleResidualCover
