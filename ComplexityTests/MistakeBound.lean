/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.MachineLearning.OnlineLearning.MistakeBound.Perceptron
import Complexity.MachineLearning.OnlineLearning.MistakeBound.SOA
import Complexity.MachineLearning.OnlineLearning.MistakeBound.Thresholds

/-! Checked instances for the realizable mistake-bound model: concrete runs of the halving
algorithm and the perceptron, the gap between VC and Littlestone dimension for thresholds, the
optimal mistake bound of all Boolean functions on three points, and the margin hypotheses of
Novikoff's theorem. -/

namespace ComplexityTests.MistakeBound

open Cslib.MachineLearning Cslib.MachineLearning.OnlineLearning.MistakeBound
open PACLearning (ConceptClass vcDim)
open RealInnerProductSpace

/-! ### Halving -/

/-- Three concepts on `Fin 2`: constantly `false`, the indicator of `1`, and constantly `true`. -/
def three : Finset (Fin 2 → Bool) := {fun _ => false, fun i => decide (i = 1), fun _ => true}

example : three.card = 3 := by decide

/-- On `(0, true), (1, true)`, halving first follows the two concepts labelling `0` with `false`
and errs; the survivor `fun _ => true` then predicts `1` correctly. -/
example : mistakes (halving three) [(0, true), (1, true)] = 1 := by decide

/-- A tie (one concept each way) is broken towards `false`, so halving errs on `(1, true)` after
`(0, false)`: the indicator of `1` is the target. -/
example : halving three [(0, false)] 1 = false ∧
    mistakes (halving three) [(0, false), (1, true)] = 1 := by decide

/-- On `(0, false), (1, false)`, halving predicts `false` twice and never errs. -/
example : mistakes (halving three) [(0, false), (1, false)] = 0 := by decide

/-- A sequence that no concept of `three` labels: `(0, true)` leaves only `fun _ => true`, which
`(1, false)` contradicts. -/
example : ¬ Realizable (three : ConceptClass (Fin 2) Bool) [(0, true), (1, false)] := by
  rw [realizable_iff]
  simp only [Finset.mem_coe]
  decide

/-- The halving bound for `three`: at most `⌊log₂ 3⌋ = 1` mistake on every realizable sequence. -/
example : mistakeBound (halving three) (three : ConceptClass (Fin 2) Bool) ≤ 1 := by
  have := mistakeBound_halving_le three
  have h3 : Nat.log 2 three.card = 1 := by decide
  rwa [h3, Nat.cast_one] at this

/-! ### Littlestone dimension, optimal mistake bounds and VC dimension -/

/-- The eight thresholds `θ ≤ 7` have VC dimension `1` but Littlestone dimension `3`. -/
example : vcDim (thresholdClassUpTo 7) = 1 ∧ littlestoneDim (thresholdClassUpTo 7) = 3 := by
  refine ⟨vcDim_thresholdClassUpTo (by norm_num), ?_⟩
  rw [littlestoneDim_thresholdClassUpTo, show Nat.log 2 (7 + 1) = 3 by decide]
  rfl

/-- Every deterministic learner can be forced to err three times on some sequence of three
examples labelled by a threshold `θ ≤ 7`. -/
example (A : OnlineLearner ℕ) :
    ∃ S : List (ℕ × Bool), S.length = 3 ∧ Realizable (thresholdClassUpTo 7) S ∧
      mistakes A S = 3 := by
  refine exists_realizable_mistakes_eq A (hasMistakeTree_of_le_littlestoneDim ?_ ?_)
  · exact ⟨thresholdConcept 0, 0, by simp, rfl⟩
  · rw [littlestoneDim_thresholdClassUpTo, show Nat.log 2 (7 + 1) = 3 by decide]

/-- The thresholds `θ ≤ 6` already have Littlestone dimension `2` only: `⌊log₂ 7⌋ = 2`. So no
complete mistake tree of height `3` exists. -/
example : ¬ HasMistakeTree 3 (thresholdClassUpTo 6) := by
  intro h
  have := le_littlestoneDim_of_hasMistakeTree h
  rw [littlestoneDim_thresholdClassUpTo, show Nat.log 2 (6 + 1) = 2 by decide] at this
  exact absurd (Nat.cast_le.mp this) (by norm_num)

/-- All Boolean functions on three points: the optimal mistake bound is `3`, attained by SOA. -/
example : optimalMistakeBound (Set.univ : ConceptClass (Fin 3) Bool) = 3 ∧
    mistakeBound (soa Set.univ) (Set.univ : ConceptClass (Fin 3) Bool) = 3 := by
  rw [optimalMistakeBound_eq_littlestoneDim, mistakeBound_soa, littlestoneDim_univ]
  simp

/-- The class of all thresholds admits no finite mistake bound, for any learner. -/
example (A : OnlineLearner ℕ) : mistakeBound A thresholdClass = ⊤ :=
  top_le_iff.mp (littlestoneDim_thresholdClass ▸ littlestoneDim_le_mistakeBound A _)

/-- A class with one concept: the learner that predicts with this concept never errs. -/
example (c : ℕ → Bool) : optimalMistakeBound ({c} : ConceptClass ℕ Bool) = 0 := by
  refine le_antisymm ((optimalMistakeBound_le (fun _ x => c x) _).trans ?_) bot_le
  refine mistakeBound_le_iff.mpr fun S hS => ?_
  obtain ⟨c', rfl, hcS⟩ := realizable_iff.mp hS
  rw [mistakes_eq_card]
  simp [hcS _ (List.getElem_mem _)]

/-! ### The perceptron -/

/-- A run in `ℝ`: the first example `(1, true)` is a mistake (the weight is `0`), the update gives
weight `1`, and `(-2, false)` is then predicted correctly. -/
example : mistakes perceptron [((1 : ℝ), true), (-2, false)] = 1 := by
  simp [mistakes, mistakesFrom_cons, perceptron, perceptronWeight, perceptronStep]

/-- Novikoff's bound applied to this run: `u = 1` separates it with margin `γ = 1`, the instances
have norm at most `R = 2`, so at most `(2 / 1)² = 4` mistakes. -/
example : (mistakes perceptron [((1 : ℝ), true), (-2, false)] : ℝ) ≤ (2 / 1) ^ 2 := by
  refine mistakes_perceptron_le (1 : ℝ) (by simp) one_pos _ ?_ ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> norm_num

/-- The hypothesis `0 ≤ γ` of `mistakes_perceptron_mul_sq_le` is needed: with `u = 0` and
`γ = -1` the margin condition holds, the perceptron errs once on `(1, true)`, and
`M γ² ≤ R² ‖u‖²` fails. -/
example : ∃ (S : List (ℝ × Bool)) (u γ R : ℝ),
    (∀ p ∈ S, γ ≤ signedLabel p.2 * ⟪u, p.1⟫) ∧ (∀ p ∈ S, ‖p.1‖ ≤ R) ∧
      ¬ (mistakes perceptron S * γ ^ 2 ≤ R ^ 2 * ‖u‖ ^ 2) := by
  refine ⟨[(1, true)], 0, -1, 1, by simp, by simp, ?_⟩
  simp [mistakes, mistakesFrom_cons, perceptron, perceptronWeight]

end ComplexityTests.MistakeBound
