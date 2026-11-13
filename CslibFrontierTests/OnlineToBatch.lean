/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Halving
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.OnlineToBatch
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.SOA
import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Thresholds

/-! Checked instances for the online-to-batch conversion of mistake bounds: a concrete majority vote
of prefix hypotheses of the halving algorithm, the resulting PAC learner for three concepts on
`Fin 2` with an explicit sample size and a sample size that does not suffice, and PAC learnability
of the bounded thresholds on `ℕ` through the standard optimal algorithm, contrasted with the class
of all thresholds, which has no finite mistake bound. -/

namespace CslibFrontierTests.OnlineToBatch

open Cslib.MachineLearning Cslib.MachineLearning.OnlineLearning.MistakeBound MeasureTheory
open PACLearning (ConceptClass LabeledSample error IsPACLearnerFor IsPACLearnable
  realizableDistributions IsRealizableBy)
open scoped NNReal ENNReal

/-- Three concepts on `Fin 2`: constantly `false`, the indicator of `1`, and constantly `true`. -/
def three : Finset (Fin 2 → Bool) := {fun _ => false, fun i => decide (i = 1), fun _ => true}

theorem mistakeBound_halving_three_le :
    mistakeBound (halving three) (three : ConceptClass (Fin 2) Bool) ≤ 1 := by
  have := mistakeBound_halving_le three
  have h3 : Nat.log 2 three.card = 1 := by decide
  rwa [h3, Nat.cast_one] at this

/-! ### Prefix hypotheses and their majority vote -/

/-- The sample `(0, true), (1, true)`, labelled by the constant `true`. -/
def sampleTT : LabeledSample (Fin 2) Bool 2 := ![(0, true), (1, true)]

/-- Before any example, halving breaks the tie at `0` (two concepts say `false`) towards `false`;
after one or two examples only the constant `true` survives. Two of the three prefix hypotheses
predict `true` at `0`, so the majority vote does, although the first prefix hypothesis does not. -/
example : prefixHypothesis (halving three) sampleTT 0 0 = false ∧
    prefixHypothesis (halving three) sampleTT 1 0 = true ∧
    prefixHypothesis (halving three) sampleTT 2 0 = true ∧
    prefixMajority (halving three) sampleTT 0 = true := by decide

/-- On a sample labelled by the constant `false`, every prefix hypothesis, and so the majority
vote, predicts `false` at `1`. -/
example : prefixMajority (halving three) ![((0 : Fin 2), false), (1, false)] 1 = false := by
  decide

/-! ### A PAC learner from the halving bound -/

/-- Accuracy and confidence `1 / 2`. -/
noncomputable def half : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Halving makes at most one mistake on `three`, so seven examples suffice for accuracy and
confidence `1 / 2`: `2 · 1 ≤ (1 / 2) · (1 / 2) · (7 + 1)`. -/
theorem isPACLearnerFor_three_seven : IsPACLearnerFor 7 half half
    (three : ConceptClass (Fin 2) Bool) (realizableDistributions three) := by
  refine isPACLearnerFor_prefixMajority (isMeasurableLearner_of_countable _)
    mistakeBound_halving_three_le ?_
  simp only [half]
  norm_num

/-- Zero examples do not suffice for `three` at accuracy and confidence `1 / 2`: the hypothesis on
the empty sample is wrong with probability one under a point mass at `0` labelled by the opposite
constant. So the theorem's sample size is not met vacuously. -/
theorem not_isPACLearnerFor_three_zero : ¬ IsPACLearnerFor 0 half half
    (three : ConceptClass (Fin 2) Bool) (realizableDistributions three) := by
  rintro ⟨A, hA⟩
  set y := !(A (fun i => i.elim0) 0)
  set D : Measure (Fin 2 × Bool) := Measure.dirac (0, y)
  have hc : (fun _ => y) ∈ (three : ConceptClass (Fin 2) Bool) := by
    cases hy : y <;> simp [three]
  have hD : D ∈ realizableDistributions (three : ConceptClass (Fin 2) Bool) :=
    ⟨fun _ => y, hc, by simp [D, error]⟩
  have key := hA D hD
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add] at key
  have hset : {S : LabeledSample (Fin 2) Bool 0 |
      ((half.val : ℝ≥0) : ℝ≥0∞) < error D (A S)} = Set.univ := by
    refine Set.eq_univ_of_forall fun S => ?_
    have hS : S = fun i => i.elim0 := Subsingleton.elim _ _
    have herr : error D (A S) = 1 := by
      rw [hS]
      simp [D, error, y]
    change ((half.val : ℝ≥0) : ℝ≥0∞) < error D (A S)
    rw [herr, half]
    exact_mod_cast (by norm_num : (1 / 2 : ℝ≥0) < 1)
  rw [hset, measure_univ, half] at key
  exact absurd key (by exact_mod_cast (by norm_num : ¬ (1 : ℝ≥0) ≤ 1 / 2))

/-! ### Thresholds on `ℕ` -/

/-- The eight thresholds `θ ≤ 7` are PAC learnable over their realizable distributions: the
standard optimal algorithm makes at most `⌊log₂ 8⌋ = 3` mistakes, so `⌈2 · 3 / (ε δ)⌉` examples
suffice. -/
example : IsPACLearnable (thresholdClassUpTo 7) (realizableDistributions (thresholdClassUpTo 7)) :=
  isPACLearnable_of_mistakeBound_le (isMeasurableLearner_of_countable _) (M := 3) (by
    rw [mistakeBound_soa, littlestoneDim_thresholdClassUpTo, show Nat.log 2 (7 + 1) = 3 by decide])

/-- The same conclusion through the optimal mistake bound. -/
example : IsPACLearnable (thresholdClassUpTo 7) (realizableDistributions (thresholdClassUpTo 7)) :=
  isPACLearnable_of_optimalMistakeBound_ne_top (by
    rw [optimalMistakeBound_eq_littlestoneDim, littlestoneDim_thresholdClassUpTo]
    exact ENat.natCast_ne_top _)

/-- The class of all thresholds has no finite optimal mistake bound, so the online-to-batch theorem
does not apply to it, although it has VC dimension `1` and is PAC learnable by VC theory. -/
example : optimalMistakeBound thresholdClass = ⊤ := by
  rw [optimalMistakeBound_eq_littlestoneDim, littlestoneDim_thresholdClass]

end CslibFrontierTests.OnlineToBatch
