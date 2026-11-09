/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.Masking
public import CslibFrontier.Crypto.Computational.Pseudoentropy.RepeatedExtraction
public import CslibFrontier.Crypto.Computational.Pseudoentropy.Boosting.Learner
import CslibFrontier.Languages.Probabilistic.Notation

/-!
# From sequence distinguishers to a learned predictor

Saved coordinate predictors turn a sequence distinguishing gap into the average bias of a
weighted validation trial. The explicit learner then samples descriptions, chooses an orientation,
and estimates their validation rates. Its output has positive weighted correlation with high
probability. All target predictions receive only the public observation.

The replay law and the masked source's extraction bound are explicit hypotheses. `SequenceLearner`
constructs saved descriptions and obtains replay from a certified sequence test. Choosing uniform
asymptotic parameters remains a separate step in the final cryptographic reduction.

## Main results

* `maskedSequence_validation_gap`: exact transfer from a sequence gap to weighted validation bias.
* `maskedSequence_learn_error_pow`: sample a correlated predictor from that gap.
* `extractedSequence_learn_error_pow`: pay the supplied test's extraction error before learning.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the following prediction reduction.
  [Holenstein2006].
  This combines the fresh-mask adaptation with explicit sampling and empirical selection.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF BitString Boosting

variable {α β : Type}

/-- The complete sequence gap is the dyadic coordinate count times the average weighted
validation bias of saved descriptions. The replay law is needed only at actual observations. -/
theorem maskedSequence_validation_gap [Finite α]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool)
    (mask : α → ProbComp Bool) (count : ℕ) (test : List (β × Bool) → ProbComp Bool)
    (candidates : ProbComp (List Bool)) (predict : List Bool → β → Bool)
    (hrealize : ∀ value ∈ (ProbComp.eval source).support,
      ProbComp.eval ((fun code => predict code (observe value)) <$> candidates) =
        ProbComp.eval
          (maskedSequencePredictor source observe truth mask count test (observe value))) :
    Pr[OracleComp.replicate count ((fun value => (observe value, truth value)) <$>
      source) >>= test] -
        Pr[OracleComp.replicate count (maskedSample source observe truth mask) >>= test] =
      (dyadicSize count : ℝ) * (Pr[candidates >>= fun code =>
        weightedTrial source mask
          (fun value => pure (predict code (observe value) == truth value))] - 1 / 2) := by
  let := Fintype.ofFinite α
  have hpoint (value : α) (hsupport : value ∈ (ProbComp.eval source).support) :
      Pr[candidates >>= fun code => pure (predict code (observe value) == truth value)] =
        Pr[(fun guess => guess == truth value) <$>
          maskedSequencePredictor source observe truth mask count test (observe value)] := by
    apply congrArg (fun law : PMF Bool => (law true).toReal)
    have h := congrArg (PMF.map (fun guess => guess == truth value)) (hrealize value hsupport)
    simpa only [bind_pure_comp, ProbComp.eval_map, PMF.map_comp, Function.comp_def] using h
  have hvalidation : Pr[candidates >>= fun code => weightedTrial source mask
      (fun value => pure (predict code (observe value) == truth value))] =
      Pr[weightedTrial source mask (fun value =>
        candidates >>= fun code => pure (predict code (observe value) == truth value))] :=
    congrArg (fun law : PMF Bool => (law true).toReal)
      (eval_weightedTrial_bind candidates source mask _)
  rw [maskedSequence_prediction_gap, hvalidation, weightedTrial_probability]
  simp only [add_sub_cancel_left]
  congr 1
  apply Finset.sum_congr rfl
  intro value _
  by_cases hsupport : value ∈ (ProbComp.eval source).support
  · rw [hpoint value hsupport]
    simp only [mul_assoc]
  · have hzero : ProbComp.eval source value = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hsupport
    simp [hzero]

/-- A noticeable sequence gap of either sign gives an explicitly sampled predictor with
positive weighted correlation. Its failure probability includes discovery and estimation. -/
theorem maskedSequence_learn_error_pow [Fintype α]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool)
    (mask : α → ProbComp Bool) (count : ℕ) (test : List (β × Bool) → ProbComp Bool)
    (candidates : ProbComp (List Bool)) (predict : List Bool → β → Bool)
    (hrealize : ∀ value ∈ (ProbComp.eval source).support,
      ProbComp.eval ((fun code => predict code (observe value)) <$> candidates) =
        ProbComp.eval
          (maskedSequencePredictor source observe truth mask count test (observe value)))
    (confidence inverseGap : ℕ) (hgap : 0 < inverseGap)
    (hdistinguish : (dyadicSize count : ℝ) / inverseGap ≤
      |Pr[OracleComp.replicate count ((fun value => (observe value, truth value)) <$>
        source) >>= test] -
          Pr[OracleComp.replicate count (maskedSample source observe truth mask) >>=
            test]|) :
    ((ProbComp.eval (learn candidates (fun code => weightedTrial source mask
      (fun value => pure (predict code (observe value) == truth value)))
        confidence inverseGap)).toOuterMeasure
      {code | ¬ 1 / (2 * inverseGap) ≤ ∑ value, (ProbComp.eval source value).toReal *
        (Pr[mask value] * signedVote (signedPredict predict code (observe value))
          (truth value))}).toReal ≤
      (((confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) * (1 / 2 : ℝ) ^ confidence := by
  apply learn_correlation_error_pow candidates source mask
    (fun code value => predict code (observe value)) truth confidence inverseGap hgap
  have hcount : (0 : ℝ) < dyadicSize count := by exact_mod_cast dyadicSize_pos count
  rw [maskedSequence_validation_gap source observe truth mask count test candidates predict
      hrealize,
    abs_mul, abs_of_pos hcount] at hdistinguish
  have hfactor : (dyadicSize count : ℝ) / inverseGap =
      dyadicSize count * (1 / inverseGap : ℝ) := by ring
  rw [hfactor] at hdistinguish
  nlinarith

/-- A distinguisher of extracted labels supplies a weak learner once its advantage exceeds
the masked-source extraction error for that test. The statistical premise concerns the
complete public observations, hash seed, and output. -/
theorem extractedSequence_learn_error_pow {Seed Output : Type} [Fintype α]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool)
    (mask : α → ProbComp Bool) (count : ℕ) (seed : ProbComp Seed)
    (hash : Seed → List Bool → Output) (test : List β × Seed × Output → ProbComp Bool)
    (ideal : PMF (List β × Seed × Output)) {ε : ℝ}
    (hclose : (Game.advantage
      ((ProbComp.eval (OracleComp.replicate count
        (maskedSample source observe truth mask) >>= extractLabels seed hash)).bind
          (fun output => ProbComp.eval (test output)))
      (ideal.bind (fun output => ProbComp.eval (test output))) : ℝ) ≤ ε)
    (candidates : ProbComp (List Bool)) (predict : List Bool → β → Bool)
    (hrealize : ∀ value ∈ (ProbComp.eval source).support,
      ProbComp.eval ((fun code => predict code (observe value)) <$> candidates) =
        ProbComp.eval (maskedSequencePredictor source observe truth mask count
          (fun samples => extractLabels seed hash samples >>= test) (observe value)))
    (confidence inverseGap : ℕ) (hgap : 0 < inverseGap)
    (hdistinguish : (dyadicSize count : ℝ) / inverseGap + ε ≤
      (Game.advantage (ProbComp.eval (do
        let samples ← OracleComp.replicate count
          ((fun value => (observe value, truth value)) <$> source)
        let result ← extractLabels seed hash samples
        test result))
        (ideal.bind (fun output => ProbComp.eval (test output))) : ℝ)) :
    ((ProbComp.eval (learn candidates (fun code => weightedTrial source mask
      (fun value => pure (predict code (observe value) == truth value)))
        confidence inverseGap)).toOuterMeasure
      {code | ¬ 1 / (2 * inverseGap) ≤ ∑ value, (ProbComp.eval source value).toReal *
        (Pr[mask value] * signedVote (signedPredict predict code (observe value))
          (truth value))}).toReal ≤
      (((confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) * (1 / 2 : ℝ) ^ confidence := by
  apply maskedSequence_learn_error_pow source observe truth mask count
    (fun samples => extractLabels seed hash samples >>= test) candidates predict hrealize
    confidence inverseGap hgap
  have h := extractLabels_sequence_gap ((fun value => (observe value, truth value)) <$> source)
    (maskedSample source observe truth mask) count seed hash test ideal hclose
  have hgap' := (le_sub_iff_add_le.mpr hdistinguish).trans h
  simpa only [Game.coe_advantage, Game.coe_succProbability] using hgap'

end Cslib.Crypto.Pseudoentropy
