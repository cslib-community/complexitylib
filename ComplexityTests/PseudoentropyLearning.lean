/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.Learning
import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Training
import Complexity.Tactic.PPT

/-!
# Sampled learning and repeated extraction

Clients exercise both predictor orientations, rejected validation, malformed descriptions,
complete training, alternative encodings, and statistical tests of the full public output.
-/

namespace ComplexityTests.PseudoentropyLearning

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.Crypto
  Cslib.Crypto.Pseudoentropy Cslib.Crypto.Pseudoentropy.Boosting Cslib.BitString
  Turing.MultiTapeTM

-- Rejection preserves a fair baseline even when the validation trial is arbitrary.
example {α : Type} (source : ProbComp α) (test : α → ProbComp Bool) :
    ProbComp.eval (weightedTrial source (fun _ => pure false) test) =
      PMF.uniformOfFintype Bool := by
  simp [weightedTrial, ProbComp.eval_bind]

-- The same saved description is used for validation and public prediction.
example : signedPredict (fun _ (_ : Unit) => false) [true] () = true ∧
    signedPredict (fun _ (_ : Unit) => false) [false] () = false ∧
    signedPredict (fun _ (_ : Unit) => false) [] () = false := by decide

-- A zero discovery budget returns its fallback, with no assumptions about the programs.
example (source : ProbComp (List Bool)) (test : List Bool → ProbComp Bool) (confidence : ℕ) :
    learn source test confidence 0 = pure [] := by
  simp [learn, OracleComp.sampleBest, OracleComp.selectFrom, OracleComp.selectBest]

-- A maximally wrong predictor has negative bias. Sampling its orientation still learns a
-- positively correlated predictor, with a nontrivial failure bound.
private theorem wrongPredictor_failure (confidence inverseGap : ℕ) (hgap : 0 < inverseGap)
    (hbias : (1 : ℝ) / inverseGap ≤ 1 / 2) :
    ((ProbComp.eval (learn (pure [])
      (fun code => weightedTrial (pure ()) (fun _ => pure true)
        (fun _ => pure ((fun _ : List Bool => false) code == true))) confidence inverseGap
      )).toOuterMeasure
      {code | ¬ (1 : ℝ) / (2 * inverseGap) ≤
        signedVote (signedPredict (fun _ (_ : Unit) => false) code ()) true}).toReal ≤
      (((confidence + 1) * (4 * inverseGap) ^ 2 : ℕ) + 1) * (1 / 2 : ℝ) ^ confidence := by
  have h := learn_correlation_error_pow (pure []) (pure ()) (fun _ => pure true)
    (fun _ (_ : Unit) => false) (fun _ => true) confidence inverseGap hgap
    (by simpa [weightedTrial, ProbComp.eval_bind] using hbias)
  simpa only [ProbComp.eval_pure, Fintype.sum_unique, PMF.pure_apply_self,
    ENNReal.toReal_one, one_mul] using h

example : ((ProbComp.eval (learn (pure [])
      (fun code => weightedTrial (pure ()) (fun _ => pure true)
        (fun _ => pure ((fun _ : List Bool => false) code == true))) 16 2)).toOuterMeasure
      {code | ¬ (1 : ℝ) / (2 * (2 : ℕ)) ≤
        signedVote (signedPredict (fun _ (_ : Unit) => false) code ()) true}
      ).toReal ≤ 1 / 32 := by
  exact (wrongPredictor_failure 16 2 (by decide) (by norm_num)).trans (by norm_num)

-- Every possible learned description, including statistically bad ones, pays for its sign bit.
example (test : List Bool → ProbComp Bool) {code : List Bool}
    (hcode : code ∈ (ProbComp.eval (learn (pure [false, true]) test 7 2)).support) :
    code.length ≤ 3 :=
  learn_length_le (pure [false, true]) test 7 2 2 (by simp) hcode

-- The complete learner is a normal client of captured-input program certificates.
example : IsPPTOn encBits encBits (fun word =>
    learn (pure word) (fun code => pure (code == word)) (word.length + 1) (word.length + 2)) := by
  ppt

example : IsPPTOn (encList encBool) encBits (fun word => do
    let confidence := word.length + 1
    let gap := word.length + 2
    learn (pure word) (fun code => pure (code == word)) confidence gap) := by ppt

-- An evaluator supplied by the caller composes with signed descriptions and captured inputs.
example (evaluate : List Bool → List Bool → Bool)
    (hevaluate : ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
      (encPair encBits encBits) encBool) :
    ComputableInPolyTime
      (fun word => signedPredict evaluate (true :: word) (word ++ [false]))
      (encList encBool) encBool := by
  fun_prop

-- Training calls the sampled learner inside its adaptive loop; no explicit machine is needed.
example : IsPPTOn encBits (encPair State.encoding encUnary) (fun word =>
    train (signedPredict (fun code observation => listStrictMajority (code ++ observation)))
      (pure (word, true))
      (fun state => learn (pure (word.take (state.threshold + 1)))
        (fun code => pure (listStrictMajority (code ++ word)))
        (word.length + 1) (word.length + 2))
      ⟨word.length + 1, 1, 1, 1, word.length + 1⟩) := by ppt

-- Raw Boolean labels and framed natural labels use the same functional extractor.
example : IsPPTOn (encList encBool)
    (encPair (encList encBits) (encPair encBool encBits)) (fun word =>
      extractLabels (ProbComp.uniform Bool)
        (fun key bits => if key then bits else bits.reverse) [(word, true), (word, false)]) := by
  ppt

example : IsPPTOn encBits (encPair (encList encBits) (encPair encBool encUnary)) (fun word => do
    let samples := [(word, word.length), ([], word.length + 1)]
    extractLabels (ProbComp.uniform Bool)
      (fun key values => if key then values.length else values.headD 0) samples) := by ppt

-- A missing validation certificate cannot be hidden by the learner's certificate.
example (test : List Bool → List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair encBits encBits) encBool (fun pair => test pair.1 pair.2)) :
    IsPPTOn encBits encBits (fun word => learn (pure word) (test word) 1 1) := by
  fail_if_success (clear htest; ppt)
  ppt

-- A fixed injective hash supplies a concrete two-universal family, with public side information.
private theorem identityHash :
    IsTwoUniversal (PMF.pure ()) (fun (_ : Unit) (bit : Bool) => bit) := by
  intro x y hne
  simp [hne]

example (joint : PMF (Bool × Bool)) :
    dist (joint.bind (fun pair => (PMF.pure ()).map (fun key => (pair.1, key, pair.2))))
      ((joint.map Prod.fst).bind (fun bit => ((PMF.pure ()).bind
        (fun key => (PMF.uniformOfFintype Bool).map (key, ·))).map (bit, ·))) ≤
      2 * (joint.toOuterMeasure
        {pair | (1 / 4 : ℝ) < (conditionalSnd joint pair.1 pair.2).toReal}).toReal + 1 / 2 := by
  have h := identityHash.leftover_hash_joint_of_heavy_probability joint (mass := 1 / 4)
    (by norm_num)
  convert h using 1
  norm_num

-- An arbitrary randomized test sees the full observation list and seed even for empty outputs.
example {Observation Label Seed : Type} (source : ProbComp (Observation × Label))
    (seed : ProbComp Seed) (count : ℕ) (test : List Observation × Seed × Unit → Game) :
    Game.advantage
      ((ProbComp.eval (OracleComp.replicate count source >>=
        extractLabels seed (fun _ _ => ()))).bind test)
      ((extractLabelsIdeal (Output := Unit) (Prod.fst <$> source) count seed).bind test) = 0 := by
  rw [eval_extractLabels_of_subsingleton, Game.advantage_self]

-- Repetition and slack computation compose through alternative input encodings.
example : ComputableInPolyTime
    (fun word => (ExtractionSchedule.count word.length (word.length + 1) 2,
      ExtractionSchedule.slack word.length (word.length + 1) 2))
    (encList encBool) (encPair encUnary encUnary) := by fun_prop

end ComplexityTests.PseudoentropyLearning
