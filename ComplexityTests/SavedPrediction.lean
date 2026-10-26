/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.SequenceLearner
import Complexity.Tactic.PPT

/-!
# Saved prediction and adaptive sequence learning

Clients exercise total decoding, exact replay of a concrete label test, zero-coordinate padding,
source-independent description bounds, and complete prediction with alternative input encodings.
-/

namespace ComplexityTests.SavedPrediction

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Pseudoentropy
  Cslib.Crypto.Pseudoentropy.Boosting Cslib.BitString Turing.MultiTapeTM

-- Exposing computed encodings works inside larger expressions, including captured inputs.
example {α : Type} (encoding : α ↪ List Bool) :
    ComputableInPolyTime (fun pair : α × List Bool =>
      pair.2 ++ encPair encoding encBits (pair.1, pair.2.reverse))
      (encPair encoding encBits) encBits := by fun_prop

example : ComputableInPolyTime (fun pair : List Bool × Bool =>
    let word := encPair encBits encBool (pair.1.reverse, !pair.2)
    (unframe word, (dropFrame word).headD false))
    (encPair (encList encBool) encBool) (encPair encBits encBool) := by fun_prop

-- An arbitrary encoding is not automatically an efficient transformation of raw words.
example (encoding : List Bool ↪ List Bool)
    (hencoding : ComputableInPolyTime encoding encBits encBits) :
    ComputableInPolyTime (fun word => encoding word.reverse) encBits encBits := by
  fail_if_success (clear hencoding; fun_prop)
  fun_prop

-- Truncated descriptions are total, and padding rejects independently of the supplied test.
example : SavedPrediction.Description.decode [true] = ⟨false, false, [], [], []⟩ := rfl

example (raw : List Bool → List Bool → List Bool) (trial : Bool) (observation : List Bool) :
    SavedPrediction.evaluate raw
      (SavedPrediction.Description.encoding ⟨false, trial, [], [], []⟩) observation = !trial := by
  simp [SavedPrediction.evaluate]

example (raw : List Bool → List Bool → List Bool)
    (hraw : ComputableInPolyTime (fun pair => raw pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun pair : List Bool × List Bool =>
      SavedPrediction.evaluate raw (pair.1.take pair.2.length) pair.2.reverse)
      (encPair (encList encBool) encBits) encBool := by
  fail_if_success (clear hraw; fun_prop)
  fun_prop

-- An evaluator that uses no coins still stores the complete context and orientation.
example (front back : List Bool) (trial : Bool) (width : ℕ) :
    ProbComp.eval (SavedPrediction.save 0 1 width trial front back) =
      PMF.pure (SavedPrediction.Description.encoding ⟨true, trial, front, back, []⟩) := by
  simp [SavedPrediction.save, SavedPrediction.coinBudget]

-- The deterministic test reads the first label. Its raw implementation parses the common
-- representation; surrounding samples and the target observation remain arbitrary.
private def firstLabel (values : List (Bool × Bool)) : ProbComp Bool :=
  pure (values.headD (false, false)).2

private def firstLabelRaw (_coins input : List Bool) : List Bool :=
  dropFrame (unframe (dropFrame input))

private theorem firstLabel_replay (base : List Bool) (values : List (Bool × Bool))
    (budget : ℕ) :
    ProbComp.eval (firstLabel values) = (uniformList budget).map (fun coins =>
      (firstLabelRaw coins (encPair encBits (encList (encPair encBool encBool))
        (base, values))).headD false) := by
  have hbase : dropFrame (frame base) = [] := by
    simpa using dropFrame_frame_append base []
  have hread (coins : List Bool) :
      (firstLabelRaw coins (encPair encBits (encList (encPair encBool encBool))
        (base, values))).headD false = (values.headD (false, false)).2 := by
    cases values <;>
      simp [firstLabelRaw, encList_cons, hbase, unframe, dropFrame]
  simp only [firstLabel, ProbComp.eval_pure, hread]
  exact (PMF.map_const _ _).symm

example (base : List Bool) (replacement original : ProbComp (Bool × Bool)) (count : ℕ)
    (observation : Bool) :
    ProbComp.eval ((fun code => SavedPrediction.evaluate firstLabelRaw code [observation]) <$>
      SavedPrediction.sample encBool base replacement original count 0 1 1) =
      ProbComp.eval (bitPredictor (fun trial =>
        sequenceTest replacement original count firstLabel (observation, trial))) := by
  exact SavedPrediction.eval_sample encBool base replacement original count 0 1 1
    firstLabel firstLabelRaw (fun values budget _ => firstLabel_replay base values budget)
    observation (by simp)

-- Padding at zero coordinates is fair even when the unused sources and test are arbitrary.
example (replacement original : ProbComp (Bool × Bool)) (observation : Bool) :
    ProbComp.eval ((fun code => SavedPrediction.evaluate firstLabelRaw code [observation]) <$>
      SavedPrediction.sample encBool [] replacement original 0 0 1 1) =
      PMF.uniformOfFintype Bool := by
  trans ProbComp.eval (bitPredictor (fun trial =>
    sequenceTest replacement original 0 firstLabel (observation, trial)))
  · exact SavedPrediction.eval_sample encBool [] replacement original 0 0 1 1
      firstLabel firstLabelRaw (fun values budget _ => firstLabel_replay [] values budget)
      observation (by simp)
  · simp only [bitPredictor, sequenceTest, Nat.not_lt_zero, ite_false, trialPredictor,
      map_bind, map_pure, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
      Bool.false_eq_true]
    simp only [PMF.bind_const]
    exact PMF.uniformOfFintype_map_equiv Bool.involutive_not.toPerm

-- Arbitrary source algorithms with bounded observations obey the same storage bound.
example (source : ProbComp (List Bool × Bool)) (base : List Bool) (count c d width gap : ℕ)
    (params : Parameters) (state : State) (evaluate : List Bool → List Bool → Bool)
    (hwidth : ∀ value ∈ (ProbComp.eval source).support, value.1.length ≤ width)
    {code : List Bool}
    (hcode : code ∈ (ProbComp.eval (SequenceLearner.learn evaluate source base count c d width
      gap params state)).support) :
    code.length ≤ SavedPrediction.codeBound base.length count c d width + 1 :=
  SequenceLearner.learn_length_le evaluate source base count c d width gap params state hwidth hcode

-- Natural observations use their supplied encoding, with no decoder premise.
example : IsPPTOn encBits encBits (fun word =>
    SavedPrediction.sample encUnary word (pure (word.length, false))
      (pure (word.length + 1, true)) (word.length + 2) 1 2 (word.length + 1)) := by ppt

-- A full adaptive learner remains an ordinary functional program.
example : IsPPTOn encBits encBool (fun word =>
    SequenceLearner.predict (fun code observation => listStrictMajority (code ++ observation))
      (pure (word, true)) word (word.length + 1) 1 2 word.length (word.length + 2)
      (SequenceLearner.parameters (word.length + 10) 1 0 (word.length + 2)
        (SavedPrediction.codeBound word.length (word.length + 1) 1 2 word.length + 1))
      word.reverse) := by ppt

example : IsPPTOn (encList encBool) encBool (fun word => do
    let count := word.length + 1
    let gap := word.length + 2
    let bound := SavedPrediction.codeBound word.length count 1 2 word.length + 1
    let params := SequenceLearner.parameters (word.length + 10) 1 0 gap bound
    SequenceLearner.predict (fun code observation => listStrictMajority (code ++ observation))
      (pure (word, true)) word count 1 2 word.length gap params word.reverse) := by ppt

-- The numerical contract has concrete instances, independently of the unknown fixed clock.
example (confidence c d : ℕ) :
    (SequenceLearner.parameters confidence 1 0 4
      (SavedPrediction.codeBound 0 1 c d 0 + 1)).Valid := by
  simp [SequenceLearner.parameters, Parameters.Valid, Parameters.denominator, dyadicSize]

-- One actual sequence test supplies one evaluator for every boosting state and observation.
-- The parameter encoding is arbitrary; this construction never asks for its inverse.
example {Param : Type} (input : Param ↪ List Bool) :
    ∃ (c d : ℕ) (evaluate : List Bool → List Bool → Bool),
      ComputableInPolyTime (fun pair => evaluate pair.1 pair.2)
        (encPair encBits encBits) encBool ∧
      ∀ a (params : Parameters) (state : State) (observation : List Bool),
        ProbComp.eval ((fun code => evaluate code observation) <$>
          SequenceLearner.candidates (signedPredict evaluate) (pure ([], true))
            (input a) 3 c d observation.length params state) =
          ProbComp.eval (maskedSequencePredictor (pure ()) (fun _ => []) (fun _ => true)
            (fun _ => SequenceLearner.mask (signedPredict evaluate) params state ([], true))
            3 (fun values => pure (values.headD ([], false)).2) observation) := by
  have htest : IsPPTOn (encPair input (encList (encPair encBits encBool))) encBool
      (fun pair : Param × List (List Bool × Bool) => pure (pair.2.headD ([], false)).2) := by
    fun_prop
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := SequenceLearner.exists_evaluator
    (test := fun (_ : Param) values => pure (values.headD ([], false)).2) htest
  refine ⟨c, d, evaluate, hefficient, ?_⟩
  intro a params state observation
  simpa only [map_pure] using hrealize a (pure ()) (fun _ => []) (fun _ => true)
    3 observation.length params state observation le_rfl

end ComplexityTests.SavedPrediction
