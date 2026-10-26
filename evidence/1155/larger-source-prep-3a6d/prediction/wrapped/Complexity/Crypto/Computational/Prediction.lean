/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Basic
import Complexity.Probability.PMF.Event
import Complexity.Languages.Probabilistic.Notation
import Complexity.Probability.PMF
import Complexity.Tactic.PPT
import Diag1155.Wrapper

/-!
# Predicting a bit from a distinguishing test

The predictor supplies a trial bit to a test and returns that bit on acceptance, or its complement
on rejection. Averaging over an independent fair trial turns the test's signed distinguishing gap
into prediction bias. The hidden bit is not an input to the predictor.

`Pr[p]` is the scoped notation of `Cslib.Probability` for the probability, in the reals, that `p`
returns `true`, so gaps and biases are signed differences.

## Main definitions

* `Cslib.Crypto.trialPredictor`: prediction using a fixed trial bit.
* `Cslib.Crypto.bitPredictor`: prediction using an independent fair trial.
* `Cslib.Crypto.calibratedTest`: orient a test with a fresh real-or-ideal reference.

## Main results

* `Cslib.Crypto.trialPredictor_gap`: the gap is the average of two signed prediction biases.
* `Cslib.Crypto.bitPredictor_bias`: a randomized trial realizes that average.
* `Cslib.Crypto.probability_calibratedTest`: exact acceptance probability of `calibratedTest`.
* `Cslib.Crypto.calibratedTest_gap`: calibration squares the distinguishing advantage.

## References

* [L. Trevisan, *CS276 Lecture 13: Pseudorandom Generators*][Trevisan2009PRG],
  scribed by Siu-On Chan, the prediction reduction in Theorem 2.

Adapted from Crypto/Computational/Prediction.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Predict a trial bit on acceptance and its complement on rejection. -/
def trialPredictor (test : Bool → ProbComp Bool) (trial : Bool) : ProbComp Bool :=
  (fun accept => if accept then trial else !trial) <$> test trial

/-- A fresh fair trial gives one uniform predictor from a bit test. -/
noncomputable def bitPredictor (test : Bool → ProbComp Bool) : ProbComp Bool := do
  let trial ← ProbComp.uniform Bool
  trialPredictor test trial

/-- The two fixed trials recover the test's signed distinguishing gap. -/
theorem trialPredictor_gap (test : Bool → ProbComp Bool) (truth : Bool) :
    Pr[test truth] - (Pr[test false] + Pr[test true]) / 2 =
      (Pr[(fun guess => guess == truth) <$> trialPredictor test false] +
        Pr[(fun guess => guess == truth) <$> trialPredictor test true] - 1) / 2 := by
  cases truth with
  | false =>
    simp only [trialPredictor, Bool.not_false, Bool.not_true, beq_false,
      Functor.map_map, Bool.ite_true_right, Bool.ite_false_right, Bool.decide_eq_true,
      Bool.or_false, Bool.and_true, Bool.not_not, id_map', ProbComp.probability_not]
    ring
  | true =>
    simp only [beq_true, trialPredictor, Bool.not_false, Bool.ite_true_right,
      Bool.decide_eq_true, Bool.or_false, Functor.map_map, Bool.not_true, Bool.ite_false_right,
      Bool.and_true, id_map']
    rw [show (fun accept => !accept) = Bool.not from rfl, ProbComp.probability_not]
    ring

/-- Randomizing the trial averages the two fixed predictors' correctness probabilities. -/
theorem probability_bitPredictor (test : Bool → ProbComp Bool) (truth : Bool) :
    Pr[(fun guess => guess == truth) <$> bitPredictor test] =
      (Pr[(fun guess => guess == truth) <$> trialPredictor test false] +
        Pr[(fun guess => guess == truth) <$> trialPredictor test true]) / 2 := by
  simp only [bitPredictor, map_bind, ProbComp.eval_bind, ProbComp.eval_uniform,
    PMF.bind_apply_toReal]
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]
  ring

/-- The randomized predictor's bias equals the gap between the real label and a fair label. -/
theorem bitPredictor_bias (test : Bool → ProbComp Bool) (truth : Bool) :
    Pr[(fun guess => guess == truth) <$> bitPredictor test] - 1 / 2 =
      Pr[test truth] - (Pr[test false] + Pr[test true]) / 2 := by
  rw [probability_bitPredictor, trialPredictor_gap]
  ring

/-- Trial prediction charges for both the supplied bit and the complete test. -/
@[program_certificate]
theorem isPPTOn_trialPredictor {α : Type} {input : α ↪ List Bool}
    {test : α → Bool → ProbComp Bool} {trial : α → Bool}
    (htest : IsPPTOn (encPair input encBool) encBool (fun pair => test pair.1 pair.2))
    (htrial : ComputableInPolyTime trial input encBool) :
    IsPPTOn input encBool (fun a => trialPredictor (test a) (trial a)) := by
  unfold trialPredictor
  diag1155_call "cc9325cb5abc5af6a" => ppt

/-- A certified test gives a strict PPT predictor without a length-dependent choice of trial. -/
@[program_certificate]
theorem isPPTOn_bitPredictor {α : Type} {input : α ↪ List Bool}
    {test : α → Bool → ProbComp Bool}
    (htest : IsPPTOn (encPair input encBool) encBool (fun pair => test pair.1 pair.2)) :
    IsPPTOn input encBool (fun a => bitPredictor (test a)) := by
  unfold bitPredictor
  diag1155_call "cf6137f959648d1b6" => ppt

/-- Use a fresh real-or-ideal trial to orient a challenge test without knowing its gap's sign. -/
noncomputable def calibratedTest (real ideal challenge : ProbComp Bool) : ProbComp Bool := do
  let direction ← bitPredictor (fun trial => if trial then real else ideal)
  (fun result => result == direction) <$> challenge

/-- Calibration multiplies the challenge's bias by the signed gap of the reference games. -/
theorem probability_calibratedTest (real ideal challenge : ProbComp Bool) :
    Pr[calibratedTest real ideal challenge] =
      1 / 2 + (Pr[real] - Pr[ideal]) *
        (Pr[challenge] - 1 / 2) := by
  let direction := bitPredictor (fun trial => if trial then real else ideal)
  have htotal := PMF.toReal_true_add_toReal_false (ProbComp.eval direction)
  have hbias := bitPredictor_bias (fun trial => if trial then real else ideal) true
  simp only [beq_true, id_map', ite_true, Bool.false_eq_true, ite_false] at hbias
  simp only [calibratedTest, ProbComp.probability_bind, Fintype.sum_bool, beq_false,
    beq_true, id_map', ProbComp.probability_not]
  linear_combination (1 - Pr[challenge]) * htotal +
    (2 * Pr[challenge] - 1) * hbias

/-- The same calibration on both sides turns a possibly negative gap into its square. -/
theorem calibratedTest_gap (real ideal : ProbComp Bool) :
    Pr[calibratedTest real ideal real] -
      Pr[calibratedTest real ideal ideal] =
      (Game.advantage (ProbComp.eval real) (ProbComp.eval ideal) : ℝ) ^ 2 := by
  simp only [probability_calibratedTest, Game.coe_advantage, Game.coe_succProbability, sq_abs]
  ring

/-- Calibration is an ordinary PPT composition of its three supplied experiments. -/
@[program_certificate]
theorem isPPTOn_calibratedTest {α : Type} {input : α ↪ List Bool}
    {real ideal challenge : α → ProbComp Bool}
    (hreal : IsPPTOn input encBool real)
    (hideal : IsPPTOn input encBool ideal)
    (hchallenge : IsPPTOn input encBool challenge) :
    IsPPTOn input encBool
      (fun a => calibratedTest (real a) (ideal a) (challenge a)) := by
  unfold calibratedTest
  diag1155_call "ccec1794f7ac5fb4b" => ppt

end Cslib.Crypto
