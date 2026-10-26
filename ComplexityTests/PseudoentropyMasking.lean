/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.Masking
import Complexity.Probability.BitString.List.Vote
import Complexity.Tactic.PPT

/-!
# Executable boosting masks and prediction reductions

Clipping endpoints, ties, hidden-label-dependent entropy and independent repetitions have
concrete clients. Certificate tests vary the spelling and encoding of the same vote computation,
and exercise captured parameters in the complete masked-sequence predictor.
-/

namespace ComplexityTests.PseudoentropyMasking

open Cslib Cslib.ProbComp Cslib.Probability Cslib.Probability.PMF Cslib.Crypto
  Cslib.Crypto.Pseudoentropy Cslib.Crypto.Pseudoentropy.Boosting Cslib.BitString Turing.MultiTapeTM

example : listStrictMajority [] = false ∧ listStrictMajority [true, false] = false ∧
    listNonpositiveMargin [true, false] true = true := by decide

example : weightNumerator 8 2 0 [] true = 8 ∧
    weightNumerator 8 2 0 [true] true = 6 ∧
    weightNumerator 8 2 0 [true, true, true, true, true] true = 0 := by decide

-- Zero rate, zero denominator and a large threshold still give total natural computations.
example : weightNumerator 8 0 0 [true] true = 8 ∧
    weightNumerator 0 1 0 [true] true = 0 ∧
    weightNumerator 8 2 100 [true] true = 8 := by decide

example : (ProbComp.eval (sampleWeight 1 1 0 [true] true) true).toReal = 1 / 2 := by
  rw [eval_sampleWeight_true]
  norm_num [Boosting.weight, listVoteMargin, dyadicSize]

example (truth : Bool) : ProbComp.eval (maskBit (pure false) truth) = PMF.pure truth := by
  simp [maskBit]

example (truth : Bool) : ProbComp.eval (maskBit (pure true) truth) = PMF.uniformOfFintype Bool := by
  simp [maskBit]

-- The observation hides the label, but the replacement probability may depend on it.
example : (1 / 2 : ℝ) ≤ conditionalEntropy (ProbComp.eval
    (maskedSample (ProbComp.uniform Bool) (fun _ => ()) id (fun bit => pure bit))) := by
  simpa [ProbComp.eval_uniform, Fintype.sum_bool, PMF.uniformOfFintype_apply] using
    maskedSample_entropy_ge (ProbComp.uniform Bool) (fun _ => ()) id (fun bit => pure bit)

-- Two occurrences of the same input draw independent masks and replacement bits.
example : (ProbComp.eval (do
    let first ← maskBit (ProbComp.uniform Bool) false
    let second ← maskBit (ProbComp.uniform Bool) false
    pure (first && second)) true).toReal = 1 / 16 := by
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, bind_apply_toReal, Fintype.sum_bool]
  norm_num [eval_maskBit_apply, ProbComp.eval_uniform, PMF.uniformOfFintype_apply, PMF.pure_apply]

-- One feasible no-shift round has positive density and correlation.
example : averagePotential (PMF.pure ()) ((1 / 2) * (1 / 2)) (fun _ => 1) ≤
    averagePotential (PMF.pure ()) ((1 / 2) * (1 / 2)) (fun _ => 0) -
      (1 / 2) * (1 / 2) ^ 2 / 8 := by
  have h := step_progress (PMF.pure ()) (γ := 1 / 2) (δ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => 0) (fun _ => 1)
    (by simp) false (by simp) (by simp) (by norm_num)
    (by norm_num [density, Boosting.weight])
  simpa using h

-- One real coordinate and one padding coordinate give bias 1/4, not 1/2.
example : (Game.succProbability (ProbComp.eval
    (maskedSequencePredictor (pure ()) (fun _ => ()) (fun _ => true) (fun _ => pure true)
      1 (fun samples => pure (samples.any Prod.snd)) ())) : ℝ) = 3 / 4 := by
  have h := maskedSequence_prediction_gap (pure ()) (fun _ => ()) (fun _ => true)
    (fun _ => pure true) 1 (fun samples => pure (samples.any Prod.snd))
  norm_num [dyadicSize, OracleComp.replicate_succ, OracleComp.replicate_zero,
    maskedSample, maskBit, map_bind, bind_assoc, ProbComp.eval_uniform,
    Game.succProbability, PMF.uniformOfFintype_apply, ProbComp.eval_bind,
    bind_apply_toReal, Fintype.sum_bool, ProbComp.eval_pure, PMF.pure_apply,
    ENNReal.toNNReal_ofNat] at h
  rw [Game.coe_succProbability]
  linarith

-- All progress inequalities can hold at equality, including the exact four-round clock.
example : (1 / 2 : ℝ) ≤ 4 / 8 := by
  have havg (i : ℕ) : averagePotential (PMF.pure ()) 1
      (fun _ => (i : ℝ) / 8 - i) = 1 / 2 + 7 * i / 8 := by
    simp only [averagePotential, Fintype.sum_unique, PMF.pure_apply_self,
      ENNReal.toReal_one, one_mul]
    rw [potential_of_nonpos 1 (by have := Nat.cast_nonneg (α := ℝ) i; linarith)]
    ring
  have h := dense_margin_of_iterations (PMF.pure ()) (γ := 1) (δ := 1)
    (by norm_num) (by norm_num) (fun i _ => (i : ℝ) / 8) (fun i => i) 4
    (by funext x; norm_num) (by norm_num) (by norm_num)
    (by
      intro i hi
      norm_num only [mul_one]
      rw [havg, havg]
      push_cast
      linarith)
    (by norm_num) (fun _ => 1) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

example : ComputableInPolyTime
    (fun votes : List Bool => listNonpositiveMargin votes (listStrictMajority votes))
    encBits encBool := by fun_prop

example : ComputableInPolyTime
    (fun votes : List Bool => listNonpositiveMargin votes (listStrictMajority votes))
    (encList encBool) encBool := by polytime

example : ComputableInPolyTime
    (fun votes : List Bool => weightNumerator (votes.length + 1) 1 0 votes true)
    encBits encUnary := by polytime

-- The same expression with a framed list encoding.
example : ComputableInPolyTime
    (fun votes : List Bool => weightNumerator (votes.length + 1) 1 0 votes true)
    (encList encBool) encUnary := by polytime

example : ComputableInPolyTime (fun input : ℕ × List Bool =>
    let votes := input.2
    weightNumerator (input.1 + 1) 1 0 votes (listStrictMajority votes))
    (encPair encUnary encBits) encUnary := by polytime

example : IsPPTOn (encPair encUnary encBits) encBool (fun input : ℕ × List Bool =>
    sampleWeight input.1 1 0 input.2 (listStrictMajority input.2)) := by ppt

example : IsPPTOn (encPair encUnary (encList encBool)) encBool (fun input : ℕ × List Bool =>
    sampleWeight input.1 1 0 input.2 (listStrictMajority input.2)) := by ppt

example : IsPPTOn (encPair encUnary encBits) encBool (fun input : ℕ × List Bool => do
    let votes := input.2
    let numerator := weightNumerator (dyadicSize input.1) 1 0 votes (listStrictMajority votes)
    sampleDyadicCoin input.1 numerator) := by ppt

example : IsPPTOn (encPair encUnary encBits) (encPair encBits encBool)
    (fun input : ℕ × List Bool => maskedSample (BitString.sampleList input.1)
      (fun sample => input.2 ++ sample) listStrictMajority
      (fun sample =>
        sampleWeight input.1 1 input.2.length sample (listStrictMajority sample))) := by
  ppt

-- The challenge is only an observation; all other labels are generated on fresh source draws.
example : IsPPTOn (encPair encUnary encBool) encBool (fun input : ℕ × Bool =>
    maskedSequencePredictor (ProbComp.uniform Bool) id id (fun _ => ProbComp.uniform Bool)
      input.1 (fun samples => pure (samples.any fun pair => pair.1 ^^ pair.2)) input.2) := by
  ppt

end ComplexityTests.PseudoentropyMasking
