/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Repeat
import Complexity.Languages.Probabilistic.Concentration
import Complexity.Tactic.PPT

/-! Empirical probability tests: functional certificates, independent trials and boundary laws. -/

namespace ComplexityTests.EmpiricalProbability

open Cslib Cslib.Probability Turing.MultiTapeTM

-- Computed labels and captured predicates work for ordinary framed lists.
example : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1.count p.2)
    (encPair (encList encUnary) encUnary) encUnary := by fun_prop

example : ComputableTidilyInPolyTime
    (fun p : List ℕ × ℕ => p.1.countP (fun n => decide (n ≤ p.2 + 1)))
    (encPair (encList encUnary) encUnary) encUnary := by polytime

-- Equivalent spellings, with both raw and framed bit-list inputs.
example : ComputableTidilyInPolyTime (fun word : List Bool => word.count true)
    encBits encUnary := by fun_prop
example : ComputableTidilyInPolyTime (fun word : List Bool => word.countP (· == true))
    encBits encUnary := by polytime
example : ComputableTidilyInPolyTime (fun word : List Bool => word.count true)
    (encList encBool) encUnary := by fun_prop

private noncomputable def sampledTest (word : List Bool) : ProbComp Bool :=
  OracleComp.testProbabilityLT ((word.length + 1) ^ 3) (word.count true + 1) (word.length + 2) (do
    let candidate ← BitString.sampleList word.length
    return decide ((candidate ++ word).count true < word.length + 1))

example : IsPPTOn encBits encBool sampledTest := by
  unfold sampledTest
  ppt

example : IsPPTOn (encList encBool) encBool sampledTest := by
  unfold sampledTest
  ppt

-- Ordinary map spelling also composes with the same counting and repetition rules.
example : IsPPTOn encBits encUnary (fun word =>
    List.count true <$> OracleComp.replicate (word.length + 2)
      ((fun bits => decide (bits.count true ≤ word.count true)) <$>
        BitString.sampleList word.length)) := by ppt

-- Zero trials perform no sampling; a zero denominator is total, without an accuracy claim.
example (program : ProbComp Bool) : OracleComp.countTrue 0 program = pure 0 := by
  simp [OracleComp.countTrue]

example (program : ProbComp Bool) (count : ℕ) :
    ProbComp.eval (OracleComp.testProbabilityLT count 0 0 program) = PMF.pure false := by
  simp only [OracleComp.testProbabilityLT, Nat.mul_zero, lt_self_iff_false, decide_false,
    ProbComp.eval_map]
  exact PMF.map_const _ _

-- One success in two fair trials has probability one half, ruling out reused randomness.
example : ProbComp.eval (OracleComp.countTrue 2 (ProbComp.uniform Bool)) 1 = 1 / 2 := by
  norm_num [OracleComp.countTrue, OracleComp.replicate_succ, ProbComp.eval_map,
    ProbComp.eval_bind, ProbComp.eval_uniform, PMF.map, PMF.bind_apply, tsum_fintype,
    PMF.uniformOfFintype_apply, PMF.pure_apply, ← ENNReal.mul_inv]
  convert ENNReal.add_halves ((2 : ENNReal)⁻¹) using 1
  norm_num [div_eq_mul_inv, ← ENNReal.mul_inv]

-- A distribution certificate transports an independently implemented sampler. Neither the
-- infinite ambient type nor the many-to-one encoding requires a decoding operation.
example (count : ℕ) :
    ProbComp.eval (OracleComp.replicate count (pure 7 : ProbComp ℕ)) =
      (ProbComp.eval (OracleComp.replicate count
        (Bool.toNat <$> ProbComp.uniform Bool))).map (List.map (fun _ => 7)) := by
  apply ProbComp.eval_replicate_map
  exact (PMF.map_const _ _).symm

example (confidence : ℕ) :
    ((ProbComp.eval (OracleComp.replicate ((confidence + 1) * 2 ^ 2)
      (ProbComp.uniform Bool))).toOuterMeasure {bits | ¬ ∃ bit ∈ bits, bit = true}).toReal ≤
        (1 / 2 : ℝ) ^ confidence := by
  apply ProbComp.replicate_failure_pow _ _ confidence 2 (by decide)
  norm_num [ProbComp.eval_uniform, PMF.toOuterMeasure_apply_fintype,
    Set.indicator_apply, Fintype.sum_bool, PMF.uniformOfFintype_apply]

-- Binary input size alone does not pay for exponentially many trials or unary counts.
example : True := by
  fail_if_success
    have : IsPPTOn encNat encUnary
        (fun count => OracleComp.countTrue count (ProbComp.uniform Bool)) := by ppt
  trivial

end ComplexityTests.EmpiricalProbability
