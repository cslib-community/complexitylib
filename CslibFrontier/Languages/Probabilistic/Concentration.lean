/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Repeat
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Concentration

/-!
# Estimating acceptance probabilities by repeated trials

The success counter is an ordinary probabilistic program. Its independent product law gives
Hoeffding bounds for the count and for its empirical acceptance probability. Division and real
numbers occur only in the specification: the program returns a natural number.

`Cslib.Computability.Probabilistic.Repeat` supplies the separate strict PPT certificate whenever
the trial program and its unary repetition count are efficient.

## Main results

* `Cslib.ProbComp.countTrue_average_deviation_pow`: exponentially accurate empirical rates
  with a polynomial trial budget in the confidence and inverse tolerance.
* `Cslib.ProbComp.testProbabilityLT_error_pow_of_bounds`: rational threshold tests satisfy
  overlapping postconditions except with exponentially small probability.
* `Cslib.ProbComp.replicate_failure_pow`: repeated sampling finds a good value with high
  probability; its proof predicate need not be computable.

## References

Adapted from Languages/Probabilistic/Concentration.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. The concentration estimate is the finite-product
bound from `Probability.Concentration`, following [Hoeffding][Hoeffding1963].
-/

@[expose] public section

namespace Cslib.ProbComp

/-- A repeated success count deviates from its mean with exponentially small probability.
This unnormalized bound also holds at count zero. -/
theorem countTrue_deviation (count : ℕ) (program : ProbComp Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((eval (OracleComp.countTrue count program)).toOuterMeasure {successes |
      ε ≤ |(successes : ℝ) - count * (eval program true).toReal|}).toReal ≤
        2 * Real.exp (-2 * ε ^ 2 / count) := by
  rw [eval_countTrue, PMF.toOuterMeasure_map_apply]
  have h := Probability.PMF.pi_sum_abs_sub_mean_ge (fun _ : Fin count => eval program)
    (fun _ bit => (bit.toNat : ℝ)) (bound := 1) (by norm_num)
    (by intro i bit _; cases bit <;> norm_num) hε
  simpa [Set.preimage_ofPred_eq, Nat.cast_sum, Fintype.sum_bool] using h

/-- The empirical acceptance probability estimates the true probability to additive tolerance
`ε`, with failure at most `2 exp (-2 * count * ε²)`. The count must be positive. -/
theorem countTrue_average_deviation (count : ℕ) (hcount : 0 < count)
    (program : ProbComp Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((eval (OracleComp.countTrue count program)).toOuterMeasure {successes |
      ε ≤ |(successes : ℝ) / count - (eval program true).toReal|}).toReal ≤
        2 * Real.exp (-2 * count * ε ^ 2) := by
  have hc : (0 : ℝ) < count := by exact_mod_cast hcount
  have hevent : {successes : ℕ |
      ε ≤ |(successes : ℝ) / count - (eval program true).toReal|} =
      {successes : ℕ | (count : ℝ) * ε ≤
        |(successes : ℝ) - count * (eval program true).toReal|} := by
    ext successes
    simp only [Set.mem_ofPred_eq]
    rw [show (successes : ℝ) / count - (eval program true).toReal =
      (successes - count * (eval program true).toReal) / count by field_simp,
      abs_div, abs_of_pos hc, le_div_iff₀ hc, mul_comm ε]
  rw [hevent]
  calc
    _ ≤ 2 * Real.exp (-2 * ((count : ℝ) * ε) ^ 2 / count) :=
      countTrue_deviation count program (mul_nonneg hc.le hε)
    _ = _ := by
      congr 2
      field_simp

/-- A polynomial trial budget gives inverse-polynomial accuracy and exponentially small failure.
Both parameters are natural numbers, so a client can compute the budget with unary arithmetic. -/
theorem countTrue_average_deviation_pow (confidence inverseTolerance : ℕ)
    (htolerance : 0 < inverseTolerance) (program : ProbComp Bool) :
    ((eval (OracleComp.countTrue ((confidence + 1) * inverseTolerance ^ 2) program)).toOuterMeasure
      {successes | (1 : ℝ) / inverseTolerance ≤
        |(successes : ℝ) / ((confidence + 1) * inverseTolerance ^ 2 : ℕ) -
          (eval program true).toReal|}).toReal ≤ (1 / 2 : ℝ) ^ confidence := by
  have ht : (0 : ℝ) < inverseTolerance := by exact_mod_cast htolerance
  have h := countTrue_average_deviation ((confidence + 1) * inverseTolerance ^ 2)
    (by positivity) program (ε := 1 / inverseTolerance) (by positivity)
  have hexponent : -2 * (((confidence + 1) * inverseTolerance ^ 2 : ℕ) : ℝ) *
      (1 / inverseTolerance) ^ 2 = -2 * (confidence + 1) := by
    push_cast
    field_simp
  rw [hexponent] at h
  refine h.trans ?_
  have hexp : Real.exp (-2) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 2)]
    linarith [Real.add_one_le_exp 2]
  rw [mul_comm (-2), ← Nat.cast_add_one, Real.exp_nat_mul]
  calc
    _ ≤ 2 * (1 / 2 : ℝ) ^ (confidence + 1) := by gcongr
    _ = _ := by rw [pow_succ]; ring

/-- Polynomially many independent draws find a good value except with exponentially small
probability whenever one draw succeeds with inverse-polynomial probability. The predicate is
used only in the proof and need not be efficiently decidable. -/
theorem replicate_failure_pow {α : Type} (source : ProbComp α) (good : α → Prop)
    (confidence inverseSuccess : ℕ) (hinverse : 0 < inverseSuccess)
    (hsuccess : (1 : ℝ) / inverseSuccess ≤
      ((eval source).toOuterMeasure {value | good value}).toReal) :
    ((eval (OracleComp.replicate ((confidence + 1) * inverseSuccess ^ 2) source)).toOuterMeasure
      {values | ¬ ∃ value ∈ values, good value}).toReal ≤ (1 / 2 : ℝ) ^ confidence := by
  classical
  have hgood : (eval ((fun value => decide (good value)) <$> source) true).toReal =
      ((eval source).toOuterMeasure {value | good value}).toReal := by
    rw [eval_map, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 2
    ext value
    simp
  have h := countTrue_average_deviation_pow confidence inverseSuccess hinverse
    ((fun value => decide (good value)) <$> source)
  rw [hgood] at h
  simp only [OracleComp.countTrue, OracleComp.replicate_map, Functor.map_map, eval_map,
    PMF.toOuterMeasure_map_apply] at h
  refine le_trans ?_ h
  apply ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro values hbad
  have hzero : (values.map (fun value => decide (good value))).count true = 0 := by
    rw [List.count_eq_zero]
    simpa only [List.mem_map, decide_eq_true_eq, Set.mem_ofPred_eq] using hbad
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hzero, Nat.cast_zero, zero_div, zero_sub,
    abs_neg, abs_of_nonneg ENNReal.toReal_nonneg] using hsuccess

/-- An invalid threshold decision requires the empirical rate to miss the true probability
by at least the permitted tolerance. Both answers are valid inside the overlap interval. -/
private theorem testProbabilityLT_error_le_deviation (count numerator denominator : ℕ)
    (hcount : 0 < count) (hdenominator : 0 < denominator) (program : ProbComp Bool) (ε : ℝ) :
    ((eval (OracleComp.testProbabilityLT count numerator denominator program)).toOuterMeasure
      {below | ¬ if below then (eval program true).toReal ≤ numerator / denominator + ε
        else numerator / denominator - ε ≤ (eval program true).toReal}).toReal ≤
      ((eval (OracleComp.countTrue count program)).toOuterMeasure {successes |
        ε ≤ |(successes : ℝ) / count - (eval program true).toReal|}).toReal := by
  have hc : (0 : ℝ) < count := by exact_mod_cast hcount
  have hd : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
  rw [OracleComp.testProbabilityLT, eval_map, PMF.toOuterMeasure_map_apply]
  apply ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro successes hbad
  have hcompare : successes * denominator < count * numerator ↔
      (successes : ℝ) / count < (numerator : ℝ) / denominator := by
    rw [div_lt_div_iff₀ hc hd]
    norm_cast
    rw [Nat.mul_comm count]
  change ε ≤ |(successes : ℝ) / count - (eval program true).toReal|
  by_cases htest : successes * denominator < count * numerator
  · have hlt := hcompare.mp htest
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, htest, decide_true, ite_true, not_le] at hbad
    exact le_abs.mpr (Or.inr (by linarith))
  · have hle := le_of_not_gt (hcompare.not.mp htest)
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, htest, decide_false,
      Bool.false_eq_true, ite_false, not_le] at hbad
    exact le_abs.mpr (Or.inl (by linarith))

/-- Except with the Hoeffding error, a true test result implies the probability is at most
the threshold plus tolerance; a false result implies it is at least the threshold minus tolerance.
-/
theorem testProbabilityLT_error (count numerator denominator : ℕ)
    (hcount : 0 < count) (hdenominator : 0 < denominator)
    (program : ProbComp Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((eval (OracleComp.testProbabilityLT count numerator denominator program)).toOuterMeasure
      {below | ¬ if below then (eval program true).toReal ≤ numerator / denominator + ε
        else numerator / denominator - ε ≤ (eval program true).toReal}).toReal ≤
      2 * Real.exp (-2 * count * ε ^ 2) :=
  (testProbabilityLT_error_le_deviation _ _ _ hcount hdenominator program ε).trans
    (countTrue_average_deviation count hcount program hε)

/-- The rational threshold test has a polynomial trial budget and exponentially small error. -/
theorem testProbabilityLT_error_pow (confidence inverseTolerance numerator denominator : ℕ)
    (htolerance : 0 < inverseTolerance) (hdenominator : 0 < denominator)
    (program : ProbComp Bool) :
    ((eval (OracleComp.testProbabilityLT ((confidence + 1) * inverseTolerance ^ 2)
      numerator denominator program)).toOuterMeasure
        {below | ¬ if below then
          (eval program true).toReal ≤ numerator / denominator + 1 / inverseTolerance
          else numerator / denominator - 1 / inverseTolerance ≤
            (eval program true).toReal}).toReal ≤ (1 / 2 : ℝ) ^ confidence :=
  (testProbabilityLT_error_le_deviation _ numerator denominator (by positivity)
    hdenominator program (1 / inverseTolerance)).trans
      (countTrue_average_deviation_pow confidence inverseTolerance htolerance program)

/-- A threshold test may target wider, overlapping postconditions. This form lets clients
use the bounds required by an algorithm without carrying its sampling tolerance further. -/
theorem testProbabilityLT_error_pow_of_bounds
    (confidence inverseTolerance numerator denominator : ℕ)
    (htolerance : 0 < inverseTolerance) (hdenominator : 0 < denominator)
    (program : ProbComp Bool) {lower upper : ℝ}
    (hlower : lower ≤ (numerator : ℝ) / denominator - 1 / inverseTolerance)
    (hupper : (numerator : ℝ) / denominator + 1 / inverseTolerance ≤ upper) :
    ((eval (OracleComp.testProbabilityLT ((confidence + 1) * inverseTolerance ^ 2)
      numerator denominator program)).toOuterMeasure
        {below | ¬ if below then (eval program true).toReal ≤ upper
          else lower ≤ (eval program true).toReal}).toReal ≤ (1 / 2 : ℝ) ^ confidence := by
  refine (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono ?_)).trans
      (testProbabilityLT_error_pow confidence inverseTolerance numerator denominator
        htolerance hdenominator program)
  intro below hbad
  cases below <;> simp_all only [Set.mem_ofPred_eq, Bool.false_eq_true, ite_false, ite_true]
  · exact fun h => hbad (hlower.trans h)
  · exact fun h => hbad (h.trans hupper)

end Cslib.ProbComp
