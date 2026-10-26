/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Sampling
import Complexity.Probability.PMF.Event
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Probability.BitString.List.Vote
import Complexity.Languages.Probabilistic.Concentration
import Complexity.Tactic.PPT

/-!
# Sampled decisions for uniform hard-core boosting

`testShift` estimates the soft density and decides whether to raise the threshold.
`testMajority` estimates the probability of a nonpositive raw vote margin and decides whether
the majority predictor is already good enough. Both tests use natural counts and rational
cross-products, have strict PPT certificates, and meet the overlapping guards except with
probability at most `2⁻ᵏ` for confidence parameter `k`.

The trial programs are explicit inputs: they must sample fresh examples and evaluate the
relevant weight or margin predicate. `sampleWeight_density` supplies the density correspondence.
The collection's worst-dense-set stopping test is not implemented here; the finite boosting
clock provides a separate route to a dense-margin guarantee at the final round.

## Main definitions

* `testShift`, `testMajority`: rational tests of soft density and raw-margin error.

## Main results

* `testShift_weights_sound`, `testMajority_source_sound`: guards for the boosting loop.
* `isPPTOn_testShift`, `isPPTOn_testMajority`: strict computational certificates.

## References

[Holenstein2005], Section 2.2, Figure 2 and Claim 2.6. The test thresholds are midpoints of the
pairs of overlapping guards. Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.Boosting

open Probability BitString Turing.MultiTapeTM

/-- Test whether the soft density is small enough to raise the vote threshold. With density
parameter `δ` and weight rate `η`, the comparison threshold is `δ (1 + η / 32)`. -/
def testShift (confidence inverseTolerance densityNumerator densityDenominator
    rateNumerator rateDenominator : ℕ) (trial : ProbComp Bool) : ProbComp Bool :=
  OracleComp.testProbabilityLT ((confidence + 1) * inverseTolerance ^ 2)
    (densityNumerator * (32 * rateDenominator + rateNumerator))
    (32 * densityDenominator * rateDenominator) trial

/-- Test whether the nonpositive-margin probability is small enough to return the majority
predictor. The threshold `13δ / 32` lies midway between `3δ / 8` and `7δ / 16`. -/
def testMajority (confidence inverseTolerance densityNumerator densityDenominator : ℕ)
    (trial : ProbComp Bool) : ProbComp Bool :=
  OracleComp.testProbabilityLT ((confidence + 1) * inverseTolerance ^ 2)
    (13 * densityNumerator) (32 * densityDenominator) trial

/-- The sampled shift decision satisfies the density guards from Figure 2. Substituting
`rate = γδ` gives the upper guard `δ (1 + γδ / 16)` used by `step_progress`. -/
theorem testShift_sound (confidence inverseTolerance densityNumerator densityDenominator
    rateNumerator rateDenominator : ℕ) (trial : ProbComp Bool)
    (htolerance : 0 < inverseTolerance) (hdensity : 0 < densityDenominator)
    (hrate : 0 < rateDenominator)
    (hprecision : 1 / (inverseTolerance : ℝ) ≤
      (densityNumerator : ℝ) / densityDenominator * (rateNumerator / rateDenominator) / 32) :
    ((ProbComp.eval (testShift confidence inverseTolerance densityNumerator densityDenominator
      rateNumerator rateDenominator trial)).toOuterMeasure
        {shift | ¬ if shift then (ProbComp.eval trial true).toReal ≤
          (densityNumerator : ℝ) / densityDenominator *
            (1 + (rateNumerator : ℝ) / rateDenominator / 16)
          else (densityNumerator : ℝ) / densityDenominator ≤
            (ProbComp.eval trial true).toReal}).toReal ≤ (1 / 2 : ℝ) ^ confidence := by
  have hd : (0 : ℝ) < densityDenominator := by exact_mod_cast hdensity
  have hr : (0 : ℝ) < rateDenominator := by exact_mod_cast hrate
  have hcutoff : (↑(densityNumerator * (32 * rateDenominator + rateNumerator)) : ℝ) /
      ↑(32 * densityDenominator * rateDenominator) =
      (densityNumerator : ℝ) / densityDenominator *
        (1 + (rateNumerator : ℝ) / rateDenominator / 32) := by
    push_cast
    field_simp
  unfold testShift
  apply ProbComp.testProbabilityLT_error_pow_of_bounds confidence inverseTolerance _ _
    htolerance (by positivity) trial <;> rw [hcutoff] <;> nlinarith [hprecision]

/-- The sampled majority decision satisfies the two majority guards from Figure 2. -/
theorem testMajority_sound (confidence inverseTolerance densityNumerator densityDenominator : ℕ)
    (trial : ProbComp Bool) (htolerance : 0 < inverseTolerance)
    (hdensity : 0 < densityDenominator)
    (hprecision : 1 / (inverseTolerance : ℝ) ≤
      (densityNumerator : ℝ) / densityDenominator / 32) :
    ((ProbComp.eval (testMajority confidence inverseTolerance
      densityNumerator densityDenominator trial)).toOuterMeasure
        {stop | ¬ if stop then (ProbComp.eval trial true).toReal ≤
          7 * ((densityNumerator : ℝ) / densityDenominator) / 16
          else 3 * ((densityNumerator : ℝ) / densityDenominator) / 8 ≤
            (ProbComp.eval trial true).toReal}).toReal ≤ (1 / 2 : ℝ) ^ confidence := by
  have hd : (0 : ℝ) < densityDenominator := by exact_mod_cast hdensity
  have hcutoff : (↑(13 * densityNumerator) : ℝ) / ↑(32 * densityDenominator) =
      13 * ((densityNumerator : ℝ) / densityDenominator) / 32 := by
    push_cast
    field_simp
  unfold testMajority
  apply ProbComp.testProbabilityLT_error_pow_of_bounds confidence inverseTolerance _ _
    htolerance (by positivity) trial <;> rw [hcutoff] <;> linarith

/-- When the trial draws an example and tests its votes, a valid stopping decision certifies
the actual majority predictor. A valid continuation certifies the raw-margin lower guard. -/
theorem testMajority_source_sound {α : Type} (source : ProbComp α)
    (votes : α → List Bool) (truth : α → Bool)
    (confidence inverseTolerance densityNumerator densityDenominator : ℕ)
    (htolerance : 0 < inverseTolerance) (hdensity : 0 < densityDenominator)
    (hprecision : 1 / (inverseTolerance : ℝ) ≤
      (densityNumerator : ℝ) / densityDenominator / 32) :
    ((ProbComp.eval (testMajority confidence inverseTolerance densityNumerator densityDenominator
      ((fun x => listNonpositiveMargin (votes x) (truth x)) <$> source))).toOuterMeasure
        {stop | ¬ if stop then
          ((ProbComp.eval source).toOuterMeasure
            {x | listStrictMajority (votes x) ≠ truth x}).toReal ≤
            7 * ((densityNumerator : ℝ) / densityDenominator) / 16
          else 3 * ((densityNumerator : ℝ) / densityDenominator) / 8 ≤
            ((ProbComp.eval source).toOuterMeasure
              {x | listVoteMargin (votes x) (truth x) ≤ 0}).toReal}).toReal ≤
      (1 / 2 : ℝ) ^ confidence := by
  have h := testMajority_sound confidence inverseTolerance densityNumerator densityDenominator
    ((fun x => listNonpositiveMargin (votes x) (truth x)) <$> source) htolerance hdensity hprecision
  simp only [ProbComp.eval_map, map_listNonpositiveMargin_true] at h
  refine (ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono ?_)).trans h
  intro stop hbad
  cases stop <;> simp only [Set.mem_ofPred_eq, Bool.false_eq_true, ite_false, ite_true] at hbad ⊢
  · exact hbad
  · exact fun hgood =>
      hbad ((listStrictMajority_error_le (ProbComp.eval source) votes truth).trans hgood)

/-- Fresh source examples and weight coins implement the density test used by the loop.
This connects the executable decision directly to the density from the potential proof. -/
theorem testShift_weights_sound {α : Type} [Fintype α] (source : ProbComp α)
    (votes : α → List Bool) (truth : α → Bool)
    (confidence inverseTolerance densityNumerator densityDenominator
      bound rateNumerator threshold : ℕ)
    (htolerance : 0 < inverseTolerance) (hdensity : 0 < densityDenominator)
    (hprecision : 1 / (inverseTolerance : ℝ) ≤
      (densityNumerator : ℝ) / densityDenominator * (rateNumerator / dyadicSize bound) / 32) :
    ((ProbComp.eval (testShift confidence inverseTolerance densityNumerator densityDenominator
      rateNumerator (dyadicSize bound)
        (source >>= fun x =>
          sampleWeight bound rateNumerator threshold (votes x) (truth x)))).toOuterMeasure
      {shift | ¬ if shift then
        density (ProbComp.eval source) (rateNumerator / dyadicSize bound)
          (fun x => listVoteMargin (votes x) (truth x) - threshold) ≤
            (densityNumerator : ℝ) / densityDenominator *
              (1 + (rateNumerator : ℝ) / dyadicSize bound / 16)
        else (densityNumerator : ℝ) / densityDenominator ≤
          density (ProbComp.eval source) (rateNumerator / dyadicSize bound)
            (fun x => listVoteMargin (votes x) (truth x) - threshold)}).toReal ≤
      (1 / 2 : ℝ) ^ confidence := by
  simpa only [ProbComp.eval_bind, sampleWeight_density] using
    testShift_sound confidence inverseTolerance densityNumerator densityDenominator
      rateNumerator (dyadicSize bound)
      (source >>= fun x => sampleWeight bound rateNumerator threshold (votes x) (truth x))
      htolerance hdensity (dyadicSize_pos bound) hprecision

/-- A natural upper bound on inverse density gives a sufficient majority-test tolerance. -/
theorem majority_precision_of_inverse (inverseDensity : ℕ) {δ : ℝ}
    (hdensity : 1 ≤ inverseDensity * δ) :
    (1 : ℝ) / (32 * inverseDensity : ℕ) ≤ δ / 32 := by
  have hi : 0 < inverseDensity := by
    by_contra h
    have hz : inverseDensity = 0 := by lia
    norm_num [hz] at hdensity
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (32 * inverseDensity : ℕ))).mpr
  push_cast
  nlinarith

/-- Natural inverse bounds give a sufficient shift-test tolerance when the weight rate is `γδ`.
The reciprocal precision and hence the number of trials remain polynomial in these bounds. -/
theorem shift_precision_of_inverse (inverseGamma inverseDensity : ℕ) {γ δ : ℝ}
    (hgamma : 1 ≤ inverseGamma * γ) (hdensity : 1 ≤ inverseDensity * δ) :
    (1 : ℝ) / (32 * inverseGamma * inverseDensity ^ 2 : ℕ) ≤ δ * (γ * δ) / 32 := by
  have hg : 0 < inverseGamma := by
    by_contra h
    have hz : inverseGamma = 0 := by lia
    norm_num [hz] at hgamma
  have hd : 0 < inverseDensity := by
    by_contra h
    have hz : inverseDensity = 0 := by lia
    norm_num [hz] at hdensity
  have hproduct := one_le_mul_of_one_le_of_one_le hgamma (one_le_pow₀ hdensity (n := 2))
  apply (div_le_iff₀
    (by positivity : (0 : ℝ) < (32 * inverseGamma * inverseDensity ^ 2 : ℕ))).mpr
  push_cast
  nlinarith

section Efficiency

variable {α : Type} {input : α ↪ List Bool} {trial : α → ProbComp Bool}
  {confidence inverseTolerance densityNumerator densityDenominator
    rateNumerator rateDenominator : α → ℕ}

/-- Efficient trials and unary parameters give a strict PPT shift decision. -/
theorem isPPTOn_testShift (htrial : IsPPTOn input encBool trial)
    (hconfidence : ComputableInPolyTime confidence input encUnary)
    (htolerance : ComputableInPolyTime inverseTolerance input encUnary)
    (hdensityNum : ComputableInPolyTime densityNumerator input encUnary)
    (hdensityDen : ComputableInPolyTime densityDenominator input encUnary)
    (hrateNum : ComputableInPolyTime rateNumerator input encUnary)
    (hrateDen : ComputableInPolyTime rateDenominator input encUnary) :
    IsPPTOn input encBool (fun a => testShift (confidence a) (inverseTolerance a)
      (densityNumerator a) (densityDenominator a)
      (rateNumerator a) (rateDenominator a) (trial a)) := by
  unfold testShift
  apply htrial.testProbabilityLT
  all_goals polytime

/-- Efficient trials and unary parameters give a strict PPT majority decision. -/
theorem isPPTOn_testMajority (htrial : IsPPTOn input encBool trial)
    (hconfidence : ComputableInPolyTime confidence input encUnary)
    (htolerance : ComputableInPolyTime inverseTolerance input encUnary)
    (hdensityNum : ComputableInPolyTime densityNumerator input encUnary)
    (hdensityDen : ComputableInPolyTime densityDenominator input encUnary) :
    IsPPTOn input encBool (fun a => testMajority (confidence a) (inverseTolerance a)
      (densityNumerator a) (densityDenominator a) (trial a)) := by
  unfold testMajority
  apply htrial.testProbabilityLT
  all_goals polytime

attribute [program_certificate] isPPTOn_testShift isPPTOn_testMajority

end Efficiency

end Cslib.Crypto.Pseudoentropy.Boosting
