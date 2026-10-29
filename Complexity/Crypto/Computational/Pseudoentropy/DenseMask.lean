/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.Basic
public import Complexity.Crypto.Computational.Pseudoentropy.Masking
import Complexity.Languages.Probabilistic.Notation
import Complexity.Crypto.Computational.Pseudoentropy.Selection
import Complexity.Crypto.Computational.Pseudoentropy.SequenceLearner
import Complexity.Tactic.PPT

/-!
# Dense masks against uniform sequence tests

A pseudoentropy pair's prediction bound forces every efficient sequence test to admit a dense
soft mask with small distinguishing gap. Otherwise the concrete sequence learner constructs one
uniform strict PPT predictor violating that bound. The mask's nonzero probabilities have an
explicit inverse-polynomial lower bound, needed for the subsequent extraction estimate.

The density and repetition schedules are efficiently computable. The indexed theorem gives one
eventual threshold for every member of a polynomial-size family of tests and density numerators.
The density need only be valid and below the entropy threshold where the conclusion is used.
Neither the program nor its parameters are chosen separately at each input length.

## Main results

* `HasGap.eventually_exists_indexed_mask`: one threshold for all tests in an efficient family.
* `HasGap.eventually_exists_mask`: specialize to a single uniform sequence test.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Games 3--5 and the following prediction reduction.
  [Holenstein2006].
* Thomas Holenstein, *Key Agreement from Weak Bit Agreement*, STOC 2005, Section 2.2.
  [Holenstein2005].
  We use the clocked soft-mask implementation, with all sampling failures included.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair

open ProbComp Probability Probability.PMF BitString Boosting Filter Turing.MultiTapeTM

@[local fun_prop]
private theorem computableTidilyInPolyTime_dyadicSize :
    ComputableTidilyInPolyTime dyadicSize encUnary encUnary :=
  ComputableInPolyTime.unary_dyadicSize.tidy

/-- All tests in a uniformly efficient polynomial-size family eventually admit dense soft masks
with small distinguishing gap whenever their density is valid. The common eventual threshold
allows arbitrary choices of index in the proof without supplying that choice to the program. -/
theorem HasGap.eventually_exists_indexed_mask {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (test : ℕ → ℕ → List (List Bool × Bool) → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encUnary)
      (encList (encPair encBits encBool))) encBool
        (fun input => test input.1.1 input.1.2 input.2))
    {candidates count densityBound inverseGap : ℕ → ℕ} {numerator : ℕ → ℕ → ℕ}
    (hcandidates : ComputableInPolyTime candidates encUnary encUnary)
    (hcount : ComputableInPolyTime count encUnary encUnary)
    (hnumerator : ComputableInPolyTime (fun input => numerator input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hinverseGap : ComputableInPolyTime inverseGap encUnary encUnary)
    (hgap : ∀ n, 0 < inverseGap n) :
    ∀ᶠ n in atTop, ∀ i < candidates n,
      0 < numerator n i → numerator n i ≤ dyadicSize (densityBound n) →
      (numerator n i : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n →
      ∃ mask : pair.Observation n × Bool → ProbComp Bool,
        (numerator n i : ℝ) / dyadicSize (densityBound n) ≤
          Pr[pair.latentSample n >>= mask] ∧
        (∀ value, 0 < Pr[mask value] →
          1 / (dyadicSize (2 * inverseGap n * dyadicSize (densityBound n)) : ℝ) ≤
            Pr[mask value]) ∧
        (Game.advantage
          (ProbComp.eval (OracleComp.replicate (count n) (pair.sample n) >>= test n i))
          (ProbComp.eval (OracleComp.replicate (count n) (maskedSample (pair.latentSample n)
            (fun value => pair.encode n value.1) Prod.snd mask) >>= test n i)) : ℝ) <
              (dyadicSize (count n) : ℝ) / inverseGap n := by
  have hcandidates := hcandidates.tidy
  have hcount := hcount.tidy
  have hnumerator := hnumerator.tidy
  have hdensity := hdensity.tidy
  have hinverseGap := hinverseGap.tidy
  classical
  let source : ℕ → ProbComp (List Bool × Bool) := fun n => (fun value : pair.Observation n × Bool =>
    (pair.encode n value.1, value.2)) <$> pair.latentSample n
  have hsource : IsPPTOn encUnary (encPair encBits encBool) source := by
    apply pair.efficient.congr
    intro n
    simp only [source, pair.eval_sample, ProbComp.eval_map, pair.eval_latentSample]
  obtain ⟨sizeCoeff, sizeDegree, hsize⟩ := hsource.length_le
  let width := fun n => sizeCoeff * (n + 1) ^ sizeDegree
  have hwidth : ComputableTidilyInPolyTime width encUnary encUnary := by
    unfold width
    polytime
  have hsize' (n : ℕ) (value : pair.Observation n × Bool)
      (hvalue : value ∈ (pair.joint n).support) : (pair.encode n value.1).length ≤ width n := by
    have h := hsize n (pair.encode n value.1, value.2)
      (by simpa only [source, ProbComp.eval_map, pair.eval_latentSample] using
        (PMF.mem_support_map_iff _ _ _).mpr ⟨value, hvalue, rfl⟩)
    simp only [length_encPair, encBits, Function.Embedding.refl_apply,
      encBool_apply, List.length_singleton,
      encUnary_apply, List.length_replicate] at h
    dsimp only [width]
    lia
  obtain ⟨c, d, evaluate, hevaluate, hrealize⟩ :=
    SequenceLearner.exists_evaluator (test := fun input : ℕ × ℕ => test input.1 input.2) htest
  let base := encPair encUnary encUnary
  let params := fun n i => SequenceLearner.parameters n (numerator n i) (densityBound n)
    (inverseGap n) (SavedPrediction.codeBound (base (n, i)).length (count n) c d (width n) + 1)
  have hparams : ComputableTidilyInPolyTime (fun input => params input.1 input.2)
      base Parameters.encoding := by
    dsimp only [params, base]
    apply ComputableInPolyTime.tidy
    apply SequenceLearner.isPolyTime_parameters
    · exact .of_tidy (by fun_prop)
    · exact .of_tidy (by fun_prop)
    · exact .of_tidy (by fun_prop)
    · exact .of_tidy (by fun_prop)
    · fun_prop
  have hrate : ComputableTidilyInPolyTime (fun n => (params n 0).rateBound)
      encUnary encUnary := by
    dsimp only [params, SequenceLearner.parameters]
    fun_prop
  let adversary := fun n i observation =>
    SequenceLearner.predict evaluate (source n) (base (n, i)) (count n) c d (width n)
      (inverseGap n) (params n i) observation
  have hadversary : IsPPTOn (encPair base encBits) encBool
      (fun input => adversary input.1.1 input.1.2 input.2) := by
    dsimp only [adversary]
    fun_prop
  have htolerance : ComputableTidilyInPolyTime
      (fun n => 4 * (params n 0).predictionInverseTolerance) encUnary encUnary := by
    unfold Parameters.predictionInverseTolerance Parameters.inverseRate Parameters.denominator
    dsimp only [params, SequenceLearner.parameters]
    fun_prop
  have hhard := hpair.eventually_indexed_error_ge adversary hadversary (.of_tidy hcandidates)
    (.of_tidy htolerance)
    (fun n => Nat.mul_pos (by decide) (params n 0).predictionInverseTolerance_pos)
  have hsmall := SequenceLearner.failureBound_eventually_le (params := fun n => params n 0)
    (inverseGap := inverseGap) (by change PolynomiallyBounded id; exact .id)
    hdensity.polynomiallyBounded hrate.polynomiallyBounded hinverseGap.polynomiallyBounded
    (fun _ => le_rfl)
  filter_upwards [hsmall, hhard] with n hsmall hhard
  intro i hi hnum hnumBound hthreshold
  specialize hhard i hi
  let := Fintype.ofFinite (pair.Observation n)
  have hvalid : (params n i).Valid := ⟨hnum, hnumBound⟩
  by_contra hnone
  have hdistinguish (state : State)
      (hdense : (params n i).delta ≤ density (pair.joint n) (params n i).rate
        (fun value => state.margin (fun code value =>
          signedPredict evaluate code (pair.encode n value.1)) Prod.snd value - state.threshold)) :
      (dyadicSize (count n) : ℝ) / inverseGap n ≤
        (Game.advantage (ProbComp.eval (OracleComp.replicate (count n) (source n) >>= test n i))
          (ProbComp.eval (OracleComp.replicate (count n) (maskedSample (pair.latentSample n)
            (fun value => pair.encode n value.1) Prod.snd (fun value =>
              SequenceLearner.mask (signedPredict evaluate) (params n i) state
                (pair.encode n value.1, value.2))) >>= test n i)) : ℝ) := by
    let mask := fun value : pair.Observation n × Bool =>
      SequenceLearner.mask (signedPredict evaluate) (params n i) state
        (pair.encode n value.1, value.2)
    have hmass (value) (hpositive : 0 < Pr[mask value]) :
        1 / (dyadicSize (2 * inverseGap n * dyadicSize (densityBound n)) : ℝ) ≤
          Pr[mask value] :=
      inv_dyadicSize_le_eval_sampleDyadicCoin (params n i).rateBound _ hpositive
    have hdense' : (numerator n i : ℝ) / dyadicSize (densityBound n) ≤
        Pr[pair.latentSample n >>= mask] := by
      change (params n i).delta ≤ _
      rw [ProbComp.eval_bind, pair.eval_latentSample, bind_apply_toReal]
      simpa only [mask, SequenceLearner.mask_probability, density, State.margin, State.votes]
        using hdense
    have hnot := fun h => hnone ⟨mask, hdense', hmass, h⟩
    apply le_of_not_gt
    intro hgap
    apply hnot
    have hsourceEq : ProbComp.eval (source n) = ProbComp.eval (pair.sample n) := by
      simp only [source, ProbComp.eval_map, pair.eval_latentSample, pair.eval_sample]
    simpa only [ProbComp.eval_bind,
      ProbComp.eval_replicate_congr hsourceEq (count n)] using hgap
  have hprediction := SequenceLearner.predict_error (pair.latentSample n)
    (fun value => pair.encode n value.1) Prod.snd evaluate (base (n, i))
    (count n) c d (width n) (inverseGap n) (params n i) (test n i) hvalid (hgap n)
    (SequenceLearner.parameters_gamma_le _ _ _ _ _ hvalid (hgap n))
    (by simpa only [pair.eval_latentSample] using hsize' n)
    le_rfl
    (fun state value hvalue => hrealize (n, i) (pair.latentSample n)
      (fun value => pair.encode n value.1) Prod.snd (count n) (width n) (params n i) state
        (pair.encode n value.1)
        (hsize' n value (by simpa only [pair.eval_latentSample] using hvalue)))
    (by simpa only [source, pair.eval_latentSample, Game.coe_advantage, Game.coe_succProbability]
      using hdistinguish)
  have hlaw : ProbComp.eval (predictionGame pair.sample (fun n => adversary n i) n) =
      ProbComp.eval (do
        let value ← pair.latentSample n
        (fun answer => answer == value.2) <$> adversary n i (pair.encode n value.1)) := by
    simp only [predictionGame, ProbComp.eval_bind, pair.eval_sample, PMF.bind_map,
      pair.eval_latentSample, ProbComp.eval_map, ProbComp.eval_pure]
    rfl
  rw [hlaw] at hhard
  change (PMF.conditionalEntropy (pair.joint n) + gap n) / 2 ≤ _ at hhard
  change (params n i).delta ≤ _ at hthreshold
  have htolerance : (0 : ℝ) < (params n i).predictionInverseTolerance := by
    exact_mod_cast (params n i).predictionInverseTolerance_pos
  change (ProbComp.eval (do
    let value ← pair.latentSample n
    (fun answer => answer == value.2) <$> adversary n i (pair.encode n value.1)) false).toReal ≤
      (params n i).delta / 2 - 1 / (params n i).predictionInverseTolerance +
        (SequenceLearner.failureBound (params n i) (inverseGap n) : ℝ) at hprediction
  change (SequenceLearner.failureBound (params n i) (inverseGap n) : ℝ) ≤
    1 / (2 * (params n i).predictionInverseTolerance) at hsmall
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hhard
  change _ ≤ _ + 1 / (4 * ((params n i).predictionInverseTolerance : ℝ)) at hhard
  have hpositive : (0 : ℝ) < 1 / (4 * (params n i).predictionInverseTolerance) := by positivity
  have hhalf : (1 : ℝ) / (2 * (params n i).predictionInverseTolerance) =
      2 * (1 / (4 * (params n i).predictionInverseTolerance)) := by ring
  have hwhole : (1 : ℝ) / (params n i).predictionInverseTolerance =
      4 * (1 / (4 * (params n i).predictionInverseTolerance)) := by ring
  linarith

/-- Every uniform sequence test eventually admits a dense soft mask with small distinguishing
gap. The mask may depend on the test and parameter; its positive probabilities are uniformly
bounded below by the configured dyadic rate. The statement exposes no boosting state. -/
theorem HasGap.eventually_exists_mask {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (test : ℕ → List (List Bool × Bool) → ProbComp Bool)
    (htest : IsPPTOn (encPair encUnary
      (encList (encPair encBits encBool))) encBool
        (fun input => test input.1 input.2))
    {count numerator densityBound inverseGap : ℕ → ℕ}
    (hcount : ComputableInPolyTime count encUnary encUnary)
    (hnumerator : ComputableInPolyTime numerator encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hinverseGap : ComputableInPolyTime inverseGap encUnary encUnary)
    (hgap : ∀ n, 0 < inverseGap n) :
    ∀ᶠ n in atTop, 0 < numerator n → numerator n ≤ dyadicSize (densityBound n) →
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n →
      ∃ mask : pair.Observation n × Bool → ProbComp Bool,
        (numerator n : ℝ) / dyadicSize (densityBound n) ≤
          Pr[pair.latentSample n >>= mask] ∧
        (∀ value, 0 < Pr[mask value] →
          1 / (dyadicSize (2 * inverseGap n * dyadicSize (densityBound n)) : ℝ) ≤
            Pr[mask value]) ∧
        (Game.advantage (ProbComp.eval (OracleComp.replicate (count n) (pair.sample n) >>= test n))
          (ProbComp.eval (OracleComp.replicate (count n) (maskedSample (pair.latentSample n)
            (fun value => pair.encode n value.1) Prod.snd mask) >>= test n)) : ℝ) <
              (dyadicSize (count n) : ℝ) / inverseGap n := by
  have h := hpair.eventually_exists_indexed_mask (fun n _ => test n) (by ppt)
    (candidates := fun _ => 1) (numerator := fun n _ => numerator n)
    (by polytime) hcount (by polytime) hdensity hinverseGap hgap
  filter_upwards [h] with n hn
  exact hn 0 (by decide)

end Cslib.Crypto.Pseudoentropy.SamplablePair
