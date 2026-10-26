/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.Basic
public import Complexity.Languages.Probabilistic.Selection
import Complexity.Computability.Probabilistic.Selection
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
# Uniform bounds for indexed predictors

An efficient sampler supplies fresh labeled examples for empirical predictor selection. A single
uniform predictor then performs almost as well as every candidate in a polynomial-size family.
Consequently a pseudoentropy gap bounds all candidates simultaneously, with any prescribed
inverse-polynomial slack. The bound allows the best candidate to vary arbitrarily with the
security parameter; that choice is never supplied to the algorithm.

## Main definitions

* `selectPredictor`: validate candidates on fresh examples before predicting the challenge.

## Main results

* `selectPredictor_error_le`: compare with every candidate, charging validation error.
* `isPPTOn_selectPredictor`: empirical selection is strict PPT.
* `SamplablePair.HasGap.eventually_indexed_error_ge`: one threshold for all candidate indices.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1.
  [Holenstein2006].
  This empirical selection step prepares the uniform treatment of the entropy guesses in that
  proof. Its quantitative bound uses the shared concentration and candidate-selection rules.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Filter Turing.MultiTapeTM

open scoped NNReal

/-- Compare predictors on fresh labeled samples, then use the chosen predictor on the challenge.
The challenge's hidden label is never an input to this program. -/
def selectPredictor (count trials : ℕ) (source : ProbComp (List Bool × Bool))
    (predict : ℕ → List Bool → ProbComp Bool) (observation : List Bool) : ProbComp Bool := do
  let chosen ← OracleComp.selectBest count trials (fun i => do
    let sample ← source
    (fun answer => answer == sample.2) <$> predict i sample.1)
  predict chosen observation

/-- Empirical prediction is strict PPT when the sampler, indexed predictors, and counts are
efficient. All callbacks may capture the original input. -/
theorem isPPTOn_selectPredictor {α : Type} {input : α ↪ List Bool}
    {count trials : α → ℕ} {source : α → ProbComp (List Bool × Bool)}
    {predict : α → ℕ → List Bool → ProbComp Bool} {observation : α → List Bool}
    (hcount : ComputableInPolyTime count input encUnary)
    (htrials : ComputableInPolyTime trials input encUnary)
    (hsource : IsPPTOn input (encPair encBits encBool) source)
    (hpredict : IsPPTOn (encPair (encPair input encUnary) encBits)
      encBool (fun x => predict x.1.1 x.1.2 x.2))
    (hobservation : ComputableInPolyTime observation input encBits) :
    IsPPTOn input encBool (fun a =>
      selectPredictor (count a) (trials a) (source a) (predict a) (observation a)) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hcount
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at htrials
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hobservation
  have htrial := hpredict.preprocess
    (input := encPair (encPair input encUnary) (encPair encBits encBool))
    (prepare := fun x : (α × ℕ) × (List Bool × Bool) => (x.1, x.2.1)) (by fun_prop)
  have hfinal := hpredict.preprocess (input := encPair input encUnary)
    (prepare := fun x : α × ℕ => (x, observation x.1)) (by fun_prop)
  unfold selectPredictor
  apply IsPPTOn.bind_with (left := encUnary) ?_ hfinal
  apply IsPPTOn.selectBest ?_ (.of_tidy hcount) (.of_tidy htrials)
  exact (hsource.preprocess (by fun_prop)).bind_with (htrial.map_with (by fun_prop))

attribute [program_certificate] isPPTOn_selectPredictor

/-- Selection is independent of the challenge, so its final correctness game is a fresh trial
of the selected candidate. -/
theorem eval_predictionGame_selectPredictor (sample : ℕ → ProbComp (List Bool × Bool))
    (predict : ℕ → ℕ → List Bool → ProbComp Bool) (count trials : ℕ → ℕ) (n : ℕ) :
    ProbComp.eval (predictionGame sample (fun n =>
      selectPredictor (count n) (trials n) (sample n) (predict n)) n) =
      ProbComp.eval (OracleComp.selectBest (count n) (trials n)
        (fun i => predictionGame sample (fun n => predict n i) n) >>=
          fun i => predictionGame sample (fun n => predict n i) n) := by
  simp only [predictionGame, selectPredictor, bind_pure_comp, ProbComp.eval_bind,
    ProbComp.eval_map, PMF.map_bind]
  rw [PMF.bind_comm (ProbComp.eval (sample n))]

/-- The selected predictor's error is bounded by every candidate's error plus estimation and
selection losses, with the challenge sampled independently of all validation samples. -/
theorem selectPredictor_error_le (sample : ℕ → ProbComp (List Bool × Bool))
    (predict : ℕ → ℕ → List Bool → ProbComp Bool) (count confidence inverseTolerance : ℕ → ℕ)
    (n i : ℕ) (hi : i < count n) (htolerance : 0 < inverseTolerance n) :
    (ProbComp.eval (predictionGame sample (fun n => selectPredictor (count n)
      ((confidence n + 1) * inverseTolerance n ^ 2) (sample n) (predict n)) n) false).toReal ≤
        (ProbComp.eval (predictionGame sample (fun n => predict n i) n) false).toReal +
          2 / inverseTolerance n + count n * (1 / 2 : ℝ) ^ confidence n := by
  rw [eval_predictionGame_selectPredictor]
  exact ProbComp.selectBest_test_error_le (count n) (confidence n) (inverseTolerance n)
    htolerance (fun i => predictionGame sample (fun n => predict n i) n) i hi

namespace SamplablePair

/-- A pseudoentropy gap bounds every member of a uniformly efficient polynomial-size family
at once, allowing any efficient inverse-polynomial slack. No computable choice of index is
assumed, and the eventual threshold is common to all indices at each parameter. -/
theorem HasGap.eventually_indexed_error_ge {pair : SamplablePair} {gap : ℕ → ℝ}
    (hgap : pair.HasGap gap) (predict : ℕ → ℕ → List Bool → ProbComp Bool)
    (hpredict : IsPPTOn
      (encPair (encPair encUnary encUnary) encBits) encBool
      (fun x => predict x.1.1 x.1.2 x.2))
    {count inverseTolerance : ℕ → ℕ}
    (hcount : ComputableInPolyTime count encUnary encUnary)
    (htolerance : ComputableInPolyTime inverseTolerance encUnary encUnary)
    (hpos : ∀ n, 0 < inverseTolerance n) :
    ∀ᶠ n in atTop, ∀ i < count n,
      (PMF.conditionalEntropy (pair.joint n) + gap n) / 2 ≤
        (ProbComp.eval (predictionGame pair.sample (fun n => predict n i) n) false).toReal +
          1 / inverseTolerance n := by
  have hcount := hcount.tidy
  have htolerance := htolerance.tidy
  have hsource := pair.efficient
  have hefficient : IsPPT encBool (fun n => selectPredictor (count n)
      ((n + 1) * (4 * inverseTolerance n) ^ 2) (pair.sample n) (predict n)) := by
    unfold IsPPT
    apply isPPTOn_selectPredictor
    · fun_prop
    · fun_prop
    · ppt
    · apply hpredict.preprocess
        (prepare := fun x : ((ℕ × List Bool) × ℕ) × List Bool => ((x.1.1.1, x.1.2), x.2))
      fun_prop
    · fun_prop
  have hselected := hgap.eventually_error_ge _ hefficient
  have hdecay := (negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num))
    |>.polynomiallyBounded_mul hcount.polynomiallyBounded
  have hsmall := hdecay.eventually_le_inv_polynomial
    (show PolynomiallyBounded (fun n => 2 * inverseTolerance n) from
      (PolynomiallyBounded.const 2).mul htolerance.polynomiallyBounded)
    (fun n => Nat.mul_pos (by decide) (hpos n))
  filter_upwards [hselected, hsmall] with n hn hsmall
  intro i hi
  have herror := selectPredictor_error_le pair.sample predict count id
    (fun n => 4 * inverseTolerance n) n i hi (by have := hpos n; positivity)
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat, Nat.cast_mul, Nat.cast_ofNat] at hsmall herror
  have hprecision : 2 / (4 * (inverseTolerance n : ℝ)) +
      1 / (2 * inverseTolerance n) = 1 / inverseTolerance n := by ring
  dsimp only [id_eq] at herror
  linarith

end SamplablePair

end Cslib.Crypto.Pseudoentropy
