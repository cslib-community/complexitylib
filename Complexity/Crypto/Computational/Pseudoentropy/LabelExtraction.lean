/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.RepeatedExtraction
public import Complexity.Crypto.Computational.Pseudoentropy.Seed
public import Complexity.Probability.UniformNat
import Complexity.Crypto.Computational.Pseudoentropy.DenseMask
import Complexity.Crypto.Computational.Pseudoentropy.MaskedExtraction
import Complexity.Crypto.Game.Statistical
import Complexity.Tactic.PolyTime

/-!
# Computational extraction of a pseudoentropy pair's labels

The dense-mask theorem supplies a comparison experiment for each efficient sequence test.
Extraction makes that experiment statistically uniform. Its information budget is the sampler's
seed length plus `n + 2`, independently of the test's polynomial running-time degree.

The theorem retains all observations and the hash seed. `HasGap.extract_indexed_labels` instantiates
a polynomial repetition schedule and proves its error negligible, leaving only the entropy budget
and admissible density conditions. A valid index may be chosen arbitrarily at each parameter;
the efficient reduction handles all indices. The generator must still combine the candidates.

## Main results

* `HasGap.indexed_extracted_advantage_negligible`: dense masks give negligible extraction
  advantage for any valid choices from a uniformly efficient indexed family.
* `HasGap.extract_indexed_labels`: the fixed polynomial schedule pays the full statistical loss.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, the transition from Game 2 through Game 5.
  [Holenstein2006].
  We use fresh soft masks and the checked strict PPT sequence learner.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair

open Probability Probability.PMF BitString Filter Turing.MultiTapeTM

open scoped NNReal

/-- Label extraction is computationally uniform along any valid choices from an efficient
polynomial-size family. The choices need not be computable: the reduction handles all indices
uniformly, and only the proof uses the chosen index. Observations and hash seeds stay public. -/
theorem HasGap.indexed_extracted_advantage_negligible {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization) (choose : ℕ → ℕ)
    {Seed Output : ℕ → ℕ → Type} [∀ n i, Finite (Seed n i)] [∀ n i, Fintype (Output n i)]
    [∀ n i, Nonempty (Output n i)] (seed : ∀ n i, ProbComp (Seed n i))
    (hash : ∀ n i, Seed n i → List Bool → Output n i)
    (test : ∀ n i, List (List Bool) × Seed n i × Output n i → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encUnary)
      (encList (encPair encBits encBool))) encBool
        (fun input => extractLabels (seed input.1.1 input.1.2) (hash input.1.1 input.1.2)
          input.2 >>= test input.1.1 input.1.2))
    {candidates count densityBound : ℕ → ℕ} {numerator : ℕ → ℕ → ℕ} {slack : ℕ → ℝ}
    (hcandidates : ComputableTidilyInPolyTime candidates encUnary encUnary)
    (hcount : ComputableTidilyInPolyTime count encUnary encUnary)
    (hnumerator : ComputableTidilyInPolyTime (fun input => numerator input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hdensity : ComputableTidilyInPolyTime densityBound encUnary encUnary)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hhash : ∀ n i, IsTwoUniversal (ProbComp.eval (seed n i))
      (fun s (bits : BitString (count n)) => hash n i s (List.ofFn bits)))
    (hslack : ∀ n, 0 ≤ slack n)
    (herror : Negligible (fun n => Real.toNNReal
      (2 * Real.exp (-2 * slack n ^ 2 / (count n * (realization.length n + n + 2 : ℕ) ^ 2)) +
        Real.sqrt (Fintype.card (Output n (choose n)) * (2 * (2 : ℝ) ^
          (-(count n * ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)) -
            slack n)))) / 2))) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (do
        let samples ← OracleComp.replicate (count n) (pair.sample n)
        let result ← extractLabels (seed n (choose n)) (hash n (choose n)) samples
        test n (choose n) result))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        pair.latentSample n) (count n) (seed n (choose n))).bind
          (fun output => ProbComp.eval (test n (choose n) output)))) := by
  classical
  let error := fun n =>
    2 * Real.exp (-2 * slack n ^ 2 / (count n * (realization.length n + n + 2 : ℕ) ^ 2)) +
      Real.sqrt (Fintype.card (Output n (choose n)) * (2 * (2 : ℝ) ^
        (-(count n * ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)) - slack n)))) / 2
  let reduced := fun n i samples => do
    let result ← extractLabels (seed n i) (hash n i) samples
    test n i result
  apply negligible_iff_coe.mpr
  apply (Asymptotics.superpolynomialDecay_iff_abs_isBoundedUnder _
    tendsto_natCast_atTop_atTop).mpr
  intro degree
  have herror' : Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) error := by
    apply (negligible_iff_coe.mp herror).congr
    intro n
    apply Real.coe_toNNReal
    positivity
  let inverseGap := fun n => dyadicSize (count n) * (n + 1) ^ degree
  have hinverseGap : ComputableTidilyInPolyTime inverseGap encUnary encUnary := by
    unfold inverseGap
    polytime
  have hgap (n : ℕ) : 0 < inverseGap n := by
    exact Nat.mul_pos (dyadicSize_pos _) (Nat.pow_pos (by lia))
  have hmasks := hpair.eventually_exists_indexed_mask reduced htest hcandidates hcount
    hnumerator hdensity hinverseGap hgap
  have hbound : PolynomiallyBounded
      (fun n => 2 * inverseGap n * dyadicSize (densityBound n)) := by
    have := hinverseGap.polynomiallyBounded
    have := hdensity.polynomiallyBounded
    fun_prop
  have hmass := maskedSample_dyadic_mass_ge_eventually
    (fun n => pair.latentSample n) (fun _ => id) (fun _ => Prod.snd)
    realization.length (fun n => 2 * inverseGap n * dyadicSize (densityBound n)) hbound
    (by simpa only [pair.eval_latentSample] using realization.mass_ge)
  refine ⟨2, Filter.eventually_map.mpr ?_⟩
  filter_upwards [hmasks, hmass, hchoose, hvalid,
    (herror' degree).eventually_le_const (by norm_num : (0 : ℝ) < 1)] with
    n hmask hmass hindex hn hsmall
  obtain ⟨mask, hdense, hpositive, hdistinguish⟩ := hmask (choose n) hindex hn.1 hn.2.1 hn.2.2
  have hclose := maskedSample_extract_dist_bind_le (pair.latentSample n)
    (fun value => pair.encode n value.1) Prod.snd mask (count n) (realization.length n + n + 2)
    (hmass mask (fun value _ => hpositive value)) (seed n (choose n)) (hash n (choose n))
    (hhash n (choose n)) hdense (hslack n)
    (fun output => ProbComp.eval (test n (choose n) output))
  rw [← coe_nndist, ← Game.advantage_eq_nndist] at hclose
  have hcompare := extractLabels_sequence_gap (pair.sample n)
    (maskedSample (pair.latentSample n)
      (fun value => pair.encode n value.1) Prod.snd mask)
    (count n) (seed n (choose n)) (hash n (choose n)) (test n (choose n)) _ hclose
  have htotal : (Game.advantage
      (ProbComp.eval (OracleComp.replicate (count n) (pair.sample n) >>= reduced n (choose n)))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        pair.latentSample n) (count n) (seed n (choose n))).bind
          (fun output => ProbComp.eval (test n (choose n) output))) : ℝ) ≤
        (dyadicSize (count n) : ℝ) / inverseGap n + error n := by
    change _ - error n ≤ _ at hcompare
    exact le_of_lt ((sub_lt_iff_lt_add.mp (hcompare.trans_lt hdistinguish)))
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) (Game.advantage _ _).coe_nonneg)]
  have hprecision : (n : ℝ) ^ degree * ((dyadicSize (count n) : ℝ) / inverseGap n) ≤ 1 := by
    have hdyadic : (dyadicSize (count n) : ℝ) ≠ 0 := by exact_mod_cast (dyadicSize_pos _).ne'
    simp only [inverseGap, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      div_mul_eq_div_div, div_self hdyadic, mul_one_div]
    apply (div_le_one (by positivity)).mpr
    gcongr
    linarith
  have h := mul_le_mul_of_nonneg_left htotal (pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) degree)
  dsimp only [error, reduced] at h
  nlinarith

/-- The explicit repetition schedule makes any valid indexed label extractor computationally
uniform. Only the proof uses the chosen indices; the sampler, hash, and test form one uniformly
efficient family. The entropy budget discharges the complete statistical error. -/
theorem HasGap.extract_indexed_labels {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization) (choose : ℕ → ℕ)
    {Seed : ℕ → ℕ → Type} [∀ n i, Finite (Seed n i)]
    {outputBits : ℕ → ℕ → ℕ} {candidates inverseSlack : ℕ → ℕ}
    (seed : ∀ n i, ProbComp (Seed n i))
    (hash : ∀ n i, Seed n i → List Bool → BitString (outputBits n i))
    (test : ∀ n i, List (List Bool) × Seed n i × BitString (outputBits n i) → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encUnary)
      (encList (encPair encBits encBool))) encBool
        (fun input => extractLabels (seed input.1.1 input.1.2) (hash input.1.1 input.1.2)
          input.2 >>= test input.1.1 input.1.2))
    (hcandidates : ComputableTidilyInPolyTime candidates encUnary encUnary)
    (hslack : ComputableTidilyInPolyTime inverseSlack encUnary encUnary)
    {numerator : ℕ → ℕ → ℕ} {densityBound : ℕ → ℕ}
    (hnumerator : ComputableTidilyInPolyTime (fun input => numerator input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hdensity : ComputableTidilyInPolyTime densityBound encUnary encUnary)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hhash : ∀ n i, IsTwoUniversal (ProbComp.eval (seed n i))
      (fun s (bits : BitString
        (ExtractionSchedule.count n (realization.length n) (inverseSlack n))) =>
          hash n i s (List.ofFn bits)))
    (hbudget : ∀ᶠ n in atTop,
      outputBits n (choose n) +
        2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n))) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (do
        let samples ← OracleComp.replicate
          (ExtractionSchedule.count n (realization.length n) (inverseSlack n)) (pair.sample n)
        let result ← extractLabels (seed n (choose n)) (hash n (choose n)) samples
        test n (choose n) result))
      ((extractLabelsIdeal ((fun value => pair.encode n value.1) <$>
        pair.latentSample n)
          (ExtractionSchedule.count n (realization.length n) (inverseSlack n))
          (seed n (choose n))).bind
            (fun output => ProbComp.eval (test n (choose n) output)))) := by
  apply hpair.indexed_extracted_advantage_negligible realization choose seed hash test htest
    hcandidates
    (ExtractionSchedule.isPolyTime_count (by fun_prop)
      realization.length_isPolyTime.tidy hslack) hnumerator hdensity hchoose hvalid hhash
    (slack := fun n => ExtractionSchedule.slack n (realization.length n) (inverseSlack n))
    (fun _ => Nat.cast_nonneg _)
  apply negligible_of_eventually_le ExtractionSchedule.error_negligible
  filter_upwards [hbudget] with n hn
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (by positivity)]
  simpa only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] using ExtractionSchedule.error_le n (realization.length n) (inverseSlack n)
      (outputBits n (choose n)) ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)) hn

end Cslib.Crypto.Pseudoentropy.SamplablePair
