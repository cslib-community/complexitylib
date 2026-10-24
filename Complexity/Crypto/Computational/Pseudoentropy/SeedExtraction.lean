/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.RepeatedExtraction
public import Complexity.Crypto.Computational.Pseudoentropy.Seed

/-!
# Statistical extraction from a sampler's seed

The first component hashes public observations; the third hashes the original sampler seeds
while revealing every observation and label. Its conditional entropy is exactly the seed length
minus the two visible entropy terms. Both use the same repetition schedule as label extraction.
The program retains unused coins and never samples a conditional distribution. Zero output bits
remain valid even when a component has no entropy left.

## Main results

* `observation_extraction`, `observation_word_extraction`: extract public-observation entropy.
* `remainingSeed_extraction`, `remainingSeed_word_extraction`: extract the remaining sampler
  entropy while retaining every observation, hidden label, and public hash seed.

All statements admit every randomized test of the joint output, without a computational
restriction on the test or an efficient entropy estimate.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, the first and third extractors and Games 0--1.
  [Holenstein2006].
  We use the shared seed-information concentration schedule.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization

open Probability Probability.PMF BitString Filter

/-- Repeated public observations supply their Shannon entropy to the first extractor. -/
theorem observation_extraction {pair : SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Finite (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List (pair.Observation n) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) →
        pair.Observation n) => hash n key (List.ofFn values)))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst)) :
    Game.Indistinguishable
      (fun (test : ∀ n, Key n × BitString (outputBits n) → Game) n =>
        (seededHash (ProbComp.eval (key n))
          (ProbComp.eval (OracleComp.replicate
            (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
              (Prod.fst <$> pair.latentSample n))) (hash n)).bind (test n))
      (fun test n => do
        let result ← do
          let k ← ProbComp.eval (key n)
          (PMF.uniformOfFintype (BitString (outputBits n))).map (k, ·)
        test n result)
      (fun _ => True) := by
  apply seededHash_replicate_indistinguishable
    (fun n => Prod.fst <$> pair.latentSample n) saved.length inverseSlack outputBits
    ?_ key hash hhash (by simpa only [ProbComp.eval_map, pair.eval_latentSample] using hbudget)
  intro n value hvalue
  simp only [ProbComp.eval_map, pair.eval_latentSample, ← saved.output_distribution,
    PMF.map_comp, Function.comp_def] at hvalue ⊢
  simpa [BitString, Real.logb_pow] using
    uniform_map_mass_ge (fun bits => (saved.output n bits).1) value hvalue

/-- The first statistical transition on ordinary sampled observation words. Its hash's finite
two-universality premise includes the public encoding; no observation is sampled conditionally. -/
theorem observation_word_extraction {pair : SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Finite (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List (List Bool) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) →
        pair.Observation n) => hash n key ((List.ofFn values).map (pair.encode n))))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst)) :
    Game.Indistinguishable
      (fun (test : ∀ n, Key n × BitString (outputBits n) → Game) n =>
        (seededHash (ProbComp.eval (key n))
          (ProbComp.eval (OracleComp.replicate
            (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
              (Prod.fst <$> pair.sample n))) (hash n)).bind (test n))
      (fun test n => do
        let result ← do
          let k ← ProbComp.eval (key n)
          (PMF.uniformOfFintype (BitString (outputBits n))).map (k, ·)
        test n result)
      (fun _ => True) := by
  intro test _
  have h := saved.observation_extraction inverseSlack outputBits key
    (fun n k values => hash n k (values.map (pair.encode n))) hhash hbudget test trivial
  apply h.congr
  intro n
  have hpublic : ProbComp.eval (Prod.fst <$> pair.sample n) =
      (ProbComp.eval (Prod.fst <$> pair.latentSample n)).map (pair.encode n) := by
    simp only [ProbComp.eval_map, pair.eval_latentSample, pair.eval_sample,
      PMF.map_comp, Function.comp_def]
  dsimp only
  rw [ProbComp.eval_replicate_map hpublic
    (ExtractionSchedule.count n (saved.length n) (inverseSlack n))]
  simp only [seededHash_eq_bind, PMF.bind_map, Function.comp_def]

/-- Extract the unused seed entropy, preserving the complete pair output and hash seed.
The entropy chain rule pays for both the public observations and the labels already revealed. -/
theorem remainingSeed_extraction {pair : SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Finite (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List (BitString (saved.length n)) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) →
        BitString (saved.length n)) => hash n key (List.ofFn values)))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    Game.Indistinguishable
      (fun (test : ∀ n,
          List (pair.Observation n × Bool) × Key n × BitString (outputBits n) → Game) n =>
        (ProbComp.eval (OracleComp.replicate
          (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
            (saved.latentSampleWithSeed n) >>= extractLabels (key n) (hash n))).bind (test n))
      (fun test n => (extractLabelsIdeal (Output := BitString (outputBits n))
        (pair.latentSample n) (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
          (key n)).bind (test n)) (fun _ => True) := by
  intro test _
  have h := extractLabels_indistinguishable
    (fun n => saved.latentSampleWithSeed n) saved.length inverseSlack outputBits
    (by simpa only [saved.eval_latentSampleWithSeed] using saved.jointWithSeed_mass_ge)
    key hash hhash
    (by
      filter_upwards [hbudget] with n hn
      simpa only [saved.eval_latentSampleWithSeed, show conditionalEntropy (saved.jointWithSeed n) =
        saved.length n - entropy ((pair.joint n).map Prod.fst) -
          conditionalEntropy (pair.joint n) by linarith [saved.entropy_chain_rule n]] using hn)
    test trivial
  apply h.congr
  intro n
  have hpublic : ProbComp.eval (Prod.fst <$> saved.latentSampleWithSeed n) =
      ProbComp.eval (pair.latentSample n) := by
    simp only [ProbComp.eval_map, pair.eval_latentSample, saved.eval_latentSampleWithSeed,
      saved.jointWithSeed_map_fst]
  simp only [extractLabelsIdeal, ProbComp.eval_replicate_congr hpublic
    (ExtractionSchedule.count n (saved.length n) (inverseSlack n))]

/-- The remaining-seed transition for the actual word sampler. Every observation and label
stays public; finite representations are confined to the two-universality hypothesis. -/
theorem remainingSeed_word_extraction {pair : SamplablePair} (saved : pair.SeedRealization)
    (inverseSlack outputBits : ℕ → ℕ) {Key : ℕ → Type} [∀ n, Finite (Key n)]
    (key : ∀ n, ProbComp (Key n))
    (hash : ∀ n, Key n → List (List Bool) → BitString (outputBits n))
    (hhash : ∀ n, IsTwoUniversal (ProbComp.eval (key n))
      (fun key (values : Fin (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) →
        BitString (saved.length n)) => hash n key ((List.ofFn values).map List.ofFn)))
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    Game.Indistinguishable
      (fun (test : ∀ n, List (List Bool × Bool) × Key n × BitString (outputBits n) → Game) n =>
        (ProbComp.eval (OracleComp.replicate
          (ExtractionSchedule.count n (saved.length n) (inverseSlack n))
            (saved.sampleWithSeed n) >>= extractLabels (key n) (hash n))).bind (test n))
      (fun test n => (extractLabelsIdeal (Output := BitString (outputBits n)) (pair.sample n)
        (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) (key n)).bind (test n))
      (fun _ => True) := by
  intro test _
  have h := saved.remainingSeed_extraction inverseSlack outputBits key
    (fun n k values => hash n k (values.map List.ofFn)) hhash hbudget
      (fun n result => test n
        (result.1.map (fun value => (pair.encode n value.1, value.2)), result.2)) trivial
  apply h.congr
  intro n
  let observe := fun value : pair.Observation n × Bool => (pair.encode n value.1, value.2)
  have hsource : ProbComp.eval (saved.sampleWithSeed n) =
      (ProbComp.eval (saved.latentSampleWithSeed n)).map
        (fun result => (observe result.1, List.ofFn result.2)) := by
    simpa only [saved.eval_latentSampleWithSeed] using
      saved.eval_sampleWithSeed n
  have hpublic : ProbComp.eval (pair.sample n) =
      (ProbComp.eval (pair.latentSample n)).map observe := by
    simp only [pair.eval_latentSample, pair.eval_sample, observe]
  have hreal := eval_replicate_extractLabels_map_pair observe List.ofFn
    (saved.latentSampleWithSeed n)
    (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) (key n) (hash n) hsource
  have hideal := extractLabelsIdeal_map_observation (Output := BitString (outputBits n))
    observe (pair.latentSample n)
    (ExtractionSchedule.count n (saved.length n) (inverseSlack n)) (key n) hpublic
  have hleft := congrArg (fun law => law.bind (test n)) hreal.symm
  have hright := congrArg (fun law => law.bind (test n)) hideal
  simpa only [ProbComp.eval_bind, PMF.bind_map, Function.comp_def, observe] using
    congrArg₂ Game.advantage hleft hright

end Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization
