/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.MatrixExtraction
public import Complexity.Crypto.Computational.Pseudoentropy.Seed
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Padding
import Complexity.Crypto.Computational.Pseudoentropy.SeedExtraction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Probabilistic.LinearHash
import Complexity.Tactic.PPT

/-!
# Executable extraction of observations and retained seeds

The first and third components use the same matrix extractor as label extraction. Concatenating
fixed-width sampler seeds supplies an injective input representation. Public observations first
receive self-delimiting padding, since their lengths can vary. Each program retains its complete
independent matrix seed. Statistical transitions quantify over every randomized Boolean test
of the complete output, with no efficiency restriction on the test.

## Main definitions

* `extractWordObservations`: pad and hash observations, returning the matrix seed and digest.
* `extractWordSeeds`: hash retained sampler seeds while preserving all observations and labels.

## Main results

* `isPPTOn_extractWordObservations`, `isPPTOn_extractWordSeeds`: strict PPT certificates.
* `SeedRealization.extract_word_observations`, `SeedRealization.extract_word_seeds`: the
  statistical transitions for the actual word programs, including their full public seeds.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, the first and third extractors and Games 0--1.
  [Holenstein2006].

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF BitString Filter Turing.MultiTapeTM

/-- Pad observations injectively, concatenate their blocks, and return a fresh hash seed and
digest as one word. The seed is part of the output, as in the strong extractor. -/
noncomputable def extractWordObservations (bound outputBits : ℕ)
    (observations : List (List Bool)) : ProbComp (List Bool) :=
  LinearHash.extract outputBits ((observations.map (padWord bound)).flatten)

/-- Bounded observations give a fixed output length, including the complete public seed. -/
theorem length_extractWordObservations (bound outputBits : ℕ) (observations : List (List Bool))
    (hbound : ∀ observation ∈ observations, observation.length ≤ bound) {output : List Bool}
    (houtput : output ∈ (ProbComp.eval
      (extractWordObservations bound outputBits observations)).support) :
    output.length = outputBits * (observations.length * (2 * bound + 1)) + outputBits := by
  simpa only [length_flatten_padWord bound observations hbound] using
    LinearHash.length_extract outputBits
    ((observations.map (padWord bound)).flatten) houtput

/-- Observation padding and concatenation compose with the matrix extractor. -/
theorem isPPTOn_extractWordObservations {α : Type} {input : α ↪ List Bool}
    {bound outputBits : α → ℕ} {observations : α → List (List Bool)}
    (hbound : ComputableTidilyInPolyTime bound input encUnary)
    (houtput : ComputableTidilyInPolyTime outputBits input encUnary)
    (hobservations : ComputableTidilyInPolyTime observations input (encList encBits)) :
    IsPPTOn input encBits
      (fun a => extractWordObservations (bound a) (outputBits a) (observations a)) := by
  unfold extractWordObservations
  ppt

attribute [program_certificate] isPPTOn_extractWordObservations

/-- The first statistical transition with an executable hash and self-delimiting padding.
Only supported observations need to fit the bound; `exists_observationBound` supplies an efficient
bound for every PPT sampler. The uniform comparison includes the entire matrix seed. -/
theorem SamplablePair.SeedRealization.extract_word_observations {pair : SamplablePair}
    (saved : pair.SeedRealization) (bound inverseSlack outputBits : ℕ → ℕ)
    (hbound : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Game.Indistinguishable
      (fun (test : ℕ → List Bool → Game) n =>
        (ProbComp.eval (OracleComp.replicate (count n) (Prod.fst <$> pair.sample n) >>=
          extractWordObservations (bound n) (outputBits n))).bind (test n))
      (fun test n => (uniformList
        (outputBits n * (count n * (2 * bound n + 1)) + outputBits n)).bind (test n))
      (fun _ => True) := by
  dsimp only
  intro test _
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  let observe (n : ℕ) (value : pair.Observation n) : BitString (2 * bound n + 1) :=
    ofList (2 * bound n + 1) (padWord (bound n) (pair.encode n value))
  let source (n : ℕ) := (fun value => observe n value.1) <$> pair.latentSample n
  have hentropy (n : ℕ) : entropy (ProbComp.eval (source n)) =
      entropy ((pair.joint n).map Prod.fst) := by
    rw [show ProbComp.eval (source n) = ((pair.joint n).map Prod.fst).map (observe n) by
      simp only [source, ProbComp.eval_map, pair.eval_latentSample, PMF.map_comp,
        Function.comp_def]]
    apply entropy_map_of_injOn
    intro x hx y hy hxy
    exact (pair.encode n).injective
      (word_eq_of_paddedBits_eq (hbound n x hx) (hbound n y hy) hxy)
  have h := seededHash_replicate_indistinguishable source saved.length inverseSlack outputBits
    (by
      intro n value hvalue
      simp only [source, ProbComp.eval_map, pair.eval_latentSample,
        ← saved.output_distribution, PMF.map_comp, Function.comp_def] at hvalue ⊢
      simpa [BitString, Real.logb_pow] using
        uniform_map_mass_ge (fun bits => observe n (saved.output n bits).1) value hvalue)
    (fun n => ProbComp.uniform (BitString (outputBits n * (count n * (2 * bound n + 1)))))
    (fun n key values =>
      LinearHash.hash (blocksEquiv (m := outputBits n) (k := count n * (2 * bound n + 1)) key)
        (ofList (count n * (2 * bound n + 1)) (values.map List.ofFn).flatten))
    (fun n => by
      simpa only [ProbComp.eval_uniform, List.map_ofFn, Function.comp_def, ← ofFn_blocksEquiv_symm,
        ofList_ofFn] using
        (LinearHash.isTwoUniversal_flat (count n * (2 * bound n + 1)) (outputBits n)).precompose
          (blocksEquiv (m := count n) (k := 2 * bound n + 1)).symm.injective)
    (by simpa only [hentropy] using hbudget)
    (fun n result => test n (List.ofFn result.1 ++ List.ofFn result.2)) trivial
  apply h.congr
  intro n
  have hpublic : ProbComp.eval (padWord (bound n) <$> (Prod.fst <$> pair.sample n)) =
      ProbComp.eval (List.ofFn <$> source n) := by
    simp only [ProbComp.eval_map, pair.eval_sample, source, pair.eval_latentSample,
      PMF.map_comp, Function.comp_def]
    apply map_congr_on_support
    intro result hresult
    exact (ofFn_ofList (length_padWord (hbound n result.1
      ((PMF.mem_support_map_iff _ _ _).mpr ⟨result, hresult, rfl⟩)))).symm
  have hreal := LinearHash.eval_extract_replicate (source n) (count n) (outputBits n)
  rw [ProbComp.eval_bind, ← ProbComp.eval_replicate_congr hpublic] at hreal
  simp only [OracleComp.replicate_map, ProbComp.eval_map, PMF.bind_map, Function.comp_def] at hreal
  have hrealTest := congrArg (fun law => law.bind (test n)) hreal
  simp only [PMF.bind_map, Function.comp_def] at hrealTest
  dsimp only
  simp only [ProbComp.eval_uniform]
  rw [← hrealTest, uniformList_add]
  simp only [count, extractWordObservations, OracleComp.replicate_map, ProbComp.eval_bind,
    ProbComp.eval_map, uniformList, PMF.bind_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  simp only [monad_bind_eq_bind, PMF.bind_map, Function.comp_def]

/-- Hash complete sampler seeds while retaining every sampled observation and label. -/
noncomputable def extractWordSeeds (count seedBits outputBits : ℕ)
    (samples : List ((List Bool × Bool) × List Bool)) :
    ProbComp (List (List Bool × Bool) × List Bool × List Bool) :=
  extractMatrixLabels (count * seedBits) outputBits List.flatten samples

/-- Seed-block concatenation composes with the shared matrix extractor's PPT certificate. -/
theorem isPPTOn_extractWordSeeds {α : Type} {input : α ↪ List Bool}
    {count seedBits outputBits : α → ℕ} {samples : α → List ((List Bool × Bool) × List Bool)}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hseed : ComputableTidilyInPolyTime seedBits input encUnary)
    (houtput : ComputableTidilyInPolyTime outputBits input encUnary)
    (hsamples : ComputableTidilyInPolyTime samples input
      (encList (encPair (encPair encBits encBool) encBits))) :
    IsPPTOn input (encPair (encList (encPair encBits encBool)) (encPair encBits encBits))
      (fun a => extractWordSeeds (count a) (seedBits a) (outputBits a) (samples a)) := by
  unfold extractWordSeeds
  ppt

attribute [program_certificate] isPPTOn_extractWordSeeds

/-- The third statistical transition for ordinary programs, with matrix universality discharged.
The ideal program preserves the complete pair output and independently samples seed and bits. -/
theorem SamplablePair.SeedRealization.extract_word_seeds {pair : SamplablePair}
    (saved : pair.SeedRealization) (inverseSlack outputBits : ℕ → ℕ)
    (hbudget : ∀ᶠ n in atTop, outputBits n = 0 ∨
      outputBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Game.Indistinguishable
      (fun (test : ℕ → List (List Bool × Bool) × List Bool × List Bool → Game) n =>
        (ProbComp.eval (OracleComp.replicate (count n) (saved.sampleWithSeed n) >>=
          extractWordSeeds (count n) (saved.length n) (outputBits n))).bind (test n))
      (fun test n => (ProbComp.eval (extractMatrixLabelsIdeal (pair.sample n) (count n)
        (count n * saved.length n) (outputBits n))).bind (test n)) (fun _ => True) := by
  dsimp only
  intro test _
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  have h := saved.remainingSeed_word_extraction inverseSlack outputBits
    (fun n => ProbComp.uniform (BitString (outputBits n * (count n * saved.length n))))
    (fun n key values => LinearHash.hash
      (blocksEquiv (m := outputBits n) (k := count n * saved.length n) key)
        (ofList (count n * saved.length n) values.flatten))
    (fun n => by
      simpa only [ProbComp.eval_uniform, List.map_ofFn, Function.comp_def, ← ofFn_blocksEquiv_symm,
        ofList_ofFn] using
        (LinearHash.isTwoUniversal_flat (count n * saved.length n) (outputBits n)).precompose
          (blocksEquiv (m := count n) (k := saved.length n)).symm.injective) hbudget
    (fun n result => test n (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) trivial
  apply h.congr
  intro n
  simp only [count, extractWordSeeds, ProbComp.eval_bind, eval_extractMatrixLabels,
    eval_extractMatrixLabelsIdeal, PMF.bind_map, PMF.bind_bind, Function.comp_def]

end Cslib.Crypto.Pseudoentropy
