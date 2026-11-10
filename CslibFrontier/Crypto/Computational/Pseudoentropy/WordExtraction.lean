/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.Seed
public import CslibFrontier.Probability.UniformNat
public import CslibFrontier.Crypto.Computational.Pseudoentropy.MatrixExtraction
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Computational.Pseudoentropy.LabelExtraction
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Executable extraction of repeated labels

The program samples a flat Boolean matrix, hashes the labels, and retains every observation and
the matrix seed. Its exact law agrees with the finite two-universal family used by the extraction
theorems. The supplied input width also defines behavior on malformed sample lists: labels are
truncated or padded with false before hashing.

## Main definitions

* `encWordExtractionOutput`: the encoding of an extraction output `(xs, seed, digest)`.
* `extractWordLabels`, `extractWordLabelsIdeal`: actual and ideal matrix-extraction programs.

## Main results

* `isPPTOn_extractWordLabels`: certify sampling, normalization, hashing and copying.
* `isPPTOn_extractedWordTest`: the extracted word test is strict PPT.
* `SamplablePair.HasGapWithAdvice.extract_indexed_word_labels`,
  `SamplablePair.HasGap.extract_indexed_word_labels`: computational extraction for one
  uniformly efficient family of tests and arbitrary valid index choices, relative to fixed advice
  and in the uniform case.
* `SamplablePair.HasGapWithAdvice.extract_word_labels`,
  `SamplablePair.HasGap.extract_word_labels`: the single-test interface.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Game 2.
  [Holenstein2006].
  The Boolean-matrix implementation replaces the write-up's finite-field hash family.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability BitString Turing.MultiTapeTM

/-- Output `(xs, seed, digest)` of word-label extraction: the list of retained observation words,
then the hash seed and the digest as bit words. The list and the seed are framed; within the list,
each observation is framed. -/
abbrev encWordExtractionOutput : List (List Bool) × List Bool × List Bool ↪ List Bool :=
  encPair (encList encBits) (encPair encBits encBits)

/-- Extract labels using an explicitly sampled matrix, retaining observations and the full seed. -/
noncomputable def extractWordLabels (count outputBits : ℕ) (samples : List (List Bool × Bool)) :
    ProbComp (List (List Bool) × List Bool × List Bool) :=
  extractMatrixLabels count outputBits id samples

/-- The comparison experiment keeps the observations and independently samples the hash seed
and output bits. -/
noncomputable def extractWordLabelsIdeal (source : ProbComp (List Bool)) (count outputBits : ℕ) :
    ProbComp (List (List Bool) × List Bool × List Bool) :=
  extractMatrixLabelsIdeal source count count outputBits

/-- Runtime dimensions and sample lists compose into a strict PPT extractor. -/
theorem isPPTOn_extractWordLabels {α : Type} {input : α ↪ List Bool} {count outputBits : α → ℕ}
    {samples : α → List (List Bool × Bool)}
    (hcount : ComputableInPolyTime count input encUnary)
    (houtput : ComputableInPolyTime outputBits input encUnary)
    (hsamples : ComputableInPolyTime samples input encLabeledSamples) :
    IsPPTOn input encWordExtractionOutput
      (fun a => extractWordLabels (count a) (outputBits a) (samples a)) :=
  isPPTOn_extractMatrixLabels hcount houtput
    ((bits_encList_polyTime encBool).2.comp (.snd input (encList encBool))) hsamples

attribute [program_certificate] isPPTOn_extractWordLabels

/-- The finite and word extractors have exactly the same law, even on malformed sample lists. -/
theorem eval_extractWordLabels (count outputBits : ℕ) (samples : List (List Bool × Bool)) :
    ProbComp.eval (extractWordLabels count outputBits samples) =
      (ProbComp.eval (extractLabels (ProbComp.uniform (BitString (outputBits * count)))
        (fun seed bits => LinearHash.hash (blocksEquiv (m := outputBits) (k := count) seed)
          (ofList count bits))
          samples)).map (fun result =>
            (result.1, List.ofFn (extractedSeed result), List.ofFn (extractedDigest result))) :=
  eval_extractMatrixLabels count outputBits id samples

/-- The ideal word program agrees with the finite ideal distribution and retains the full seed. -/
theorem eval_extractWordLabelsIdeal (source : ProbComp (List Bool)) (count outputBits : ℕ) :
    ProbComp.eval (extractWordLabelsIdeal source count outputBits) =
      (extractLabelsIdeal (Output := BitString outputBits) source count
        (ProbComp.uniform (BitString (outputBits * count)))).map
          (fun result =>
            (result.1, List.ofFn (extractedSeed result), List.ofFn (extractedDigest result))) :=
  eval_extractMatrixLabelsIdeal source count count outputBits

/-- An ordinary word test after extraction gives the finite test required by the security
theorem. Sampling, padding, hashing, and encoding the public data are all charged to PPT.
The test and dimensions may depend on any encoded runtime parameter. -/
theorem isPPTOn_extractedWordTest {α : Type} {input : α ↪ List Bool} {count outputBits : α → ℕ}
    (test : α → List (List Bool) × List Bool × List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair input encWordExtractionOutput) encBool
      (fun input => test input.1 input.2))
    (hcount : ComputableInPolyTime count input encUnary)
    (houtput : ComputableInPolyTime outputBits input encUnary) :
    IsPPTOn (encPair input encLabeledSamples) encBool
      (fun input => do
        let result ← extractLabels
          (ProbComp.uniform (BitString (outputBits input.1 * count input.1)))
          (fun seed bits => LinearHash.hash
            (blocksEquiv (m := outputBits input.1) (k := count input.1) seed)
            (ofList (count input.1) bits)) input.2
        test input.1
          (result.1, List.ofFn (extractedSeed result), List.ofFn (extractedDigest result))) := by
  let sampleEnc := encList (encPair encBits encBool)
  let resultEnc := encPair (encList encBits) (encPair encBits encBits)
  have hparam := ComputableInPolyTime.fst input sampleEnc
  have hword := (isPPTOn_extractWordLabels (hcount.comp hparam) (houtput.comp hparam)
    (.snd input sampleEnc)).bind_with (second := fun p => test p.1)
    (htest.preprocess ((hparam.comp (.fst _ resultEnc)).prod (.snd _ resultEnc)))
  refine hword.congr fun input => ?_
  simp only [pmf_norm, eval_extractWordLabels]

open Filter in
/-- An efficient indexed family of word extractors is computationally uniform relative to fixed
advice along any bounded choice satisfying the entropy budget. The choice is used only in the
proof and need not be efficient; the reduction certifies the whole family of tests. -/
theorem SamplablePair.HasGapWithAdvice.extract_indexed_word_labels {pair : SamplablePair}
    {gap : ℕ → ℝ} {advice : ℕ → List Bool} (hpair : pair.HasGapWithAdvice gap advice)
    (realization : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates inverseSlack densityBound : ℕ → ℕ} {outputBits numerator : ℕ → ℕ → ℕ}
    (hcandidates : ComputableInPolyTime candidates encUnary encUnary)
    (houtput : ComputableInPolyTime (fun input => outputBits input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hslack : ComputableInPolyTime inverseSlack encUnary encUnary)
    (hnumerator : ComputableInPolyTime (fun input => numerator input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      outputBits n (choose n) +
        2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (test : ℕ × List Bool → ℕ → List (List Bool) × List Bool × List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair (encPair encUnary encBits) encUnary)
      encWordExtractionOutput) encBool (fun ((a, i), result) => test a i result)) :
    let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (do
        let samples ← OracleComp.replicate (count n) (pair.sample n)
        let result ← extractWordLabels (count n) (outputBits n (choose n)) samples
        test (n, advice n) (choose n) result))
      (ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n)
        (outputBits n (choose n)) >>= test (n, advice n) (choose n)))) := by
  let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
  have hcount := ExtractionSchedule.isPolyTime_count .id'
    realization.length_isPolyTime hslack
  have hn := (ComputableInPolyTime.fst (encPair encUnary encBits) encUnary).fst'
  have h := hpair.extract_indexed_labels realization choose
    (inverseSlack := inverseSlack)
    (fun n i => ProbComp.uniform (BitString (outputBits n i * count n)))
    (fun n i seed bits => LinearHash.hash
      (blocksEquiv (m := outputBits n i) (k := count n) seed) (ofList (count n) bits))
    (fun a i result => test a i (result.1, List.ofFn result.2.1, List.ofFn result.2.2))
    (isPPTOn_extractedWordTest
      (count := fun input : (ℕ × List Bool) × ℕ => count input.1.1)
      (outputBits := fun input : (ℕ × List Bool) × ℕ => outputBits input.1.1 input.2)
      (fun input : (ℕ × List Bool) × ℕ => test input.1 input.2) htest
      (hcount.comp hn) (houtput.comp (hn.prod (.snd _ encUnary))))
    hcandidates hslack hnumerator hdensity hchoose hvalid
    (fun n i => by simpa only [ProbComp.eval_uniform, ofList_ofFn] using
      LinearHash.isTwoUniversal_flat (count n) (outputBits n i)) hbudget
  refine h.congr fun n => ?_
  have hpublic : ProbComp.eval ((fun value => pair.encode n value.1) <$>
      pair.latentSample n) = ProbComp.eval (Prod.fst <$> pair.sample n) := by
    simp only [pmf_norm, pair.eval_latentSample, pair.eval_sample]
  simp only [count, ProbComp.eval_bind, eval_extractWordLabels,
    eval_extractWordLabelsIdeal, PMF.bind_map, Function.comp_def, extractLabelsIdeal,
    ProbComp.eval_replicate_congr hpublic
      (ExtractionSchedule.count n (realization.length n) (inverseSlack n))]

open Filter in
/-- An efficient indexed family of word extractors is computationally uniform along any bounded
choice satisfying the entropy budget. The choice is used only in the proof and need not be
efficient; the reduction certifies the whole family of tests. -/
theorem SamplablePair.HasGap.extract_indexed_word_labels {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates inverseSlack densityBound : ℕ → ℕ} {outputBits numerator : ℕ → ℕ → ℕ}
    (hcandidates : ComputableInPolyTime candidates encUnary encUnary)
    (houtput : ComputableInPolyTime (fun input => outputBits input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hslack : ComputableInPolyTime inverseSlack encUnary encUnary)
    (hnumerator : ComputableInPolyTime (fun input => numerator input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      outputBits n (choose n) +
        2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (test : ℕ → ℕ → List (List Bool) × List Bool × List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encUnary) encWordExtractionOutput)
      encBool (fun ((n, i), result) => test n i result)) :
    let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (do
        let samples ← OracleComp.replicate (count n) (pair.sample n)
        let result ← extractWordLabels (count n) (outputBits n (choose n)) samples
        test n (choose n) result))
      (ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n)
        (outputBits n (choose n)) >>= test n (choose n)))) := by
  have houter := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encUnary)
    (encPair (encList encBits) (encPair encBits encBits))
  have h := (SamplablePair.hasGap_iff_hasGapWithAdvice_nil.mp hpair).extract_indexed_word_labels
    realization choose hcandidates houtput hslack hnumerator hdensity hchoose hvalid hbudget
    (fun a => test a.1) (htest.preprocess ((houter.fst'.fst'.prod houter.snd').prod (.snd _ _)))
  dsimp only at h ⊢
  exact h

open Filter in
/-- Computational label extraction relative to fixed advice as two ordinary word programs. The
client supplies the entropy budget and a certified test; matrix sampling, finite representations,
and the uniform prediction reduction are discharged by the library. -/
theorem SamplablePair.HasGapWithAdvice.extract_word_labels {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} (hpair : pair.HasGapWithAdvice gap advice)
    (realization : pair.SeedRealization)
    {outputBits inverseSlack numerator densityBound : ℕ → ℕ}
    (houtput : ComputableInPolyTime outputBits encUnary encUnary)
    (hslack : ComputableInPolyTime inverseSlack encUnary encUnary)
    (hnumerator : ComputableInPolyTime numerator encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n ∧ numerator n ≤ dyadicSize (densityBound n) ∧
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      outputBits n + 2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n : ℝ) / dyadicSize (densityBound n)))
    (test : ℕ × List Bool → List (List Bool) × List Bool × List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encBits) encWordExtractionOutput) encBool
      (fun input => test input.1 input.2)) :
    let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (do
        let samples ← OracleComp.replicate (count n) (pair.sample n)
        let result ← extractWordLabels (count n) (outputBits n) samples
        test (n, advice n) result))
      (ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n)
        (outputBits n) >>= test (n, advice n)))) := by
  have hn := ComputableInPolyTime.fst encUnary encUnary
  have houter := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encUnary)
    (encPair (encList encBits) (encPair encBits encBits))
  exact hpair.extract_indexed_word_labels realization (fun _ => 0)
    (outputBits := fun n _ => outputBits n) (numerator := fun n _ => numerator n)
    (.const 1) (houtput.comp hn) hslack (hnumerator.comp hn) hdensity
    (Eventually.of_forall (by intro n; decide)) hvalid hbudget (fun a _ => test a)
    (htest.preprocess (houter.fst'.prod (.snd _ _)))

open Filter in
/-- Computational label extraction as two ordinary word programs. The client supplies the
entropy budget and a certified test; matrix sampling, finite representations, and the uniform
prediction reduction are discharged by the library. -/
theorem SamplablePair.HasGap.extract_word_labels {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (realization : pair.SeedRealization)
    {outputBits inverseSlack numerator densityBound : ℕ → ℕ}
    (houtput : ComputableInPolyTime outputBits encUnary encUnary)
    (hslack : ComputableInPolyTime inverseSlack encUnary encUnary)
    (hnumerator : ComputableInPolyTime numerator encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n ∧ numerator n ≤ dyadicSize (densityBound n) ∧
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        PMF.conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      outputBits n + 2 * (ExtractionSchedule.slack n (realization.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (realization.length n) (inverseSlack n) *
          ((numerator n : ℝ) / dyadicSize (densityBound n)))
    (test : ℕ → List (List Bool) × List Bool × List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair encUnary encWordExtractionOutput) encBool
      (fun input => test input.1 input.2)) :
    let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (do
        let samples ← OracleComp.replicate (count n) (pair.sample n)
        let result ← extractWordLabels (count n) (outputBits n) samples
        test n result))
      (ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n)
        (outputBits n) >>= test n))) := by
  have houter := ComputableInPolyTime.fst (encPair encUnary encBits)
    (encPair (encList encBits) (encPair encBits encBits))
  have h := (SamplablePair.hasGap_iff_hasGapWithAdvice_nil.mp hpair).extract_word_labels
    realization houtput hslack hnumerator hdensity hvalid hbudget
    (fun a => test a.1) (htest.preprocess (houter.fst'.prod (.snd _ _)))
  dsimp only at h ⊢
  exact h

end Cslib.Crypto.Pseudoentropy
