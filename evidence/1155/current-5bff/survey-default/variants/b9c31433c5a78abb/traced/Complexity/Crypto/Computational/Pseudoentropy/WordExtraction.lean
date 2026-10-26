/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.Seed
public import Complexity.Probability.UniformNat
public import Complexity.Crypto.Computational.Pseudoentropy.MatrixExtraction
import Complexity.Crypto.Computational.Pseudoentropy.LabelExtraction
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# Executable extraction of repeated labels

The program samples a flat Boolean matrix, hashes the labels, and retains every observation and
the matrix seed. Its exact law agrees with the finite two-universal family used by the extraction
theorems. The supplied input width also defines behavior on malformed sample lists: labels are
truncated or padded with false before hashing.

## Main definitions

* `extractWordLabels`, `extractWordLabelsIdeal`: actual and ideal matrix-extraction programs.

## Main results

* `isPPTOn_extractWordLabels`: certify sampling, normalization, hashing and copying.
* `isPPTOn_extractedWordTest`: the extracted word test is strict PPT.
* `SamplablePair.HasGap.extract_indexed_word_labels`: computational extraction for one
  uniformly efficient family of tests and arbitrary valid index choices.
* `SamplablePair.HasGap.extract_word_labels`: the ordinary single-test interface.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Game 2.
  [Holenstein2006].
  The Boolean-matrix implementation replaces the write-up's finite-field hash family.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/


diag1155_install
@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability BitString Turing.MultiTapeTM

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
    (hsamples : ComputableInPolyTime samples input (encList (encPair encBits encBool))) :
    IsPPTOn input
      (encPair (encList encBits) (encPair encBits encBits))
      (fun a => extractWordLabels (count a) (outputBits a) (samples a)) := by
  unfold extractWordLabels
  ppt

attribute [program_certificate] isPPTOn_extractWordLabels

/-- The finite and word extractors have exactly the same law, even on malformed sample lists. -/
theorem eval_extractWordLabels (count outputBits : ℕ) (samples : List (List Bool × Bool)) :
    ProbComp.eval (extractWordLabels count outputBits samples) =
      (ProbComp.eval (extractLabels (ProbComp.uniform (BitString (outputBits * count)))
        (fun seed bits => LinearHash.hash (blocksEquiv (m := outputBits) (k := count) seed)
          (ofList count bits))
          samples)).map (fun result => (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  exact eval_extractMatrixLabels count outputBits id samples

/-- The ideal word program agrees with the finite ideal distribution and retains the full seed. -/
theorem eval_extractWordLabelsIdeal (source : ProbComp (List Bool)) (count outputBits : ℕ) :
    ProbComp.eval (extractWordLabelsIdeal source count outputBits) =
      (extractLabelsIdeal (Output := BitString outputBits) source count
        (ProbComp.uniform (BitString (outputBits * count)))).map
          (fun result => (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  exact eval_extractMatrixLabelsIdeal source count count outputBits

/-- An ordinary word test after extraction gives the finite test required by the security
theorem. Sampling, padding, hashing, and encoding the public data are all charged to PPT.
The test and dimensions may depend on any encoded runtime parameter. -/
theorem isPPTOn_extractedWordTest {α : Type} {input : α ↪ List Bool} {count outputBits : α → ℕ}
    (test : α → List (List Bool) × List Bool × List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair input (encPair (encList encBits)
      (encPair encBits encBits))) encBool (fun input => test input.1 input.2))
    (hcount : ComputableInPolyTime count input encUnary)
    (houtput : ComputableInPolyTime outputBits input encUnary) :
    IsPPTOn (encPair input
      (encList (encPair encBits encBool))) encBool
      (fun input => do
        let result ← extractLabels
          (ProbComp.uniform (BitString (outputBits input.1 * count input.1)))
          (fun seed bits => LinearHash.hash
            (blocksEquiv (m := outputBits input.1) (k := count input.1) seed)
            (ofList (count input.1) bits)) input.2
        test input.1 (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  have hword : IsPPTOn (encPair input
      (encList (encPair encBits encBool))) encBool
      (fun input => extractWordLabels (count input.1) (outputBits input.1) input.2 >>=
        test input.1) := by ppt
  apply hword.congr
  intro input
  simp only [ProbComp.eval_bind, eval_extractWordLabels, PMF.bind_map, Function.comp_def]

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
    (htest : IsPPTOn (encPair (encPair encUnary encUnary)
      (encPair (encList encBits) (encPair encBits encBits)))
      encBool (fun input => test input.1.1 input.1.2 input.2)) :
    let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (do
        let samples ← OracleComp.replicate (count n) (pair.sample n)
        let result ← extractWordLabels (count n) (outputBits n (choose n)) samples
        test n (choose n) result))
      (ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n)
        (outputBits n (choose n)) >>= test n (choose n)))) := by
  have hcandidates := hcandidates.tidy
  have houtput := houtput.tidy
  have hslack := hslack.tidy
  have hnumerator := hnumerator.tidy
  have hdensity := hdensity.tidy
  let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
  have hcount : ComputableTidilyInPolyTime count encUnary encUnary :=
    (ExtractionSchedule.isPolyTime_count (.of_tidy (by fun_prop))
      realization.length_isPolyTime (.of_tidy hslack)).tidy
  have h := hpair.extract_indexed_labels realization choose
    (inverseSlack := inverseSlack)
    (fun n i => ProbComp.uniform (BitString (outputBits n i * count n)))
    (fun n i seed bits => LinearHash.hash
      (blocksEquiv (m := outputBits n i) (k := count n) seed) (ofList (count n) bits))
    (fun n i result => test n i (result.1, List.ofFn result.2.1, List.ofFn result.2.2))
    (isPPTOn_extractedWordTest (count := fun input : ℕ × ℕ => count input.1)
      (outputBits := fun input : ℕ × ℕ => outputBits input.1 input.2)
      (fun input : ℕ × ℕ => test input.1 input.2) htest
      (.of_tidy (by fun_prop)) (.of_tidy houtput))
    (.of_tidy hcandidates) (.of_tidy hslack) (.of_tidy hnumerator) (.of_tidy hdensity) hchoose
      hvalid
    (fun n i => by simpa only [ProbComp.eval_uniform, ofList_ofFn] using
      LinearHash.isTwoUniversal_flat (count n) (outputBits n i)) hbudget
  apply h.congr
  intro n
  have hpublic : ProbComp.eval ((fun value => pair.encode n value.1) <$>
      pair.latentSample n) = ProbComp.eval (Prod.fst <$> pair.sample n) := by
    simp only [ProbComp.eval_map, pair.eval_latentSample, pair.eval_sample, PMF.map_comp,
      Function.comp_def]
  simp only [count, ProbComp.eval_bind, eval_extractWordLabels,
    eval_extractWordLabelsIdeal, PMF.bind_map, Function.comp_def, extractLabelsIdeal,
    ProbComp.eval_replicate_congr hpublic
      (ExtractionSchedule.count n (realization.length n) (inverseSlack n))]

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
    (htest : IsPPTOn (encPair encUnary (encPair (encList encBits)
      (encPair encBits encBits))) encBool (fun input => test input.1 input.2)) :
    let count := fun n => ExtractionSchedule.count n (realization.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (do
        let samples ← OracleComp.replicate (count n) (pair.sample n)
        let result ← extractWordLabels (count n) (outputBits n) samples
        test n result))
      (ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> pair.sample n) (count n)
        (outputBits n) >>= test n))) := by
  exact hpair.extract_indexed_word_labels realization (fun _ => 0)
    (candidates := fun _ => 1) (outputBits := fun n _ => outputBits n)
    (numerator := fun n _ => numerator n) (by polytime) (by polytime) hslack (by polytime)
    hdensity (Eventually.of_forall (by intro n; decide)) hvalid hbudget (fun n _ => test n) (by ppt)

end Cslib.Crypto.Pseudoentropy
