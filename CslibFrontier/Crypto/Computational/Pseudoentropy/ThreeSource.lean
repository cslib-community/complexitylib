/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Crypto.Computational.Nonuniform.Basic
public import CslibFrontier.Crypto.Computational.Pseudoentropy.WordExtraction
public import CslibFrontier.Crypto.Computational.Pseudoentropy.WordSeedExtraction
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Combining the three pseudoentropy extractors

One collection of sampler seeds supplies the observations, hidden labels, and remaining seed
randomness. Each extractor keeps its independent public matrix seed. The security argument
replaces the remaining-seed component, then the labels, then the observations by uniform bits.
The middle transition uses a strict PPT test; the other two are statistical transitions.
The indexed theorem allows any valid choice from a polynomial-size family. The choice belongs
only to the security argument; the efficient test handles all indices uniformly.

## Main definitions

* `ThreeSource.extract`: sample once and hash observations, labels, and retained sampler seeds.
* `ThreeSource.seedLength`, `ThreeSource.outputLength`: exact input and output budgets.
* `ThreeSource.Efficient`: the shared uniformity contract for the extraction schedules.

## Main results

* `ThreeSource.isPolyTime_seedLength`, `ThreeSource.isPolyTime_outputLength`: extraction ledger
  lengths are computable in polynomial time.
* `ThreeSource.replace_remaining`, `ThreeSource.replace_observations`,
  `ThreeSource.replace_indexed_labels_withAdvice`, `ThreeSource.replace_indexed_labels`: hybrid
  reductions replacing each source component with uniform bits.
* `ThreeSource.isPPTOn_extract`: the composed program has a strict PPT certificate.
* `SamplablePair.HasGapWithAdvice.extract_indexed_three`,
  `SamplablePair.HasGap.extract_indexed_three`: security for any valid candidate choice relative
  to fixed advice and in the uniform case.
* `SamplablePair.HasGapWithAdvice.extract_three`, `SamplablePair.HasGap.extract_three`: the
  single-candidate computational interface.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Lemma 5 and the final proof of Theorem 1.
  [Holenstein2006].
  We use the shared Boolean-matrix family and make the three component transitions explicit.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. Statistical transitions quantify over all randomized
Boolean tests of the complete output; only the middle transition restricts tests to strict PPT.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.ThreeSource

open Probability BitString Turing.MultiTapeTM

/-- The observation word of a labeled seeded sample `((observation, label), seed)`. -/
abbrev sampleObservation {Obs Label Seed : Type*} (s : (Obs × Label) × Seed) : Obs := s.1.1

/-- The label of a labeled seeded sample `((observation, label), seed)`. -/
abbrev sampleLabel {Obs Label Seed : Type*} (s : (Obs × Label) × Seed) : Label := s.1.2

/-- Finish the first two components by hashing observations and retaining the label hash. -/
noncomputable def finish (bound observationBits : ℕ)
    (middle : List (List Bool) × List Bool × List Bool) : ProbComp (List Bool) := do
  let first ← extractWordObservations bound observationBits middle.1
  return first ++ (extractedSeed middle ++ extractedDigest middle)

/-- The last observation hash composes with a certified intermediate result. -/
theorem isPPTOn_finish {α : Type} {input : α ↪ List Bool} {bound observationBits : α → ℕ}
    {middle : α → List (List Bool) × List Bool × List Bool}
    (hbound : ComputableInPolyTime bound input encUnary)
    (hobservation : ComputableInPolyTime observationBits input encUnary)
    (hmiddle : ComputableInPolyTime middle input encWordExtractionOutput) :
    IsPPTOn input encBits (fun a => finish (bound a) (observationBits a) (middle a)) :=
  let hmid := (ComputableInPolyTime.fst input encBits).trans hmiddle.snd'
  (isPPTOn_extractWordObservations hbound hobservation hmiddle.fst').bind_with
    (ComputableInPolyTime.bitsAppend (.snd input encBits)
      (ComputableInPolyTime.bitsAppend hmid.fst' hmid.snd')).isPPTOn

attribute [program_certificate] isPPTOn_finish

/-- Sample once and hash all three components, retaining every independent matrix seed. -/
noncomputable def extract (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp ((List Bool × Bool) × List Bool)) : ProbComp (List Bool) := do
  let samples ← OracleComp.replicate count source
  let third ← extractWordSeeds count seedBits remainingBits samples
  let middle ← extractWordLabels count labelBits third.1
  let front ← finish bound observationBits middle
  return front ++ (extractedSeed third ++ extractedDigest third)

/-- The complete three-component program is PPT from ordinary sampler and size certificates. -/
theorem isPPTOn_extract {α : Type} {input : α ↪ List Bool}
    {count seedBits bound observationBits labelBits remainingBits : α → ℕ}
    {source : α → ProbComp ((List Bool × Bool) × List Bool)}
    (hsource : IsPPTOn input
      (encPair (encPair encBits encBool) encBits) source)
    (hcount : ComputableInPolyTime count input encUnary)
    (hseed : ComputableInPolyTime seedBits input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hobservation : ComputableInPolyTime observationBits input encUnary)
    (hlabel : ComputableInPolyTime labelBits input encUnary)
    (hremaining : ComputableInPolyTime remainingBits input encUnary) :
    IsPPTOn input encBits (fun a => extract (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a) (source a)) :=
  let eSamples := encList (encPair (encPair encBits encBool) encBits)
  let eThird := encPair (encList (encPair encBits encBool)) (encPair encBits encBits)
  let eMid := encPair (encList encBits) (encPair encBits encBits)
  let hparam := ComputableInPolyTime.fst input eSamples
  let hthird := isPPTOn_extractWordSeeds (hparam.trans hcount) (hparam.trans hseed)
    (hparam.trans hremaining) (.snd input eSamples)
  let hroot := (ComputableInPolyTime.fst (encPair input eSamples) eThird).fst'
  let hthirdVal := ComputableInPolyTime.snd (encPair input eSamples) eThird
  let hmiddle := isPPTOn_extractWordLabels (hroot.trans hcount) (hroot.trans hlabel) hthirdVal.fst'
  let hroot3 := (ComputableInPolyTime.fst (encPair (encPair input eSamples) eThird) eMid).fst'.fst'
  let hfinish := isPPTOn_finish (hroot3.trans hbound) (hroot3.trans hobservation) (.snd _ eMid)
  let hlastThird :=
    (ComputableInPolyTime.fst (encPair (encPair (encPair input eSamples) eThird) eMid)
      encBits).fst'.snd'
  let hlast := hfinish.bind_with
    (ComputableInPolyTime.bitsAppend (.snd _ encBits)
      (ComputableInPolyTime.bitsAppend hlastThird.snd'.fst' hlastThird.snd'.snd')).isPPTOn
  (hsource.replicate hcount).bind_with (hthird.bind_with (hmiddle.bind_with hlast))

attribute [program_certificate] isPPTOn_extract

/-- The first hybrid replaces the remaining-seed component by independent uniform bits. -/
noncomputable def withoutSeeds
    (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp (List Bool × Bool)) : ProbComp (List Bool) := do
  let samples ← OracleComp.replicate count source
  let middle ← extractWordLabels count labelBits samples
  let front ← finish bound observationBits middle
  let suffix ← BitString.sampleList (remainingBits * (count * seedBits) + remainingBits)
  return front ++ suffix

/-- The second hybrid also replaces the label component by independent uniform bits. -/
noncomputable def withoutLabels
    (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp (List Bool)) : ProbComp (List Bool) := do
  let samples ← OracleComp.replicate count source
  let first ← extractWordObservations bound observationBits samples
  let middle ← BitString.sampleList (labelBits * count + labelBits)
  let third ← BitString.sampleList (remainingBits * (count * seedBits) + remainingBits)
  return (first ++ middle) ++ third

/-- The output length counts every digest and every retained matrix seed. -/
def outputLength (count seedBits bound observationBits labelBits remainingBits : ℕ) : ℕ :=
  (observationBits * (count * (2 * bound + 1)) + observationBits) +
    (labelBits * count + labelBits) + (remainingBits * (count * seedBits) + remainingBits)

/-- Every supported output has the advertised length when sampled observations fit the bound.
The statement also covers zero-sized components and malformed retained seeds. -/
theorem length_extract (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp ((List Bool × Bool) × List Bool))
    (hbound : ∀ sample ∈ (ProbComp.eval source).support, (sampleObservation sample).length ≤ bound)
    {output : List Bool} (houtput : output ∈ (ProbComp.eval
      (extract count seedBits bound observationBits labelBits remainingBits source)).support) :
    output.length = outputLength count seedBits bound observationBits labelBits remainingBits := by
  simp only [extract, ProbComp.eval_bind, PMF.mem_support_bind_iff,
    ProbComp.eval_pure, PMF.mem_support_pure_iff] at houtput
  obtain ⟨samples, hsamples, third, hthird, middle, hmiddle, front, hfront, rfl⟩ := houtput
  have hsamples := (ProbComp.mem_support_replicate_iff count source samples).mp hsamples
  have hthird := extractMatrixLabels_result (count * seedBits) remainingBits List.flatten
    samples hthird
  have hmiddle := extractMatrixLabels_result count labelBits id third.1 hmiddle
  have hfits : ∀ observation ∈ middle.1, observation.length ≤ bound := by
    intro observation hobservation
    rw [hmiddle.1, hthird.1, List.map_map] at hobservation
    obtain ⟨sample, hsample, rfl⟩ := List.mem_map.mp hobservation
    exact hbound sample (hsamples.2 sample hsample)
  have hcount : middle.1.length = count := by
    rw [hmiddle.1, List.length_map, hthird.1, List.length_map, hsamples.1]
  simp only [finish, bind_pure_comp, ProbComp.eval_map, PMF.mem_support_map_iff] at hfront
  obtain ⟨first, hfirst, rfl⟩ := hfront
  have hfirst := length_extractWordObservations bound observationBits middle.1 hfits hfirst
  simp only [List.length_append, hfirst, hcount, hmiddle.2.1, hmiddle.2.2,
    hthird.2.1, hthird.2.2, outputLength, Nat.add_assoc]

/-- Original sampler coins followed by the three matrix seeds in execution order. -/
def seedLength (count seedBits bound observationBits labelBits remainingBits : ℕ) : ℕ :=
  count * seedBits + (remainingBits * (count * seedBits) +
    (labelBits * count + observationBits * (count * (2 * bound + 1))))

section Lengths

variable {α : Type} {input : α ↪ List Bool}
  {count seedBits bound observationBits labelBits remainingBits : α → ℕ}
  (hcount : ComputableInPolyTime count input encUnary)
  (hseed : ComputableInPolyTime seedBits input encUnary)
  (hbound : ComputableInPolyTime bound input encUnary)
  (hobservation : ComputableInPolyTime observationBits input encUnary)
  (hlabel : ComputableInPolyTime labelBits input encUnary)
  (hremaining : ComputableInPolyTime remainingBits input encUnary)

include hcount hseed hbound hobservation hlabel hremaining

/-- The exact seed ledger can be computed in unary from efficient dimensions. -/
theorem isPolyTime_seedLength :
    ComputableInPolyTime (fun a => seedLength (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a)) input encUnary :=
  let hcs := hcount.unary_mul' hseed
  let hobs := hobservation.unary_mul'
    (hcount.unary_mul' (((ComputableInPolyTime.const 2).unary_mul' hbound).unary_add' (.const 1)))
  hcs.unary_add'
    ((hremaining.unary_mul' hcs).unary_add' ((hlabel.unary_mul' hcount).unary_add' hobs))

/-- The exact output ledger can be computed in unary from efficient dimensions. -/
theorem isPolyTime_outputLength :
    ComputableInPolyTime (fun a => outputLength (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a)) input encUnary :=
  let hcs := hcount.unary_mul' hseed
  let hobs := hobservation.unary_mul'
    (hcount.unary_mul' (((ComputableInPolyTime.const 2).unary_mul' hbound).unary_add' (.const 1)))
  ((hobs.unary_add' hobservation).unary_add'
    ((hlabel.unary_mul' hcount).unary_add' hlabel)).unary_add'
    ((hremaining.unary_mul' hcs).unary_add' hremaining)

end Lengths

attribute [program_certificate] isPolyTime_seedLength isPolyTime_outputLength

/-- Retained matrix seeds cancel in the expansion budget: only the digest bits must exceed
the original sampler coins. `ThreeSource.Seeded` realizes this exact input length. -/
theorem seedLength_lt_outputLength_iff
    (count seedBits bound observationBits labelBits remainingBits : ℕ) :
    seedLength count seedBits bound observationBits labelBits remainingBits <
        outputLength count seedBits bound observationBits labelBits remainingBits ↔
      count * seedBits < observationBits + labelBits + remainingBits := by
  unfold seedLength outputLength
  lia

/-- Moving the independent ideal seed component to the end gives the first hybrid exactly. -/
theorem eval_ideal_remaining
    (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (source : ProbComp (List Bool × Bool)) :
    ProbComp.eval (do
      let third ← extractMatrixLabelsIdeal source count (count * seedBits) remainingBits
      let middle ← extractWordLabels count labelBits third.1
      let front ← finish bound observationBits middle
      return front ++ (extractedSeed third ++ extractedDigest third)) =
      ProbComp.eval (withoutSeeds count seedBits bound observationBits labelBits remainingBits
        source) := by
  simpa only [pmf_norm, withoutSeeds, PMF.map] using
    eval_extractMatrixLabelsIdeal_append source count (count * seedBits) remainingBits
      (fun samples => extractWordLabels count labelBits samples >>= finish bound observationBits)

/-- Once the label hash is ideal, its seed and digest can follow the observation extraction. -/
theorem eval_ideal_labels (count bound observationBits labelBits : ℕ)
    (source : ProbComp (List Bool)) :
    ProbComp.eval (extractWordLabelsIdeal source count labelBits >>= finish bound observationBits) =
      ProbComp.eval (do
        let samples ← OracleComp.replicate count source
        let first ← extractWordObservations bound observationBits samples
        let middle ← BitString.sampleList (labelBits * count + labelBits)
        return first ++ middle) := by
  simpa only [pmf_norm, extractWordLabelsIdeal, finish, PMF.map] using
    eval_extractMatrixLabelsIdeal_append source count count labelBits
      (extractWordObservations bound observationBits)

open Probability.PMF Filter in
/-- Statistical extraction replaces the third component while retaining the data needed by
the first two components. No efficiency assumption is needed for this postprocessing. -/
theorem replace_remaining {pair : SamplablePair} (saved : pair.SeedRealization)
    (bound inverseSlack observationBits labelBits remainingBits : ℕ → ℕ)
    (hbudget : ∀ᶠ n in atTop, remainingBits n = 0 ∨
      remainingBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Game.Indistinguishable
      (fun (test : ℕ → List Bool → Game) n =>
        (ProbComp.eval (extract (count n) (saved.length n) (bound n)
          (observationBits n) (labelBits n) (remainingBits n) (saved.sampleWithSeed n))).bind
            (test n))
      (fun test n => (ProbComp.eval (withoutSeeds (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n) (pair.sample n))).bind (test n))
      (fun _ => True) := by
  dsimp only
  intro test _
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  have h := saved.extract_word_seeds inverseSlack remainingBits hbudget
    (fun n third => (ProbComp.eval (do
      let middle ← extractWordLabels (count n) (labelBits n) third.1
      let front ← finish (bound n) (observationBits n) middle
      return front ++ (third.2.1 ++ third.2.2))).bind (test n)) trivial
  apply h.congr
  intro n
  simp only [← PMF.bind_bind, ← ProbComp.eval_bind, eval_ideal_remaining,
    extract, bind_assoc, count]

open Probability.PMF Filter in
/-- After the other two components are uniform, observation extraction completes the
statistical comparison with a single uniform word of the advertised total length. -/
theorem replace_observations {pair : SamplablePair} (saved : pair.SeedRealization)
    (bound inverseSlack observationBits labelBits remainingBits : ℕ → ℕ)
    (hbound : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hbudget : ∀ᶠ n in atTop, observationBits n = 0 ∨
      observationBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Game.Indistinguishable
      (fun (test : ℕ → List Bool → Game) n =>
        (ProbComp.eval (withoutLabels (count n) (saved.length n) (bound n)
          (observationBits n) (labelBits n) (remainingBits n) (Prod.fst <$> pair.sample n))).bind
            (test n))
      (fun test n => (uniformList (outputLength (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n))).bind (test n)) (fun _ => True) := by
  dsimp only
  intro test _
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  have h := saved.extract_word_observations bound inverseSlack observationBits hbound hbudget
    (fun n first => (ProbComp.eval (do
      let middle ← BitString.sampleList (labelBits n * count n + labelBits n)
      let third ← BitString.sampleList
        (remainingBits n * (count n * saved.length n) + remainingBits n)
      return (first ++ middle) ++ third)).bind (test n)) trivial
  apply h.congr
  intro n
  simp only [pmf_norm, withoutLabels, outputLength, count, BitString.eval_sampleList,
    uniformList_add, PMF.map, List.append_assoc]

/-- Plain polynomial-time computation of the schedules used by three-source extraction.
This contract covers every candidate; it imposes no computability requirement on the index chosen
in the security proof. Entropy and observation-size assumptions remain separate. -/
structure Efficient (candidates bound inverseSlack densityBound : ℕ → ℕ)
    (observationBits labelBits remainingBits numerator : ℕ → ℕ → ℕ) : Prop where
  candidates_isPolyTime : ComputableInPolyTime candidates encUnary encUnary
  bound_isPolyTime : ComputableInPolyTime bound encUnary encUnary
  observation_isPolyTime : ComputableInPolyTime
    (fun input => observationBits input.1 input.2) (encPair encUnary encUnary) encUnary
  label_isPolyTime : ComputableInPolyTime
    (fun input => labelBits input.1 input.2) (encPair encUnary encUnary) encUnary
  remaining_isPolyTime : ComputableInPolyTime
    (fun input => remainingBits input.1 input.2) (encPair encUnary encUnary) encUnary
  slack_isPolyTime : ComputableInPolyTime inverseSlack encUnary encUnary
  numerator_isPolyTime : ComputableInPolyTime
    (fun input => numerator input.1 input.2) (encPair encUnary encUnary) encUnary
  density_isPolyTime : ComputableInPolyTime densityBound encUnary encUnary

open Probability.PMF Filter in
/-- Indexed label extraction relative to fixed advice remains secure when the test computes the
observation hash and supplies the independent third component. Only the proof uses the chosen
valid index. -/
theorem replace_indexed_labels_withAdvice {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} (hpair : pair.HasGapWithAdvice gap advice)
    (saved : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates bound inverseSlack densityBound : ℕ → ℕ}
    {observationBits labelBits remainingBits numerator : ℕ → ℕ → ℕ}
    (efficient : ThreeSource.Efficient candidates bound inverseSlack densityBound
      observationBits labelBits remainingBits numerator)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      labelBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (adversary : ℕ × List Bool → ℕ → List Bool → ProbComp Bool)
    (hadversary : IsPPTOn (encPair (encPair (encPair encUnary encBits) encUnary) encBits)
      encBool (fun input => adversary input.1.1 input.1.2 input.2)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (withoutSeeds (count n) (saved.length n) (bound n)
        (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (pair.sample n) >>=
          adversary (n, advice n) (choose n)))
      (ProbComp.eval (withoutLabels (count n) (saved.length n) (bound n)
        (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (Prod.fst <$> pair.sample n) >>=
          adversary (n, advice n) (choose n)))) := by
  let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
  have hcount := ExtractionSchedule.isPolyTime_count .id' saved.length_isPolyTime
    efficient.slack_isPolyTime
  let test (a : ℕ × List Bool) (i : ℕ)
      (middle : List (List Bool) × List Bool × List Bool) : ProbComp Bool := do
    let front ← finish (bound a.1) (observationBits a.1 i) middle
    let suffix ← BitString.sampleList
      (remainingBits a.1 i * (count a.1 * saved.length a.1) + remainingBits a.1 i)
    adversary a i (front ++ suffix)
  let eAI := encPair (encPair encUnary encBits) encUnary
  let eMid := encPair (encList encBits) (encPair encBits encBits)
  let eIn := encPair eAI eMid
  have hni := (ComputableInPolyTime.fst eAI eMid).fst'.fst'.prod
    (ComputableInPolyTime.fst eAI eMid).snd'
  have hfinish := isPPTOn_finish
    ((ComputableInPolyTime.fst eAI eMid).fst'.fst'.trans efficient.bound_isPolyTime)
    (hni.trans efficient.observation_isPolyTime) (.snd eAI eMid)
  have hrem := ((ComputableInPolyTime.fst eIn encBits).trans hni).trans
    efficient.remaining_isPolyTime
  have hcs := (ComputableInPolyTime.fst eIn encBits).fst'.fst'.fst'.trans
    (hcount.unary_mul' saved.length_isPolyTime)
  have hsuffix := ((hrem.unary_mul' hcs).unary_add' hrem).sampleList
  have hp1 := ComputableInPolyTime.fst (encPair eIn encBits) encBits
  have hadv := hadversary.preprocess
    (hp1.fst'.fst'.prod (ComputableInPolyTime.bitsAppend hp1.snd' (.snd _ encBits)))
  have htest : IsPPTOn eIn encBool (fun ((a, i), middle) => test a i middle) :=
    (show (fun ((a, i), middle) => test a i middle) = (fun p => test p.1.1 p.1.2 p.2) from rfl) ▸
      (hfinish.bind_with (hsuffix.bind_with hadv) :
        IsPPTOn eIn encBool (fun p => test p.1.1 p.1.2 p.2))
  have h := hpair.extract_indexed_word_labels saved choose efficient.candidates_isPolyTime
    efficient.label_isPolyTime efficient.slack_isPolyTime efficient.numerator_isPolyTime
    efficient.density_isPolyTime hchoose hvalid hbudget test htest
  have hideal (a : ℕ × List Bool) (i : ℕ) :
      ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> pair.sample a.1) (count a.1)
        (labelBits a.1 i) >>= test a i) =
      ProbComp.eval (withoutLabels (count a.1) (saved.length a.1) (bound a.1)
        (observationBits a.1 i) (labelBits a.1 i) (remainingBits a.1 i)
        (Prod.fst <$> pair.sample a.1) >>=
          adversary a i) := by
    have heq := congrArg (fun distribution : PMF (List Bool) => distribution.bind (fun front =>
      ProbComp.eval (do
        let suffix ← BitString.sampleList
          (remainingBits a.1 i * (count a.1 * saved.length a.1) + remainingBits a.1 i)
        adversary a i (front ++ suffix))))
      (eval_ideal_labels (count a.1) (bound a.1) (observationBits a.1 i) (labelBits a.1 i)
        (Prod.fst <$> pair.sample a.1))
    simpa only [pmf_norm, test, withoutLabels] using heq
  apply h.congr
  intro n
  rw [hideal (n, advice n)]
  simp only [pmf_norm, count, test, withoutSeeds]

open Probability.PMF Filter in
/-- Indexed label extraction remains secure when the test computes the observation hash and
supplies the independent third component. Only the proof uses the chosen valid index. -/
theorem replace_indexed_labels {pair : SamplablePair} {gap : ℕ → ℝ} (hpair : pair.HasGap gap)
    (saved : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates bound inverseSlack densityBound : ℕ → ℕ}
    {observationBits labelBits remainingBits numerator : ℕ → ℕ → ℕ}
    (efficient : ThreeSource.Efficient candidates bound inverseSlack densityBound
      observationBits labelBits remainingBits numerator)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hbudget : ∀ᶠ n in atTop,
      labelBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (adversary : ℕ → ℕ → List Bool → ProbComp Bool)
    (hadversary : IsPPTOn (encPair (encPair encUnary encUnary) encBits)
      encBool (fun input => adversary input.1.1 input.1.2 input.2)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (withoutSeeds (count n) (saved.length n) (bound n)
        (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (pair.sample n) >>=
          adversary n (choose n)))
      (ProbComp.eval (withoutLabels (count n) (saved.length n) (bound n)
        (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (Prod.fst <$> pair.sample n) >>=
          adversary n (choose n)))) := by
  let p0 := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encUnary) encBits
  have hprepare := (p0.fst'.fst'.prod p0.snd').prod (.snd _ encBits)
  have htest : IsPPTOn (encPair (encPair (encPair encUnary encBits) encUnary) encBits)
      encBool (fun ((a, i), word) => adversary a.1 i word) :=
    (show (fun ((a, i), word) => adversary a.1 i word) =
        (fun x : ((ℕ × List Bool) × ℕ) × List Bool => adversary x.1.1.1 x.1.2 x.2) from rfl) ▸
      hadversary.preprocess hprepare
  have h := replace_indexed_labels_withAdvice
    (SamplablePair.hasGap_iff_hasGapWithAdvice_nil.mp hpair) saved choose efficient hchoose
    hvalid hbudget (fun a i => adversary a.1 i) htest
  dsimp only at h ⊢
  exact h

end Cslib.Crypto.Pseudoentropy.ThreeSource

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF BitString Filter Turing.MultiTapeTM

/-- A valid candidate in an efficient polynomial-size family passes the complete three-source
game argument relative to fixed advice. The candidate may vary arbitrarily with the parameter;
one efficient indexed test handles the entire family. All three entropy budgets are needed only at
the chosen candidate. -/
theorem SamplablePair.HasGapWithAdvice.extract_indexed_three {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} (hpair : pair.HasGapWithAdvice gap advice)
    (saved : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates bound inverseSlack densityBound : ℕ → ℕ}
    {observationBits labelBits remainingBits numerator : ℕ → ℕ → ℕ}
    (efficient : ThreeSource.Efficient candidates bound inverseSlack densityBound
      observationBits labelBits remainingBits numerator)
    (hfits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hfirst : ∀ᶠ n in atTop, observationBits n (choose n) = 0 ∨
      observationBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst))
    (hmiddle : ∀ᶠ n in atTop,
      labelBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (hlast : ∀ᶠ n in atTop, remainingBits n (choose n) = 0 ∨
      remainingBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n)))
    (test : ℕ × List Bool → ℕ → List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair (encPair encUnary encBits) encUnary) encBits)
      encBool (fun ((a, i), word) => test a i word)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (ThreeSource.extract (count n) (saved.length n) (bound n)
        (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (saved.sampleWithSeed n) >>=
          test (n, advice n) (choose n)))
      (ProbComp.eval (BitString.sampleList (ThreeSource.outputLength
        (count n) (saved.length n) (bound n)
        (observationBits n (choose n)) (labelBits n (choose n)) (remainingBits n (choose n))) >>=
          test (n, advice n) (choose n)))) := by
  let continuation := fun n word => ProbComp.eval (test (n, advice n) (choose n) word)
  have third := (ThreeSource.replace_remaining saved bound inverseSlack
    (fun n => observationBits n (choose n)) (fun n => labelBits n (choose n))
    (fun n => remainingBits n (choose n)) hlast) continuation trivial
  have middle := ThreeSource.replace_indexed_labels_withAdvice hpair saved choose efficient
    hchoose hvalid hmiddle test htest
  have first := (ThreeSource.replace_observations saved bound inverseSlack
    (fun n => observationBits n (choose n)) (fun n => labelBits n (choose n))
    (fun n => remainingBits n (choose n)) hfits hfirst) continuation trivial
  simp only [ProbComp.eval_bind, BitString.eval_sampleList, continuation] at third middle first ⊢
  apply negligible_of_le (third.add (middle.add first))
  intro n
  exact (Game.advantage_triangle _ _ _).trans
    (add_le_add le_rfl (Game.advantage_triangle _ _ _))

/-- A valid candidate in an efficient polynomial-size family passes the complete three-source
game argument. The candidate may vary arbitrarily with the parameter; one efficient indexed test
handles the entire family. All three entropy budgets are needed only at the chosen candidate. -/
theorem SamplablePair.HasGap.extract_indexed_three {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization) (choose : ℕ → ℕ)
    {candidates bound inverseSlack densityBound : ℕ → ℕ}
    {observationBits labelBits remainingBits numerator : ℕ → ℕ → ℕ}
    (efficient : ThreeSource.Efficient candidates bound inverseSlack densityBound
      observationBits labelBits remainingBits numerator)
    (hfits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hchoose : ∀ᶠ n in atTop, choose n < candidates n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n (choose n) ∧
      numerator n (choose n) ≤ dyadicSize (densityBound n) ∧
      (numerator n (choose n) : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hfirst : ∀ᶠ n in atTop, observationBits n (choose n) = 0 ∨
      observationBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst))
    (hmiddle : ∀ᶠ n in atTop,
      labelBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n (choose n) : ℝ) / dyadicSize (densityBound n)))
    (hlast : ∀ᶠ n in atTop, remainingBits n (choose n) = 0 ∨
      remainingBits n (choose n) +
        2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n)))
    (test : ℕ → ℕ → List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encUnary) encBits)
      encBool (fun ((n, i), word) => test n i word)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    Negligible (fun n => Game.advantage
      (ProbComp.eval (ThreeSource.extract (count n) (saved.length n) (bound n)
        (observationBits n (choose n))
        (labelBits n (choose n)) (remainingBits n (choose n)) (saved.sampleWithSeed n) >>=
          test n (choose n)))
      (ProbComp.eval (BitString.sampleList (ThreeSource.outputLength
        (count n) (saved.length n) (bound n)
        (observationBits n (choose n)) (labelBits n (choose n)) (remainingBits n (choose n))) >>=
          test n (choose n)))) := by
  let p0 := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encUnary) encBits
  have hprepare := (p0.fst'.fst'.prod p0.snd').prod (.snd _ encBits)
  have htest' : IsPPTOn (encPair (encPair (encPair encUnary encBits) encUnary) encBits)
      encBool (fun ((a, i), word) => test a.1 i word) :=
    (show (fun ((a, i), word) => test a.1 i word) =
        (fun x : ((ℕ × List Bool) × ℕ) × List Bool => test x.1.1.1 x.1.2 x.2) from rfl) ▸
      htest.preprocess hprepare
  have h := (SamplablePair.hasGap_iff_hasGapWithAdvice_nil.mp hpair).extract_indexed_three
    saved choose efficient hfits hchoose hvalid hfirst hmiddle hlast
    (fun a i => test a.1 i) htest'
  dsimp only at h ⊢
  exact h

/-- The three-source construction is computationally uniform relative to fixed advice under its
three entropy budgets. The schedules must be computed by uniform polynomial-time algorithms.
`ThreeSource.Seeded` implements this ensemble deterministically with an exact seed budget, and
`EntropyGrid` supplies budgets for which some candidate is valid. -/
theorem SamplablePair.HasGapWithAdvice.extract_three {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} (hpair : pair.HasGapWithAdvice gap advice)
    (saved : pair.SeedRealization)
    {bound inverseSlack observationBits labelBits remainingBits numerator densityBound : ℕ → ℕ}
    (efficient : ThreeSource.Efficient (fun _ => 1) bound inverseSlack densityBound
      (fun n _ => observationBits n) (fun n _ => labelBits n)
      (fun n _ => remainingBits n) (fun n _ => numerator n))
    (hfits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n ∧ numerator n ≤ dyadicSize (densityBound n) ∧
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hfirst : ∀ᶠ n in atTop, observationBits n = 0 ∨
      observationBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst))
    (hmiddle : ∀ᶠ n in atTop,
      labelBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n : ℝ) / dyadicSize (densityBound n)))
    (hlast : ∀ᶠ n in atTop, remainingBits n = 0 ∨
      remainingBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    IndistinguishableWithAdvice advice
      (fun n => ProbComp.eval (ThreeSource.extract (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n) (saved.sampleWithSeed n)))
      (fun n => uniformList (ThreeSource.outputLength (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n))) := by
  dsimp only
  intro adversary hadversary
  let p0 := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encUnary) encBits
  have hprepare := p0.fst'.prod (.snd _ encBits)
  have htest : IsPPTOn (encPair (encPair (encPair encUnary encBits) encUnary) encBits)
      encBool (fun ((a, _), word) => adversary (a, word)) :=
    (show (fun ((a, _), word) => adversary (a, word)) =
        (fun x : ((ℕ × List Bool) × ℕ) × List Bool => adversary (x.1.1, x.2)) from rfl) ▸
      hadversary.preprocess hprepare
  have h := hpair.extract_indexed_three saved (fun _ => 0)
    (candidates := fun _ => 1) (observationBits := fun n _ => observationBits n)
    (labelBits := fun n _ => labelBits n) (remainingBits := fun n _ => remainingBits n)
    (numerator := fun n _ => numerator n) efficient hfits
    (Eventually.of_forall (by intro n; decide))
    hvalid hfirst hmiddle hlast (fun a _ word => adversary (a, word)) htest
  simpa only [distinguishingGame, PMF.monad_bind_eq_bind, ProbComp.eval_bind,
    BitString.eval_sampleList] using h

/-- The three-source construction is computationally uniform under its three entropy budgets.
The schedules must be computed by uniform polynomial-time algorithms. `ThreeSource.Seeded`
implements this ensemble deterministically with an exact seed budget, and `EntropyGrid` supplies
budgets for which some candidate is valid. -/
theorem SamplablePair.HasGap.extract_three {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization)
    {bound inverseSlack observationBits labelBits remainingBits numerator densityBound : ℕ → ℕ}
    (efficient : ThreeSource.Efficient (fun _ => 1) bound inverseSlack densityBound
      (fun n _ => observationBits n) (fun n _ => labelBits n)
      (fun n _ => remainingBits n) (fun n _ => numerator n))
    (hfits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ bound n)
    (hvalid : ∀ᶠ n in atTop, 0 < numerator n ∧ numerator n ≤ dyadicSize (densityBound n) ∧
      (numerator n : ℝ) / dyadicSize (densityBound n) ≤
        conditionalEntropy (pair.joint n) + gap n)
    (hfirst : ∀ᶠ n in atTop, observationBits n = 0 ∨
      observationBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          entropy ((pair.joint n).map Prod.fst))
    (hmiddle : ∀ᶠ n in atTop,
      labelBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          ((numerator n : ℝ) / dyadicSize (densityBound n)))
    (hlast : ∀ᶠ n in atTop, remainingBits n = 0 ∨
      remainingBits n + 2 * (ExtractionSchedule.slack n (saved.length n) (inverseSlack n) : ℝ) ≤
        ExtractionSchedule.count n (saved.length n) (inverseSlack n) *
          (saved.length n - entropy ((pair.joint n).map Prod.fst) -
            conditionalEntropy (pair.joint n))) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) (inverseSlack n)
    ComputationallyIndistinguishable
      (fun n => ProbComp.eval (ThreeSource.extract (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n) (saved.sampleWithSeed n)))
      (fun n => uniformList (ThreeSource.outputLength (count n) (saved.length n) (bound n)
        (observationBits n) (labelBits n) (remainingBits n))) :=
  computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil.mpr
    ((SamplablePair.hasGap_iff_hasGapWithAdvice_nil.mp hpair).extract_three saved efficient
      hfits hvalid hfirst hmiddle hlast)

end Cslib.Crypto.Pseudoentropy
