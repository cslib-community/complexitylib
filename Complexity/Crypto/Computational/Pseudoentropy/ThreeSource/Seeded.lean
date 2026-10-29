/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Probabilistic.LinearHash
import Complexity.Tactic.PolyTime.Init

/-!
# Deterministic three-source extraction

The input contains exactly the original sampler seeds and three independent matrix seeds.
Ordinary word operations split this tape and evaluate the same hashes as the probabilistic
program. The implementation uses the shared row parser and polynomial-time combinators.

## Main definitions

* `hashSamples`: evaluate the three hashes with supplied keys, retaining each key.
* `generate`: parse one input seed and run the deterministic construction.

## Main results

* `isPolyTime_hashSamples`: deterministic hashing composes efficient word operations.
* `isPolyTime_generate`: runtime dimensions and a captured evaluator compose efficiently.
* `generate_distribution`: uniform input bits give independent sampler coins and matrix seeds.
* `eval_generate`, `eval_generate_of_realization`: equality with the sampled extractor.
* `length_generate`: every correctly sized seed produces the declared number of output bits.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, Lemma 5.
  [Holenstein2006].
  The matrix seeds are retained in full, so their lengths cancel from the expansion budget.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed certificates and the shared list-row parser.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.ThreeSource

open Probability BitString Turing.MultiTapeTM

/-- Evaluate the three hashes using supplied matrix seeds, preserving all three seeds. -/
def hashSamples (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (samples : List ((List Bool × Bool) × List Bool))
    (firstKey middleKey lastKey : List Bool) : List Bool :=
  let observations := ((samples.map (fun sample => sample.1.1)).map (padWord bound)).flatten
  let labels := listRow count 0 (samples.map (fun sample => sample.1.2))
  let seeds := listRow (count * seedBits) 0 (samples.map Prod.snd).flatten
  ((firstKey ++ LinearHash.wordHash observationBits firstKey observations) ++
    (middleKey ++ LinearHash.wordHash labelBits middleKey labels)) ++
      (lastKey ++ LinearHash.wordHash remainingBits lastKey seeds)

/-- Deterministic hashing composes the same efficient word operations as the sampled program. -/
theorem isPolyTime_hashSamples {α : Type} {input : α ↪ List Bool}
    {count seedBits bound observationBits labelBits remainingBits : α → ℕ}
    {samples : α → List ((List Bool × Bool) × List Bool)}
    {firstKey middleKey lastKey : α → List Bool}
    (hcount : ComputableInPolyTime count input encUnary)
    (hseed : ComputableInPolyTime seedBits input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hobservation : ComputableInPolyTime observationBits input encUnary)
    (hlabel : ComputableInPolyTime labelBits input encUnary)
    (hremaining : ComputableInPolyTime remainingBits input encUnary)
    (hsamples : ComputableInPolyTime samples input
      (encList (encPair (encPair encBits encBool) encBits)))
    (hfirst : ComputableInPolyTime firstKey input encBits)
    (hmiddle : ComputableInPolyTime middleKey input encBits)
    (hlast : ComputableInPolyTime lastKey input encBits) :
    ComputableInPolyTime (fun a => hashSamples (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a) (samples a)
      (firstKey a) (middleKey a) (lastKey a)) input encBits := by
  let sampleEncoding := encPair (encPair encBits encBool) encBits
  have houter := ComputableInPolyTime.fst input sampleEncoding
  have hsample := ComputableInPolyTime.snd input sampleEncoding
  have hpad := ComputableInPolyTime.bitsPadWord (hbound.comp houter) hsample.fst'.fst'
  have hobservationWords := ComputableInPolyTime.mapWithInput
    (encB := encBits)
    (f := fun a (sample : (List Bool × Bool) × List Bool) => padWord (bound a) sample.1.1)
    hsamples (by simpa only [Function.comp_def] using hpad)
  have hobservations := ComputableInPolyTime.bitsFlatten hobservationWords
  have hlabelWord := ComputableInPolyTime.mapToBitsWithInput
    (f := fun (_ : α) (sample : (List Bool × Bool) × List Bool) => sample.1.2)
    hsamples hsample.fst'.snd'
  have hlabels := ComputableInPolyTime.bitsRowWithInput hcount
    (ComputableInPolyTime.const 0) hlabelWord
  have hseedWords := (ComputableInPolyTime.map
    (ComputableInPolyTime.snd (encPair encBits encBool) encBits)).comp hsamples
  have hseeds := ComputableInPolyTime.bitsRowWithInput
    (ComputableInPolyTime.unary_mul.comp (hcount.prod hseed))
    (ComputableInPolyTime.const 0) (ComputableInPolyTime.bitsFlatten hseedWords)
  have hfirstHash := LinearHash.computableInPolyTime_wordHash hobservation hfirst hobservations
  have hmiddleHash := LinearHash.computableInPolyTime_wordHash hlabel hmiddle hlabels
  have hlastHash := LinearHash.computableInPolyTime_wordHash hremaining hlast hseeds
  have h := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hfirst hfirstHash)
      (ComputableInPolyTime.bitsAppend hmiddle hmiddleHash))
    (ComputableInPolyTime.bitsAppend hlast hlastHash)
  simpa only [hashSamples, List.map_map, Function.comp_def] using h

attribute [program_certificate] isPolyTime_hashSamples

/-- Evaluate from one seed: sampler coins, remaining-seed matrix, label matrix, observation matrix.
Parsing is total even on short input tapes; exact sampling laws use `seedLength` input bits. -/
def generate (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (evaluate : List Bool → List Bool × Bool) (tape : List Bool) : List Bool :=
  let coins := tape.take (count * seedBits)
  let tape := tape.drop (count * seedBits)
  let lastKey := tape.take (remainingBits * (count * seedBits))
  let tape := tape.drop (remainingBits * (count * seedBits))
  let middleKey := tape.take (labelBits * count)
  let firstKey := tape.drop (labelBits * count)
  let samples := (listRows count seedBits coins).map (fun seed => (evaluate seed, seed))
  hashSamples count seedBits bound observationBits labelBits remainingBits samples
    firstKey middleKey lastKey

/-- Runtime dimensions, parsing, and every evaluator call are charged through ordinary
polynomial-time combinators. The callback may capture the original input. -/
theorem isPolyTime_generate {α : Type} {input : α ↪ List Bool}
    {count seedBits bound observationBits labelBits remainingBits : α → ℕ}
    {evaluate : α → List Bool → List Bool × Bool} {tape : α → (List Bool)}
    (hcount : ComputableInPolyTime count input encUnary)
    (hseed : ComputableInPolyTime seedBits input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hobservation : ComputableInPolyTime observationBits input encUnary)
    (hlabel : ComputableInPolyTime labelBits input encUnary)
    (hremaining : ComputableInPolyTime remainingBits input encUnary)
    (hevaluate : ComputableInPolyTime (fun a => evaluate a.1 a.2)
      (encPair input encBits) (encPair encBits encBool))
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => generate (count a) (seedBits a) (bound a)
      (observationBits a) (labelBits a) (remainingBits a) (evaluate a) (tape a)) input encBits := by
  have hcb := ComputableInPolyTime.unary_mul' hcount hseed
  have hcoins := ComputableInPolyTime.bitsTakeWithInput htape hcb
  have htape1 := ComputableInPolyTime.bitsDropWithInput htape hcb
  have hrk := ComputableInPolyTime.unary_mul' hremaining hcb
  have hlastKey := ComputableInPolyTime.bitsTakeWithInput htape1 hrk
  have htape2 := ComputableInPolyTime.bitsDropWithInput htape1 hrk
  have hlc := ComputableInPolyTime.unary_mul' hlabel hcount
  have hmiddleKey := ComputableInPolyTime.bitsTakeWithInput htape2 hlc
  have hfirstKey := ComputableInPolyTime.bitsDropWithInput htape2 hlc
  have hrows := ComputableInPolyTime.bitsRowsWithInput hcount hseed hcoins
  have hsamples := ComputableInPolyTime.mapWithInput
    (f := fun a seed => (evaluate a seed, seed)) hrows
    (hevaluate.prod (ComputableInPolyTime.snd input encBits))
  unfold generate
  exact isPolyTime_hashSamples hcount hseed hbound hobservation hlabel hremaining
    hsamples hfirstKey hmiddleKey hlastKey

attribute [program_certificate] isPolyTime_generate

/-- Uniform input bits supply independent sampler coins and matrix seeds, with no padding
coins added by an execution clock. -/
theorem generate_distribution (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (evaluate : List Bool → List Bool × Bool) :
    (uniformList (seedLength count seedBits bound observationBits labelBits remainingBits)).map
        (generate count seedBits bound observationBits labelBits remainingBits evaluate) =
      (do
        let coins ← uniformList (count * seedBits)
        let lastKey ← uniformList (remainingBits * (count * seedBits))
        let middleKey ← uniformList (labelBits * count)
        (uniformList (observationBits * (count * (2 * bound + 1)))).map fun firstKey =>
          hashSamples count seedBits bound observationBits labelBits remainingBits
            ((listRows count seedBits coins).map (fun seed => (evaluate seed, seed)))
            firstKey middleKey lastKey) := by
  unfold seedLength
  let run (coins lastKey middleKey firstKey : List Bool) :=
    hashSamples count seedBits bound observationBits labelBits remainingBits
      ((listRows count seedBits coins).map (fun seed => (evaluate seed, seed)))
      firstKey middleKey lastKey
  change (uniformList _).bind (fun tape => PMF.pure
    (run (tape.take (count * seedBits))
      ((tape.drop (count * seedBits)).take (remainingBits * (count * seedBits)))
      (((tape.drop (count * seedBits)).drop (remainingBits * (count * seedBits))).take
        (labelBits * count))
      (((tape.drop (count * seedBits)).drop (remainingBits * (count * seedBits))).drop
        (labelBits * count)))) = _
  rw [uniformList_bind_split (count * seedBits) _ (fun coins tape => PMF.pure
    (run coins (tape.take (remainingBits * (count * seedBits)))
      ((tape.drop (remainingBits * (count * seedBits))).take (labelBits * count))
      ((tape.drop (remainingBits * (count * seedBits))).drop (labelBits * count))))]
  congr 1
  funext coins
  rw [uniformList_bind_split (remainingBits * (count * seedBits)) _
    (fun lastKey tape => PMF.pure
      (run coins lastKey (tape.take (labelBits * count)) (tape.drop (labelBits * count))))]
  congr 1
  funext lastKey
  exact uniformList_bind_split (labelBits * count) _
    (fun middleKey firstKey => PMF.pure (run coins lastKey middleKey firstKey))

/-- Supplying independent uniform keys to the deterministic hash core realizes the three
probabilistic hashing calls exactly. Only the observation padding requires a size bound. -/
theorem eval_hashSamples (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (samples : List ((List Bool × Bool) × List Bool)) (hcount : samples.length = count)
    (hbound : ∀ sample ∈ samples, sample.1.1.length ≤ bound) :
    ProbComp.eval (do
      let third ← extractWordSeeds count seedBits remainingBits samples
      let middle ← extractWordLabels count labelBits third.1
      let front ← finish bound observationBits middle
      return front ++ (third.2.1 ++ third.2.2)) =
      (do
        let lastKey ← uniformList (remainingBits * (count * seedBits))
        let middleKey ← uniformList (labelBits * count)
        (uniformList (observationBits * (count * (2 * bound + 1)))).map fun firstKey =>
          hashSamples count seedBits bound observationBits labelBits remainingBits samples
            firstKey middleKey lastKey) := by
  have hfits : ∀ observation ∈ samples.map (fun sample => sample.1.1),
      observation.length ≤ bound := by
    intro observation hobservation
    obtain ⟨sample, hsample, rfl⟩ := List.mem_map.mp hobservation
    exact hbound sample hsample
  have hlength := length_flatten_padWord bound _ hfits
  simp only [List.length_map, hcount, List.map_map, Function.comp_def] at hlength
  simp only [ProbComp.eval_bind, extractWordSeeds, extractWordLabels, extractMatrixLabels,
    extractLabels, finish, extractWordObservations, LinearHash.extract,
    ProbComp.eval_pure, BitString.eval_sampleList, hashSamples, List.map_map, Function.comp_def,
    hlength, PMF.pure_bind, PMF.map, PMF.bind_bind, id_eq]
  rfl

/-- A uniform seed of exactly `seedLength` bits realizes the complete sampled extractor.
The only size premise is the observation bound on correctly sized sampler seeds. -/
theorem eval_generate (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (evaluate : List Bool → List Bool × Bool)
    (hbound : ∀ seed, seed.length = seedBits → (evaluate seed).1.length ≤ bound) :
    (uniformList (seedLength count seedBits bound observationBits labelBits remainingBits)).map
        (generate count seedBits bound observationBits labelBits remainingBits evaluate) =
      ProbComp.eval (extract count seedBits bound observationBits labelBits remainingBits (do
        let seed ← BitString.sampleList seedBits
        return (evaluate seed, seed))) := by
  rw [generate_distribution, extract, ProbComp.eval_bind,
    ProbComp.eval_replicate_of_uniformList count seedBits _ (fun seed => (evaluate seed, seed))
      (by simp only [bind_pure_comp, ProbComp.eval_map, BitString.eval_sampleList])]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  funext coins
  symm
  apply eval_hashSamples
  · simp only [List.length_map, length_listRows]
  · intro sample hsample
    obtain ⟨seed, hseed, rfl⟩ := List.mem_map.mp hsample
    exact hbound seed (length_of_mem_listRows hseed)

/-- Every correctly sized seed produces the advertised fixed output length. -/
theorem length_generate (count seedBits bound observationBits labelBits remainingBits : ℕ)
    (evaluate : List Bool → List Bool × Bool)
    (hbound : ∀ seed, seed.length = seedBits → (evaluate seed).1.length ≤ bound)
    {tape : List Bool}
    (htape : tape.length =
      seedLength count seedBits bound observationBits labelBits remainingBits) :
    (generate count seedBits bound observationBits labelBits remainingBits evaluate tape).length =
      outputLength count seedBits bound observationBits labelBits remainingBits := by
  apply length_extract count seedBits bound observationBits labelBits remainingBits
    (do
      let seed ← BitString.sampleList seedBits
      return (evaluate seed, seed))
  · intro sample hsample
    simp only [bind_pure_comp, ProbComp.eval_map, BitString.eval_sampleList,
      PMF.mem_support_map_iff] at hsample
    obtain ⟨seed, hseed, rfl⟩ := hsample
    exact hbound seed (mem_support_uniformList_iff.mp hseed)
  · rw [← eval_generate count seedBits bound observationBits labelBits remainingBits
      evaluate hbound]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨tape, mem_support_uniformList_iff.mpr htape, rfl⟩

/-- The sampler's saved-seed evaluator implements the exact ensemble in the security theorem.
The observation bound only concerns outcomes in the support of the finite pair. -/
theorem eval_generate_of_realization {pair : SamplablePair} (saved : pair.SeedRealization)
    (n count bound observationBits labelBits remainingBits : ℕ)
    (hbound : ∀ observation ∈ ((pair.joint n).map Prod.fst).support,
      (pair.encode n observation).length ≤ bound) :
    (uniformList (seedLength count (saved.length n) bound
        observationBits labelBits remainingBits)).map
        (generate count (saved.length n) bound observationBits labelBits remainingBits
          (saved.evaluate n)) =
      ProbComp.eval (extract count (saved.length n) bound observationBits labelBits remainingBits
        (saved.sampleWithSeed n)) :=
  eval_generate count (saved.length n) bound observationBits labelBits remainingBits
    (saved.evaluate n) (fun _ h => saved.observation_length_le n bound hbound h)

end Cslib.Crypto.Pseudoentropy.ThreeSource
