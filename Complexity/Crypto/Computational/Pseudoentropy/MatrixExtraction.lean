/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.RepeatedExtraction
public import Complexity.Languages.Probabilistic.LinearHash
import Complexity.Computability.Probabilistic.LinearHash
import Complexity.Tactic.PPT

/-!
# Repeated extraction with an executable matrix hash

The three extractors in the pseudoentropy construction share this program. A client prepares
the label list as one word; the extractor supplies a fresh matrix, hashes at the declared width,
and retains every observation and the complete matrix seed. Width normalization specifies total
behavior on malformed inputs without affecting the finite extraction laws.

## Main definitions

* `extractMatrixLabels`: retain observations while hashing normalized labels with a fresh matrix.
* `extractMatrixLabelsIdeal`: the independent comparison program with the same public seed.

## Main results

* `isPPTOn_extractMatrixLabels`: certify sampling, hashing and copying at runtime dimensions.
* `eval_extractMatrixLabels`: the exact finite matrix experiment.
* `eval_extractMatrixLabelsIdeal_append`: combine the ideal seed and digest after any processing
  of the public observations.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5.
  [Holenstein2006].
  We use the shared Boolean-matrix family in place of finite-field hashing.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability BitString Turing.MultiTapeTM

/-- Hash prepared labels with a fresh matrix, retaining the observations and full seed. -/
noncomputable def extractMatrixLabels {Observation Label : Type} (inputBits outputBits : ℕ)
    (prepare : List Label → List Bool) (samples : List (Observation × Label)) :
    ProbComp (List Observation × List Bool × List Bool) :=
  extractLabels (BitString.sampleList (outputBits * inputBits))
    (fun seed labels => LinearHash.wordHash outputBits seed
      (listRow inputBits 0 (prepare labels))) samples

/-- Every result preserves the observations and has the declared seed and digest lengths. -/
theorem extractMatrixLabels_result {Observation Label : Type} (inputBits outputBits : ℕ)
    (prepare : List Label → List Bool) (samples : List (Observation × Label))
    {result : List Observation × List Bool × List Bool}
    (hresult : result ∈ (ProbComp.eval
      (extractMatrixLabels inputBits outputBits prepare samples)).support) :
    result.1 = samples.map Prod.fst ∧ result.2.1.length = outputBits * inputBits ∧
      result.2.2.length = outputBits := by
  simp only [extractMatrixLabels, extractLabels, bind_pure_comp, ProbComp.eval_map,
    BitString.eval_sampleList, PMF.mem_support_map_iff] at hresult
  obtain ⟨seed, hseed, rfl⟩ := hresult
  exact ⟨rfl, mem_support_uniformList_iff.mp hseed, LinearHash.length_wordHash _ _ _⟩

/-- The comparison experiment preserves the observations and samples independent seed and bits. -/
noncomputable def extractMatrixLabelsIdeal {Observation : Type} (source : ProbComp Observation)
    (count inputBits outputBits : ℕ) : ProbComp (List Observation × List Bool × List Bool) := do
  let observations ← OracleComp.replicate count source
  let seed ← BitString.sampleList (outputBits * inputBits)
  let bits ← BitString.sampleList outputBits
  return (observations, seed, bits)

/-- Runtime dimensions and a certified preparation function give an ordinary PPT program. -/
theorem isPPTOn_extractMatrixLabels {α Observation Label : Type} {input : α ↪ List Bool}
    {observation : Observation ↪ List Bool} {label : Label ↪ List Bool}
    {inputBits outputBits : α → ℕ} {prepare : α → List Label → List Bool}
    {samples : α → List (Observation × Label)}
    (hinput : ComputableInPolyTime inputBits input encUnary)
    (houtput : ComputableInPolyTime outputBits input encUnary)
    (hprepare : ComputableInPolyTime (fun pair => prepare pair.1 pair.2)
      (encPair input (encList label)) encBits)
    (hsamples : ComputableInPolyTime samples input
      (encList (encPair observation label))) :
    IsPPTOn input
      (encPair (encList observation) (encPair encBits encBits))
      (fun a => extractMatrixLabels (inputBits a) (outputBits a) (prepare a) (samples a)) := by
  unfold extractMatrixLabels
  ppt

attribute [program_certificate hsamples] isPPTOn_extractMatrixLabels

/-- Word matrix sampling and hashing exactly realize the finite extraction experiment. -/
theorem eval_extractMatrixLabels {Observation Label : Type} (inputBits outputBits : ℕ)
    (prepare : List Label → List Bool) (samples : List (Observation × Label)) :
    ProbComp.eval (extractMatrixLabels inputBits outputBits prepare samples) =
      (ProbComp.eval (extractLabels (ProbComp.uniform (BitString (outputBits * inputBits)))
        (fun seed labels => LinearHash.hash (blocksEquiv (m := outputBits) (k := inputBits) seed)
          (ofList inputBits (prepare labels))) samples)).map
            (fun result => (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  have hrow (word : List Bool) : listRow inputBits 0 word =
      List.ofFn (ofList inputBits word) :=
    listRow_eq_ofFn inputBits (0 : Fin 1) word
  simp only [extractMatrixLabels, extractLabels, bind_pure_comp, ProbComp.eval_map,
    ProbComp.eval_uniform, eval_sampleList, uniformList, PMF.map_comp, Function.comp_def,
    hrow, LinearHash.wordHash_eq_ofFn, ofList_ofFn, blocksEquiv_apply]

/-- The ideal word program agrees with the finite ideal distribution, retaining the full seed. -/
theorem eval_extractMatrixLabelsIdeal {Observation : Type} (source : ProbComp Observation)
    (count inputBits outputBits : ℕ) :
    ProbComp.eval (extractMatrixLabelsIdeal source count inputBits outputBits) =
      (extractLabelsIdeal (Output := BitString outputBits) source count
        (ProbComp.uniform (BitString (outputBits * inputBits)))).map
          (fun result => (result.1, List.ofFn result.2.1, List.ofFn result.2.2)) := by
  simp only [extractMatrixLabelsIdeal, ProbComp.eval_bind, ProbComp.eval_pure,
    extractLabelsIdeal, ProbComp.eval_uniform, eval_sampleList, uniformList,
    Function.comp_def, PMF.map, PMF.bind_bind, PMF.pure_bind]
  simp only [PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.pure_bind]

/-- In the ideal experiment, the public matrix seed and digest together form one uniform word.
The continuation may depend on all retained observations. -/
theorem eval_extractMatrixLabelsIdeal_bind {Observation Output : Type}
    (source : ProbComp Observation) (count inputBits outputBits : ℕ)
    (next : List Observation → List Bool → ProbComp Output) :
    ProbComp.eval (do
      let result ← extractMatrixLabelsIdeal source count inputBits outputBits
      next result.1 (result.2.1 ++ result.2.2)) =
        ProbComp.eval (do
          let observations ← OracleComp.replicate count source
          let bits ← BitString.sampleList (outputBits * inputBits + outputBits)
          next observations bits) := by
  simp only [extractMatrixLabelsIdeal, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList]
  rw [uniformList_add]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.pure_bind, Function.comp_def]

/-- An independently uniform ideal hash can be sampled after processing the observations. -/
theorem eval_extractMatrixLabelsIdeal_append {Observation : Type}
    (source : ProbComp Observation) (count inputBits outputBits : ℕ)
    (next : List Observation → ProbComp (List Bool)) :
    ProbComp.eval (do
      let result ← extractMatrixLabelsIdeal source count inputBits outputBits
      (fun front => front ++ (result.2.1 ++ result.2.2)) <$> next result.1) =
        ProbComp.eval (do
          let observations ← OracleComp.replicate count source
          let front ← next observations
          let suffix ← BitString.sampleList (outputBits * inputBits + outputBits)
          return front ++ suffix) := by
  rw [eval_extractMatrixLabelsIdeal_bind source count inputBits outputBits
    (fun observations suffix => (fun front => front ++ suffix) <$> next observations)]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    BitString.eval_sampleList]
  congr 1
  funext observations
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm]

end Cslib.Crypto.Pseudoentropy
