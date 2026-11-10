/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Probability.BitString.LinearHash

/-!
# Extracting with a sampled linear hash

The extractor samples a fresh Boolean matrix and returns its complete seed followed by the
digest. Its exact law is the finite strong-extraction experiment. Arbitrary randomized tests
of the word output satisfy the leftover-hash bound; tests may inspect both seed and digest and
need not be efficient. This uses the upstream finite-PMF distance without a competing metric
on the infinite type of lists. Uniform strict PPT is certified separately.

## Main definitions

* `Cslib.BitString.LinearHash.extract`: sample and reveal a matrix and its hash output.

## Main results

* `Cslib.BitString.LinearHash.eval_extract_bind`: the complete finite-to-list joint law.
* `Cslib.BitString.LinearHash.eval_extract_replicate`: extraction from concatenated repeated runs.
* `Cslib.BitString.LinearHash.extract_dist_bind_le`: leftover hashing for every randomized test
  with a finite result type, including arbitrary Boolean distinguishers.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 3.3, Lemma 1.
* [I. Haitner, S. Vadhan, *The Many Entropies in One-Way Functions*][HaitnerVadhan2017],
  Section 2.4.1, Definition 4 and Lemma 8.

Adapted from Languages/Probabilistic/LinearHash.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing block and finite-distance APIs.
-/

@[expose] public section

namespace Cslib.BitString.LinearHash

open Cslib.Probability Cslib.Probability.PMF

/-- Sample an independent hash matrix and return its seed followed by the extracted bits. -/
noncomputable def extract (count : ℕ) (input : List Bool) : ProbComp (List Bool) := do
  let seed ← sampleList (count * input.length)
  return seed ++ wordHash count seed input

/-- Every extractor output contains the complete matrix seed and exactly `count` digest bits. -/
theorem length_extract (count : ℕ) (input : List Bool) {output : List Bool}
    (houtput : output ∈ (ProbComp.eval (extract count input)).support) :
    output.length = count * input.length + count := by
  simp only [extract, bind_pure_comp, ProbComp.eval_map, eval_sampleList,
    PMF.mem_support_map_iff] at houtput
  obtain ⟨seed, hseed, rfl⟩ := houtput
  simp only [List.length_append, length_wordHash, mem_support_uniformList_iff.mp hseed]

/-- The word extractor agrees exactly with the finite strong-extraction experiment. -/
theorem eval_extract_bind {n m : ℕ} (source : PMF (BitString n)) :
    (source.map List.ofFn).bind (fun input => ProbComp.eval (extract m input)) =
      (seededHash (PMF.uniformOfFintype (BitString (m * n))) source
        (fun seed => hash (blocksEquiv (m := m) (k := n) seed))).map
          (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2) := by
  simp only [PMF.bind_map, Function.comp_def, extract, ProbComp.eval_bind,
    ProbComp.eval_pure, eval_sampleList, List.length_ofFn]
  simp only [uniformList, seededHash, PMF.map_bind, PMF.map_comp, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm]
  simp only [PMF.map, Function.comp_def,
    wordHash_eq_ofFn, ofList_ofFn, blocksEquiv_apply]

/-- The word extractor's exact finite law on one fixed-width input. -/
theorem eval_extract_ofFn {n m : ℕ} (input : BitString n) :
    ProbComp.eval (extract m (List.ofFn input)) =
      (PMF.uniformOfFintype (BitString (m * n))).map
        (fun seed => List.ofFn seed ++
          List.ofFn (hash (blocksEquiv (m := m) (k := n) seed) input)) := by
  simpa only [PMF.pure_map, PMF.pure_bind, seededHash_eq_bind, PMF.map_comp,
    Function.comp_def] using
    eval_extract_bind (m := m) (PMF.pure input)

/-- Hashing concatenated independent fixed-width words has the tuple extraction law. -/
theorem eval_extract_replicate {width : ℕ} (source : ProbComp (BitString width))
    (count outputBits : ℕ) :
    ProbComp.eval (do
      let words ← OracleComp.replicate count (List.ofFn <$> source)
      extract outputBits words.flatten) =
        (seededHash (PMF.uniformOfFintype (BitString (outputBits * (count * width))))
          (ProbComp.eval (OracleComp.replicate count source))
          (fun seed values => hash (blocksEquiv (m := outputBits) (k := count * width) seed)
            (ofList (count * width) (values.map List.ofFn).flatten))).map
              (fun result => List.ofFn result.1 ++ List.ofFn result.2) := by
  simp only [OracleComp.replicate_map, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_replicate, PMF.bind_map, PMF.map_comp, PMF.map_bind,
    seededHash_eq_bind, Function.comp_def, List.map_ofFn, ← ofFn_blocksEquiv_symm,
    ofList_ofFn, eval_extract_ofFn]

/-- Every randomized finite-output test of the complete word output satisfies the strong
leftover-hash bound. The test has no computational restriction and sees the public seed. -/
theorem extract_dist_bind_le {n m : ℕ} (source : PMF (BitString n))
    {Result : Type*} [Fintype Result] (test : List Bool → PMF Result) :
    dist (((source.map List.ofFn).bind (fun input => ProbComp.eval (extract m input))).bind test)
        ((uniformList (m * n + m)).bind test) ≤
      Real.sqrt ((2 : ℝ) ^ m * collisionProbability source) / 2 := by
  have h := (isTwoUniversal_flat n m).leftover_hash source
  have hideal : ((PMF.uniformOfFintype (BitString (m * n))).bind
      (fun seed => (PMF.uniformOfFintype (BitString m)).map (seed, ·))).map
      (fun pair => List.ofFn pair.1 ++ List.ofFn pair.2) = uniformList (m * n + m) := by
    rw [uniformList_add]
    simp only [uniformList, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
  rw [eval_extract_bind, ← hideal]
  simp only [PMF.bind_map, Function.comp_def]
  exact (dist_bind_le _ _ _).trans (by simpa [BitString] using h)

end Cslib.BitString.LinearHash
