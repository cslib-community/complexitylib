/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Crypto.Computational.Pseudoentropy.Basic
public import Complexity.Languages.Probabilistic.BitString
public import Complexity.Probability.EntropyConcentration
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# Uniform seeds for samplable pseudoentropy pairs

Every strict PPT sampler admits one polynomial-time deterministic evaluator driven by a uniform
polynomial-length seed. `SeedRealization` exposes this algorithm while preserving the pair's exact
finite joint law. Its `output` is the finite mathematical view used for entropy accounting.

The entropy chain rule accounts for every seed bit, including coins unused by the sampler:
`H(observation) + H(bit | observation) + H(seed | observation, bit) = seed length`.
Thus the third source in the later extraction argument retains the unused randomness too.
The seed also bounds the information in a single outcome, giving an explicit exponential
concentration bound for independent repetitions of the pair.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization`: a uniformly efficient evaluator
  with the exact joint law on uniform seeds.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.sampleWithSeed`: return the evaluated
  pair together with every seed bit, including unused coins.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.latentSampleWithSeed`: the exact
  finite mathematical view, with no claim that observation decoding is efficient.

## Main results

* `Cslib.Crypto.Pseudoentropy.SamplablePair.exists_seedRealization`: the sampler's existing strict
  PPT certificate supplies its deterministic evaluator.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.isPPTOn_sampleWithSeed`: sampling with
  retained seed bits is strict PPT.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.SeedRealization.entropy_chain_rule`: account for the
  entire seed's entropy.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Definition 4 and Section 5.
  Shared machine replay supplies the uniform-seed presentation; the bounded-information
  concentration estimate depends on the complete seed length.

Adapted from Crypto/Computational/Pseudoentropy/Seed.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing typed saved-coin evaluator and tidy
machine certificates. Positive pseudoentropy gaps and extraction remain separate developments.

-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.SamplablePair

open Probability Turing.MultiTapeTM

/-- A sampler's PPT certificate supplies an efficiently computed bound on every possible
public observation. Impossible values in its finite observation type need no size bound. -/
theorem exists_observationBound (pair : SamplablePair) :
    ∃ bound : ℕ → ℕ, ComputableInPolyTime bound encUnary encUnary ∧
      ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
        (pair.encode n observation).length ≤ bound n := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  have hsample : IsPPTOn encUnary encBits (fun n => Prod.fst <$> pair.sample n) := by
    have hefficient := pair.efficient
    ppt
  obtain ⟨c, d, hbound⟩ := hsample.length_le
  refine ⟨fun n => c * (n + 1) ^ d, by polytime, ?_⟩
  intro n observation hobservation
  have hsupported : pair.encode n observation ∈ (ProbComp.eval
      (Prod.fst <$> pair.sample n)).support := by
    obtain ⟨result, hresult, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hobservation
    simp only [ProbComp.eval_map, pair.eval_sample, PMF.map_comp, Function.comp_def]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, hresult, rfl⟩
  simpa only [encBits, Function.Embedding.refl_apply, encUnary_apply, List.length_replicate] using
    hbound n (pair.encode n observation) hsupported

/-- A plain polynomial-time evaluator from a uniform seed, with all input bits counted. -/
structure SeedRealization (pair : SamplablePair) where
  /-- The complete number of seed bits at this parameter. -/
  length : ℕ → ℕ
  /-- The seed length is efficiently available in unary. -/
  length_isPolyTime : ComputableInPolyTime length encUnary encUnary
  /-- Evaluate the public observation and hidden bit from a saved seed. -/
  evaluate : ℕ → List Bool → List Bool × Bool
  /-- Evaluation is one polynomial-time word program, also on malformed seeds. -/
  efficient : ComputableInPolyTime (fun input : ℕ × List Bool => evaluate input.1 input.2)
    (encPair encUnary encBits) (encPair encBits encBool)
  /-- Uniform seeds realize exactly the original finite joint law. -/
  distribution : ∀ n, (BitString.uniformList (length n)).map (evaluate n) =
    (pair.joint n).map (fun output => (pair.encode n output.1, output.2))

/-- A strict PPT sampler supplies an efficient uniform-seed realization with no additional
computability or sampling assumption. -/
theorem exists_seedRealization (pair : SamplablePair) : Nonempty (SeedRealization pair) := by
  obtain ⟨c, d, evaluate, hefficient, hrealize⟩ := pair.efficient.exists_seeded_evaluator
  refine ⟨{ length := fun n => c * (n + 1) ^ d
            length_isPolyTime := by polytime
            evaluate := evaluate
            efficient := .of_tidy hefficient
            distribution := ?_ }⟩
  intro n
  rw [← pair.eval_sample]
  symm
  simpa only [encUnary_apply, List.length_replicate] using hrealize n

namespace SeedRealization

variable {pair : SamplablePair} (seed : SeedRealization pair)

/-- Every well-formed seed produces an outcome in the support of the original finite law. -/
theorem exists_supported_output (n : ℕ) {word : List Bool} (hlength : word.length = seed.length n) :
    ∃ output ∈ (pair.joint n).support,
      (pair.encode n output.1, output.2) = seed.evaluate n word := by
  have hs : seed.evaluate n word ∈
      ((BitString.uniformList (seed.length n)).map (seed.evaluate n)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr
      ⟨word, BitString.mem_support_uniformList_iff.mpr hlength, rfl⟩
  rw [seed.distribution] at hs
  exact (PMF.mem_support_map_iff _ _ _).mp hs

/-- Every well-formed seed produces an encoded observation and bit in the original finite law. -/
theorem exists_output (n : ℕ) (bits : Fin (seed.length n) → Bool) :
    ∃ output : pair.Observation n × Bool,
      (pair.encode n output.1, output.2) = seed.evaluate n (List.ofFn bits) := by
  obtain ⟨output, _, houtput⟩ := seed.exists_supported_output n List.length_ofFn
  exact ⟨output, houtput⟩

/-- A bound on supported observations also bounds the evaluator on every correctly sized seed. -/
theorem observation_length_le (n bound : ℕ)
    (hbound : ∀ observation ∈ ((pair.joint n).map Prod.fst).support,
      (pair.encode n observation).length ≤ bound)
    {word : List Bool} (hlength : word.length = seed.length n) :
    (seed.evaluate n word).1.length ≤ bound := by
  obtain ⟨output, houtput, heq⟩ := seed.exists_supported_output n hlength
  rw [← heq]
  exact hbound output.1 ((PMF.mem_support_map_iff _ _ _).mpr ⟨output, houtput, rfl⟩)

/-- The evaluator's finite mathematical output on a well-formed seed. No search over observations
is run: its word representation is exactly the efficient evaluator's output. -/
noncomputable def output (n : ℕ) (bits : Fin (seed.length n) → Bool) : pair.Observation n × Bool :=
  (exists_output seed n bits).choose

/-- The finite view preserves the evaluator's complete output, including the hidden bit. -/
theorem encode_output (n : ℕ) (bits : Fin (seed.length n) → Bool) :
    (pair.encode n (seed.output n bits).1, (seed.output n bits).2) =
      seed.evaluate n (List.ofFn bits) := (exists_output seed n bits).choose_spec

/-- The uniform finite-seed presentation has the original joint law. -/
theorem output_distribution (n : ℕ) :
    (PMF.uniformOfFintype (Fin (seed.length n) → Bool)).map (seed.output n) = pair.joint n := by
  apply PMF.map_injective (f := fun output : pair.Observation n × Bool =>
    (pair.encode n output.1, output.2))
    ((pair.encode n).injective.prodMap Function.injective_id)
  rw [PMF.map_comp]
  simpa only [BitString.uniformList, PMF.map_comp, Function.comp_def, seed.encode_output] using
    seed.distribution n

/-- Retain the complete sampler seed together with its finite output. -/
noncomputable def jointWithSeed (n : ℕ) :
    PMF ((pair.Observation n × Bool) × (Fin (seed.length n) → Bool)) :=
  (PMF.uniformOfFintype (Fin (seed.length n) → Bool)).map (fun bits => (seed.output n bits, bits))

/-- Sample the finite mathematical view and retain every original seed bit. This relabelling
has no efficiency claim; `sampleWithSeed` below is its efficient encoded realization. -/
noncomputable def latentSampleWithSeed (n : ℕ) :
    ProbComp ((pair.Observation n × Bool) × (Fin (seed.length n) → Bool)) :=
  (fun bits => (seed.output n bits, bits)) <$> ProbComp.uniform (Fin (seed.length n) → Bool)

/-- Finite uniform sampling realizes the complete latent output/seed law. -/
theorem eval_latentSampleWithSeed (n : ℕ) :
    ProbComp.eval (seed.latentSampleWithSeed n) = seed.jointWithSeed n := by
  simp only [latentSampleWithSeed, jointWithSeed, ProbComp.eval_map, ProbComp.eval_uniform]

/-- Forgetting the retained seed recovers the pair's original joint law. -/
@[simp] theorem jointWithSeed_map_fst (n : ℕ) :
    (seed.jointWithSeed n).map Prod.fst = pair.joint n := by
  simpa only [jointWithSeed, PMF.map_comp, Function.comp_def] using seed.output_distribution n

/-- Keeping the seed retains its full pointwise information bound. -/
theorem jointWithSeed_mass_ge (n : ℕ) (result)
    (hresult : result ∈ (seed.jointWithSeed n).support) :
    (2 : ℝ) ^ (-(seed.length n : ℝ)) ≤ (seed.jointWithSeed n result).toReal := by
  simpa [jointWithSeed, Fintype.card_fun, Real.logb_pow] using
    PMF.uniform_map_mass_ge (fun bits => (seed.output n bits, bits)) result hresult

/-- An ordinary program returns the observation, label, and complete seed, including unused
coins. The evaluator is the same deterministic program supplied by the sampler's certificate. -/
noncomputable def sampleWithSeed (n : ℕ) : ProbComp ((List Bool × Bool) × List Bool) := do
  let bits ← BitString.sampleList (seed.length n)
  return (seed.evaluate n bits, bits)

/-- Retaining the seed preserves strict PPT; no conditional sampling is performed. -/
@[program_certificate]
theorem isPPTOn_sampleWithSeed : IsPPTOn encUnary
    (encPair (encPair encBits encBool) encBits) seed.sampleWithSeed := by
  have hlength := seed.length_isPolyTime
  have hevaluate := seed.efficient
  unfold sampleWithSeed
  ppt

/-- The efficient program exactly realizes the finite joint experiment with its retained seed. -/
theorem eval_sampleWithSeed (n : ℕ) : ProbComp.eval (seed.sampleWithSeed n) =
    (seed.jointWithSeed n).map (fun result =>
      ((pair.encode n result.1.1, result.1.2), List.ofFn result.2)) := by
  simp only [sampleWithSeed, bind_pure_comp, ProbComp.eval_map, jointWithSeed, PMF.map_comp,
    Function.comp_def, seed.encode_output]
  simp only [BitString.eval_sampleList, BitString.uniformList, PMF.map_comp, Function.comp_def]

/-- Every possible output has at least the probability of one complete seed. -/
theorem mass_ge (n : ℕ) (result : pair.Observation n × Bool)
    (hresult : result ∈ (pair.joint n).support) :
    (2 : ℝ) ^ (-(seed.length n : ℝ)) ≤ (pair.joint n result).toReal := by
  rw [← seed.output_distribution] at hresult ⊢
  simpa [Fintype.card_fun, Real.logb_pow] using
    PMF.uniform_map_mass_ge (seed.output n) result hresult

/-- Independent repetitions concentrate their conditional information around the Shannon
entropy of the pair. The loss accounts for the sampler's full saved seed length. -/
theorem conditionalSurprisal_concentration (n repetitions : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((PMF.pi (fun _ : Fin repetitions => pair.joint n)).toOuterMeasure {outcomes |
      ∑ i, PMF.surprisal (PMF.conditionalSnd (pair.joint n) (outcomes i).1) (outcomes i).2 ≤
        repetitions * PMF.conditionalEntropy (pair.joint n) - ε}).toReal ≤
      Real.exp (-2 * ε ^ 2 / (repetitions * (seed.length n : ℝ) ^ 2)) := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    PMF.pi_sum_conditionalSurprisal_le (fun _ : Fin repetitions => pair.joint n)
      (Nat.cast_nonneg (seed.length n)) (fun _ => seed.mass_ge n) hε

/-- Revealing the observation and hidden bit leaves exactly the remaining seed entropy.
This identity also counts coins that the sampler never inspected. -/
theorem entropy_chain_rule (n : ℕ) :
    PMF.entropy ((pair.joint n).map Prod.fst) + PMF.conditionalEntropy (pair.joint n) +
      PMF.conditionalEntropy (seed.jointWithSeed n) = seed.length n := by
  simp only [PMF.conditionalEntropy, seed.jointWithSeed_map_fst, add_sub_cancel]
  rw [jointWithSeed, PMF.entropy_map_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  simp [PMF.entropy_uniform, Real.logb_pow]

end SeedRealization

end Cslib.Crypto.Pseudoentropy.SamplablePair
