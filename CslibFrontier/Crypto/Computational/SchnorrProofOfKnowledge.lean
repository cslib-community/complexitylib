/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProtocol
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.ProofOfKnowledge

/-!
# Schnorr's protocol is a proof of knowledge of discrete logarithms

Schnorr's Sigma protocol `schnorrFamily` ([BonehShoup2023]), indexed by a unary security
parameter `n` and a group description `d`, is a proof of knowledge of the discrete logarithm of
the statement `u`. The knowledge extractor `schnorrKnowledgeExtractor A` is the generic rewinding
extractor of `CslibFrontier.Crypto.Protocols.SigmaProtocol.ProofOfKnowledge` for a prover `A` on
words. It draws its two challenges with the fair-coin sampler `schnorrSampleChallenge` and computes
`(c - c')⁻¹ (z - z')` modulo the group order `q` with `schnorrExtractWord`.

* **Efficiency** (`isPPTOn_schnorrKnowledgeExtractor`): the extractor is uniform strict PPT
  whenever `A` is. There is no other hypothesis.
* **Extraction** (`le_add_sqrt_schnorrExtractionGame`): for every group description and every
  statement `u`, not only on average over generated keys, the honest verifier's acceptance
  probability `ε` of `A` and the probability `ε'` that the extractor outputs the binary encoding of
  the discrete logarithm of `u` satisfy

    `ε ≤ 1 / q + 2 / 2 ^ n + √ε'`.

  The term `2 / 2 ^ n` comes from the challenge sampler, which is within statistical distance
  `1 / 2 ^ n` of uniform on `ZMod q`.

Combined with a discrete-logarithm assumption, this is the extraction step behind the security of
Schnorr identification; `CslibFrontier.Crypto.Computational.SchnorrIdentification` proves that
security with `k`-bit challenges.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrKnowledgeExtractor`: the rewinding knowledge
  extractor.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_schnorrKnowledgeExtractor`: it is uniform strict PPT.
* `Cslib.Crypto.PrimeOrderGroupFamily.le_add_sqrt_schnorrExtractionGame`:
  `ε ≤ 1 / q + 2 / 2 ^ n + √ε'` on every statement.

## References

* [M. Bellare, O. Goldreich, *On Defining Proofs of Knowledge*][BellareGoldreich1992]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023]
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols Protocols.SigmaProtocol
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-- The rewinding knowledge extractor for Schnorr's protocol: run the prover `A` to its
commitment, answer two challenges sampled by `schnorrSampleChallenge` from the same state, and
apply `schnorrExtractWord` to the two conversations. -/
noncomputable def schnorrKnowledgeExtractor (A : MaliciousProver (ℕ × F.Desc)) :
    (ℕ × F.Desc) × List Bool → ProbComp (List Bool) :=
  knowledgeExtractor F.schnorrEncoding F.schnorrSampleChallenge F.schnorrExtractWord A

/-- **Schnorr's knowledge extractor is uniform strict PPT** whenever the prover is. -/
theorem isPPTOn_schnorrKnowledgeExtractor {A : MaliciousProver (ℕ × F.Desc)}
    (hA : A.IsPPT (encPair encUnary F.encDesc)) :
    IsPPTOn (encPair (encPair encUnary F.encDesc) encBits) encBits
      (F.schnorrKnowledgeExtractor A) :=
  isPPTOn_knowledgeExtractor F.isPPTOn_schnorrSampleChallenge
    F.computableInPolyTime_schnorrExtractWord hA

/-- **Schnorr's protocol is a proof of knowledge of discrete logarithms.** At the security
parameter `n`, in the group described by `d` of order `q`, and on every statement `u`, if the
prover `A` convinces the honest verifier with probability `ε`, the knowledge extractor outputs the
binary encoding of the discrete logarithm of `u` with probability `ε'` such that
`ε ≤ 1 / q + 2 / 2 ^ n + √ε'`. -/
theorem le_add_sqrt_schnorrExtractionGame (A : MaliciousProver (ℕ × F.Desc)) (n : ℕ)
    (d : F.Desc) (u : F.Carrier d) :
    (Game.succProbability (acceptanceGame F.schnorrFamily F.schnorrEncoding A (n, d) u
        (PMF.uniformOfFintype (ZMod (F.order d)))) : ℝ) ≤
      1 / F.order d + 2 / 2 ^ n +
        √(Game.succProbability (extractionGame F.schnorrEncoding (fun i => F.encScalar i.2)
          (fun i α u => α • F.generator i.2 = u) (F.schnorrKnowledgeExtractor A) (n, d) u)) := by
  have h := le_add_sqrt_extractionGame F.efficientSpecialSoundness_schnorr.specialSoundness
    F.extractorRealizedBy_schnorrExtractWord A (n, d) u (F.closeTo_schnorrSampleChallenge (n, d))
  simp only [ZMod.card, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat] at h
  refine h.trans_eq ?_
  rw [schnorrKnowledgeExtractor]
  ring

end Cslib.Crypto.PrimeOrderGroupFamily
