/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Sampling.BitString
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Efficient
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.ProofOfKnowledge

/-!
# Lyubashevsky identification is a proof of knowledge of short SIS solutions

Lyubashevsky's identification protocol `lyubashevskyFamily` ([Lyubashevsky2012]), indexed by its
parameters `p`, has `k`-bit challenges, and its special-soundness extractor returns a solution of
a relaxed SIS instance: a nonzero integer vector of infinity norm at most
`max (2 (γ - β)) 1` in the kernel of `[A | T]` (`efficientSpecialSoundness_lyubashevsky`). The
rewinding knowledge extractor `lyubashevskyKnowledgeExtractor A` of
`CslibFrontier.Crypto.Protocols.SigmaProtocol.ProofOfKnowledge` draws its two challenges uniformly
with `k` fair coins and applies `lyubashevskyExtractorAdapter`.

* **Efficiency** (`isPPTOn_lyubashevskyKnowledgeExtractor`): the extractor is uniform strict PPT
  whenever the prover `A` is.
* **Extraction** (`sq_sub_le_lyubashevskyExtractionGame`): for every parameter record `p` and
  every statement `(A, T)`, the honest verifier's acceptance probability `ε` of the prover and the
  probability `ε'` that the extractor outputs the encoding of a relaxed SIS solution satisfy
  `ε ^ 2 - ε / 2 ^ k ≤ ε'`.

The knowledge is of the relaxed relation: the extracted vector is a short kernel vector of
`[A | T]`, not the prover's secret `S` with `T = A S`.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySampleChallenge`: uniform `k`-bit challenges.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyKnowledgeExtractor`: the rewinding knowledge
  extractor.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.isPPTOn_lyubashevskySampleChallenge`,
  `Cslib.Crypto.Protocols.SigmaProtocol.isPPTOn_lyubashevskyKnowledgeExtractor`: the challenge
  sampler and the extractor are uniform strict PPT.
* `Cslib.Crypto.Protocols.SigmaProtocol.sq_sub_le_lyubashevskyExtractionGame`:
  `ε ^ 2 - ε / 2 ^ k ≤ ε'` on every statement.

## References

* [M. Bellare, O. Goldreich, *On Defining Proofs of Knowledge*][BellareGoldreich1992]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Turing.MultiTapeTM

/-- Uniform `k`-bit challenges for `lyubashevskyFamily p`. -/
noncomputable def lyubashevskySampleChallenge (p : LyubashevskyParams) :
    ProbComp (BitString p.k) :=
  ProbComp.uniform (BitString p.k)

/-- One machine samples the encoded challenges of `lyubashevskySampleChallenge` from the encoded
parameters, with `k` fair coins. -/
theorem isPPTOn_lyubashevskySampleChallenge :
    IsPPTOn encLyubashevskyParams encBits
      fun p => lyubashevskyEncoding.challenge p <$> lyubashevskySampleChallenge p :=
  ComputableInPolyTime.uniformBitString (k := LyubashevskyParams.k)
    (by fun_prop)

/-- The rewinding knowledge extractor for Lyubashevsky's protocol: run the prover `A` to its
commitment, answer two uniform `k`-bit challenges from the same state, and apply
`lyubashevskyExtractorAdapter` to the two conversations. -/
noncomputable def lyubashevskyKnowledgeExtractor (A : MaliciousProver LyubashevskyParams) :
    LyubashevskyParams × List Bool → ProbComp (List Bool) :=
  knowledgeExtractor lyubashevskyEncoding lyubashevskySampleChallenge
    lyubashevskyExtractorAdapter A

/-- **Lyubashevsky's knowledge extractor is uniform strict PPT** whenever the prover is. -/
theorem isPPTOn_lyubashevskyKnowledgeExtractor {A : MaliciousProver LyubashevskyParams}
    (hA : A.IsPPT encLyubashevskyParams) :
    IsPPTOn (encPair encLyubashevskyParams encBits) encBits
      (lyubashevskyKnowledgeExtractor A) :=
  isPPTOn_knowledgeExtractor isPPTOn_lyubashevskySampleChallenge
    computableInPolyTime_lyubashevskyExtractorAdapter hA

/-- **Lyubashevsky identification is a proof of knowledge of relaxed SIS solutions.** For the
parameters `p` and on every statement `(A, T)`, if the prover `A` convinces the honest verifier
with probability `ε`, the knowledge extractor outputs the encoding of a nonzero vector of infinity
norm at most `max (2 (γ - β)) 1` in the kernel of `[A | T]` with probability `ε'` such that
`ε ^ 2 - ε / 2 ^ k ≤ ε'`. -/
theorem sq_sub_le_lyubashevskyExtractionGame (A : MaliciousProver LyubashevskyParams)
    (p : LyubashevskyParams)
    (y : Matrix (Fin p.n) (Fin p.m) (ZMod p.q) × Matrix (Fin p.n) (Fin p.k) (ZMod p.q)) :
    (Game.succProbability (acceptanceGame lyubashevskyFamily lyubashevskyEncoding A p y
        (PMF.uniformOfFintype (BitString p.k))) : ℝ) ^ 2 -
      Game.succProbability (acceptanceGame lyubashevskyFamily lyubashevskyEncoding A p y
        (PMF.uniformOfFintype (BitString p.k))) / 2 ^ p.k ≤
      Game.succProbability (extractionGame lyubashevskyEncoding encLyubashevskyExtracted
        (fun p u y => SIS.IsSolution (Matrix.fromCols y.1 y.2) (max (2 * (p.γ - p.β)) 1) u)
        (lyubashevskyKnowledgeExtractor A) p y) := by
  have h := sq_sub_le_extractionGame efficientSpecialSoundness_lyubashevsky.specialSoundness
    extractorRealizedBy_lyubashevskyExtractorAdapter A p y
    (sampleChallenge := lyubashevskySampleChallenge) (ProbComp.eval_uniform _)
  simpa only [lyubashevskyKnowledgeExtractor, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using h

end Cslib.Crypto.Protocols.SigmaProtocol
