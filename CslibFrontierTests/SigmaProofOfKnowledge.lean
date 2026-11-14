/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SchnorrProofOfKnowledge
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.ProofOfKnowledge
import CslibFrontier.Tactic.PPT

/-!
# Tests for Sigma-protocol knowledge extraction

`MaliciousProver.IsPPT` is satisfiable: the echoing prover, which commits to the statement word and
answers with the challenge word, is uniform strict PPT for any index encoding. So the strict PPT
certificates of the Schnorr and Lyubashevsky knowledge extractors apply to it.
-/

@[expose] public section

namespace CslibFrontierTests.SigmaProofOfKnowledge

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.SigmaProtocol
open Turing.MultiTapeTM

/-- A prover that commits to the statement word, keeps it as its state, and answers each challenge
word with itself. -/
def echoProver (I : Type) : MaliciousProver I where
  commit _ y := pure (y, y)
  respond _ _ c := pure c

/-- The echoing prover is uniform strict PPT for any index encoding. -/
theorem isPPT_echoProver {I : Type} (encI : I ↪ List Bool) : (echoProver I).IsPPT encI where
  commit := (ComputableInPolyTime.tidy (by fun_prop :
    ComputableInPolyTime (fun p : I × List Bool => (p.2, p.2)) (encPair encI encBits)
      (encPair encBits encBits))).isPPTOn
  respond := (ComputableInPolyTime.tidy (by fun_prop :
    ComputableInPolyTime (fun p : I × List Bool × List Bool => p.2.2)
      (encPair encI (encPair encBits encBits)) encBits)).isPPTOn

/-- Schnorr's knowledge extractor for the echoing prover is uniform strict PPT. -/
example (F : PrimeOrderGroupFamily) :
    IsPPTOn (encPair (encPair encUnary F.encDesc) encBits) encBits
      (F.schnorrKnowledgeExtractor (echoProver _)) :=
  F.isPPTOn_schnorrKnowledgeExtractor (isPPT_echoProver _)

/-- Lyubashevsky's knowledge extractor for the echoing prover is uniform strict PPT. -/
example :
    IsPPTOn (encPair encLyubashevskyParams encBits) encBits
      (lyubashevskyKnowledgeExtractor (echoProver _)) :=
  isPPTOn_lyubashevskyKnowledgeExtractor (isPPT_echoProver _)

end CslibFrontierTests.SigmaProofOfKnowledge
