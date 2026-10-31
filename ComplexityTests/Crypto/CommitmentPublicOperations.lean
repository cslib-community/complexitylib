/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Computational.DiscreteLog.SchnorrGroup
import Complexity.Crypto.Computational.PedersenCommitment.PublicOperations
import Mathlib.Tactic.NormNum.Prime

/-!
# Public-input commitment clients

An ordinary module imports only the exported API. Concrete encoded verification checks use the
Schnorr group of order `11` modulo `23`; composition clients charge the public key using precisely
`pedersenScheme.encodeKey`.
-/

public section

namespace ComplexityTests.Crypto.CommitmentPublicOperations

open Cslib Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM

/-- A concrete valid Schnorr group description used by the evaluation checks. -/
def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

/-- Public bytes `h = 8`, message `4` and opening `5` verify commitment `3`. -/
example : schnorrGroups.encodePedersenVerify
    ((d23, Nat.bits 8), Nat.bits 4, Nat.bits 3, Nat.bits 5) = true := by decide

/-- A different commitment is rejected with exactly the same public input and opening. -/
example : schnorrGroups.encodePedersenVerify
    ((d23, Nat.bits 8), Nat.bits 4, Nat.bits 4, Nat.bits 5) = false := by decide

/-- Noncanonical message words are rejected even if they represent the same exponent. -/
example : schnorrGroups.encodePedersenVerify
    ((d23, Nat.bits 8), Nat.bits 4 ++ [false], Nat.bits 3, Nat.bits 5) = false := by decide

/-- The public-operations evaluator computes both commitment and opening for supplied coins. -/
example : schnorrGroups.pedersenPublicOperations.commit
    ⟨d23, (3 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23⟩
    (Nat.bits 4) (Nat.bits 5) =
      (Nat.bits 3, Nat.bits 5) := by decide

/-- A client can discard the opening after evaluation with fixed supplied randomness, charging
its arbitrary public key and message as input. -/
example : ComputableInPolyTime
    (fun p : schnorrGroups.PedersenKey × List Bool =>
      (schnorrGroups.pedersenPublicOperations.commit p.1 p.2 (Nat.bits 5)).1)
    (encPair schnorrGroups.pedersenScheme.encodeKey encBits) encBits := by
  have hk := ComputableInPolyTime.fst schnorrGroups.pedersenScheme.encodeKey encBits
  have hm := ComputableInPolyTime.snd schnorrGroups.pedersenScheme.encodeKey encBits
  exact (schnorrGroups.pedersenPublicOperations.computableInPolyTime_commit
    hk hm (.const (Nat.bits 5))).fst'

/-- A verifier client recomputes a candidate commitment from supplied coins and verifies the
result through the general public-operations API, without receiving the semantic key as advice. -/
example : ComputableInPolyTime
    (fun p : schnorrGroups.PedersenKey × List Bool × List Bool =>
      let co := schnorrGroups.pedersenPublicOperations.commit p.1 p.2.1 p.2.2
      schnorrGroups.pedersenScheme.verify p.1 p.2.1 co.1 co.2)
    (encPair schnorrGroups.pedersenScheme.encodeKey (encPair encBits encBits)) encBool := by
  have hk := ComputableInPolyTime.fst schnorrGroups.pedersenScheme.encodeKey
    (encPair encBits encBits)
  have hrest := ComputableInPolyTime.snd schnorrGroups.pedersenScheme.encodeKey
    (encPair encBits encBits)
  have hco := schnorrGroups.pedersenPublicOperations.computableInPolyTime_commit
    hk hrest.fst' hrest.snd'
  exact schnorrGroups.pedersenPublicOperations.computableInPolyTime_verify
    hk hrest.fst' hco.fst' hco.snd'

end ComplexityTests.Crypto.CommitmentPublicOperations
