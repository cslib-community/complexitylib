/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Commitment.PublicOperations
public import Complexity.Crypto.Computational.PedersenCommitment
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Public-operation certificates for Pedersen commitments

`PrimeOrderGroupFamily.pedersenPublicOperations` certifies deterministic commitment evaluation
on supplied randomness and verification using exactly the public key bytes of `pedersenScheme`.
It reuses `encodePedersenCommit` and its existing polynomial-time certificate. The ideal law
of the randomness word is the canonical binary encoding of a uniform exponent in `ZMod q`;
the exact map equation recovers `pedersenCommitPairLaw`.

No executable randomness sampler, setup algorithm, or strict-PPT realization of the ideal
commitment law is asserted. In particular, the uniform exponent law is still semantic `PMF` data.
The security games and their existing hiding and binding claims are unchanged.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.encodePedersenVerify`: verification on encoded public group
  elements and message, commitment and opening words.
* `Cslib.Crypto.PrimeOrderGroupFamily.pedersenPublicOperations`: efficient public deterministic
  operations with the exact ideal supplied-randomness law.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.encodePedersenVerify_encode`: encoded verification agrees
  with the existing semantic verifier.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodePedersenVerify`: the encoded
  verifier is polynomial-time.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

/-- Pedersen verification from `(description, encoded public element)`, message, commitment and
opening words. The public element is already encoded; no discrete logarithm or semantic group
value is supplied to this algorithm. -/
def encodePedersenVerify
    (input : (F.Desc × List Bool) × List Bool × List Bool × List Bool) : Bool :=
  decide (ofBits input.2.1 < F.order input.1.1) &&
    decide ((ofBits input.2.1).bits = input.2.1) &&
    decide (F.encodePedersenCommit
      (input.1.1, input.1.2, ofBits input.2.1, ofBits input.2.2.2) = input.2.2.1)

/-- The encoded verifier computes exactly the verifier used by `pedersenScheme`. -/
@[simp]
theorem encodePedersenVerify_encode (d : F.Desc) (h : F.Carrier d) (m c o : List Bool) :
    F.encodePedersenVerify ((d, F.encode d h), m, c, o) = F.pedersenVerify d h m c o := by
  simp only [encodePedersenVerify, pedersenVerify, encodePedersenCommit_encode]

/-- Encoded Pedersen verification is polynomial-time in all of its input words. -/
theorem computableInPolyTime_encodePedersenVerify :
    ComputableInPolyTime F.encodePedersenVerify
      (encPair (encPair F.encDesc encBits) (encPair encBits (encPair encBits encBits)))
      encBool := by
  have horder := F.computableInPolyTime_order
  have hcommit := F.computableInPolyTime_encodePedersenCommit
  unfold encodePedersenVerify
  fun_prop

/-- Deterministic Pedersen commitment evaluation and verification from `pedersenScheme.encodeKey`,
with the ideal randomness law given by the canonical bits of a uniform `ZMod q` exponent.
This does not certify sampling that law or key generation. -/
noncomputable def pedersenPublicOperations : F.pedersenScheme.PublicOperations where
  commit k m coins :=
    (F.encodePedersenCommit (k.1, F.encode k.1 k.2, ofBits m, ofBits coins), coins)
  randomness k := (PMF.uniformOfFintype (ZMod (F.order k.1))).map (fun r => r.val.bits)
  map_commit k m := by
    simp only [PMF.map_comp, pedersenScheme, pedersenCommitPairLaw]
    congr 1
    funext r
    have hr : (ofBits r.val.bits : ZMod (F.order k.1)) = r := by
      unfold ofBits
      rw [Nat.foldr_bit_bits, ZMod.natCast_zmod_val]
    simp only [Function.comp_apply, encodePedersenCommit_encode, hr]
  commit_polyTime := by
    have hkey : ComputableInPolyTime
        (fun k : F.PedersenKey => (k.1, F.encode k.1 k.2))
        F.pedersenScheme.encodeKey (encPair F.encDesc encBits) := .of_eq fun _ => rfl
    have hpublic := hkey.comp
      (ComputableInPolyTime.fst F.pedersenScheme.encodeKey (encPair encBits encBits))
    have hrest := ComputableInPolyTime.snd F.pedersenScheme.encodeKey (encPair encBits encBits)
    have hm := ComputableInPolyTime.bitsToNat.comp hrest.fst'
    have hr := ComputableInPolyTime.bitsToNat.comp hrest.snd'
    exact (F.computableInPolyTime_encodePedersenCommit.comp
      (hpublic.fst'.prod (hpublic.snd'.prod (hm.prod hr)))).prod hrest.snd'
  verify_polyTime := by
    have hkey : ComputableInPolyTime
        (fun k : F.PedersenKey => (k.1, F.encode k.1 k.2))
        F.pedersenScheme.encodeKey (encPair F.encDesc encBits) := .of_eq fun _ => rfl
    have hpublic := hkey.comp (ComputableInPolyTime.fst F.pedersenScheme.encodeKey
      (encPair encBits (encPair encBits encBits)))
    have hrest := ComputableInPolyTime.snd F.pedersenScheme.encodeKey
      (encPair encBits (encPair encBits encBits))
    have hv := F.computableInPolyTime_encodePedersenVerify.comp (hpublic.prod hrest)
    convert hv using 1
    funext p
    exact (F.encodePedersenVerify_encode p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2).symm

end Cslib.Crypto.PrimeOrderGroupFamily
