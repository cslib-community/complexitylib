/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.CollisionResistant
public import Complexity.Crypto.Computational.IndexedSignature
public import Complexity.Crypto.Computational.MerkleTree.Binding
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import Complexity.Languages.Probabilistic.Repeat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Merkle signatures

Merkle's tree signature ([Merkle1989], Section 6) authenticates `2 ^ d` one-time verification
keys by the root of a Merkle tree, which is the public key. The signature at leaf `u` is the
one-time key of leaf `u`, its one-time signature and its authentication path. Each leaf may be used
once, so the scheme is an indexed signature scheme (`IndexedSignatureScheme`) whose index is the
leaf ([BonehShoup2023], Section 14.6.1, "Shrinking the public-key").

`MerkleSignature.scheme S H depth` builds it from any signature scheme `S`, used as a one-time
scheme on `n`-bit messages, and a keyed hash `H` with `n`-bit digests under `n`-bit keys:

* key generation samples a hash key `k ← {0, 1}^n` and `2 ^ depth n` key pairs of `S`, and
  publishes `k` and the Merkle root of the one-time verification keys;
* signing `msg` at leaf `u` signs the digest `H k msg` with the one-time key of leaf `u`
  (hash-and-sign, [BonehShoup2023], Section 13.2), and attaches the verification key and the
  authentication path;
* verification checks the opening of leaf `u` with `merkleVerify`, which fixes the path length to
  `depth n` and checks `u < 2 ^ depth n`, and then the one-time signature on `H k msg`.

The capacity is `2 ^ depth n`, required to be computable in unary in polynomial time, hence
polynomial in `n`. Security is in `Complexity.Crypto.Computational.MerkleSignature.Security`.

The scheme is stateful in use: the signer must sign at most once per leaf, for instance with a
counter. `IndexedSignatureScheme` makes the leaf an explicit input, and its security game refuses
a repeated leaf.

## Main definitions

* `Cslib.Crypto.MerkleSignature.encodeSignature`, `Cslib.Crypto.MerkleSignature.signatureDecoder`:
  the signature word.
* `Cslib.Crypto.MerkleSignature.publicKey`, `Cslib.Crypto.MerkleSignature.secretKey`,
  `Cslib.Crypto.MerkleSignature.secretKeyDecoder`: the key words.
* `Cslib.Crypto.MerkleSignature.keyGen`, `Cslib.Crypto.MerkleSignature.signWith`,
  `Cslib.Crypto.MerkleSignature.sign`, `Cslib.Crypto.MerkleSignature.verify`: the algorithms.
* `Cslib.Crypto.MerkleSignature.scheme`: the indexed signature scheme.

## Main results

* `Cslib.Crypto.MerkleSignature.verify_sign`: completeness.
* `Cslib.Crypto.MerkleSignature.isPPTOn_keyGen`, `Cslib.Crypto.MerkleSignature.isPPTOn_sign`,
  `Cslib.Crypto.MerkleSignature.computableInPolyTime_verify`: efficiency.

## References

* [R. C. Merkle, *A Certified Digital Signature*][Merkle1989], Section 6.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Sections 8.9, 13.2 and 14.6.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace MerkleSignature

/-! ### Words -/

/-- A Merkle signature: the one-time verification key, the one-time signature and the
authentication path. -/
def encodeSignature (vk ots : List Bool) (path : List (List Bool)) : List Bool :=
  encPair encBits (encPair encBits (encList encBits)) (vk, ots, path)

/-- Read the one-time verification key, the one-time signature and the authentication path of a
signature word. -/
def signatureDecoder : Decoder (encPair encBits (encPair encBits (encList encBits))) :=
  Decoder.bits.pair (Decoder.bits.pair Decoder.bits.list)

/-- The secret key: the hash key and the one-time key pairs. -/
def secretKey (k : List Bool) (keys : List (List Bool × List Bool)) : List Bool :=
  encPair encBits (encList (encPair encBits encBits)) (k, keys)

/-- Read the hash key and the one-time key pairs of a secret key word. -/
def secretKeyDecoder : Decoder (encPair encBits (encList (encPair encBits encBits))) :=
  Decoder.bits.pair (Decoder.bits.pair Decoder.bits).list

variable (S : SignatureScheme) (H : List Bool → List Bool → List Bool) (depth : ℕ → ℕ)

/-- The public key: the hash key and the Merkle root of the one-time verification keys. -/
def publicKey (k : List Bool) (keys : List (List Bool × List Bool)) : List Bool :=
  encPair encBits encBits (k, merkleRoot H k (keys.map Prod.fst))

/-! ### Algorithms -/

/-- Key generation: a uniform `n`-bit hash key and `2 ^ depth n` key pairs of `S`. -/
noncomputable def keyGen (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let k ← BitString.sampleList n
  let keys ← OracleComp.replicate (2 ^ depth n) (S.keyGen n)
  return (publicKey H k keys, secretKey k keys)

/-- Sign `msg` at leaf `u`, given the hash key and the one-time key pairs: sign the digest
`H k msg` with the one-time key of leaf `u`, and attach its verification key and authentication
path. -/
def signWith (k : List Bool) (keys : List (List Bool × List Bool)) (u : ℕ)
    (msg : List Bool) : ProbComp (List Bool) := do
  let ots ← S.sign (keys.getD u ([], [])).2 (H k msg)
  return encodeSignature (keys.getD u ([], [])).1 ots (merklePath H k (keys.map Prod.fst) u)

/-- Sign `msg` at leaf `u` with a secret key word. -/
def sign (sk : List Bool) (u : ℕ) (msg : List Bool) : ProbComp (List Bool) :=
  signWith S H (secretKeyDecoder.decode sk).1 (secretKeyDecoder.decode sk).2 u msg

/-- Verify a signature on `msg` at leaf `u` under the public key `pk = (k, root)`: the attached
verification key opens leaf `u` of the depth-`depth k.length` tree with root `root`
(`merkleVerify`, which checks the path length and `u < 2 ^ depth k.length`), and the one-time
signature verifies on `H k msg`. -/
def verify (pk : List Bool) (u : ℕ) (msg sig : List Bool) : Bool :=
  let k := unframe pk
  let forged := signatureDecoder.decode sig
  merkleVerify H k (depth k.length) (dropFrame pk) u forged.1 forged.2.2 &&
    S.verify forged.1 (H k msg) forged.2.1

/-! ### Completeness -/

variable {S H depth}

/-- Every supported key generation produces an `n`-bit hash key and `2 ^ depth n` supported
one-time key pairs. -/
theorem mem_support_keyGen {n : ℕ} {keys : List Bool × List Bool}
    (h : keys ∈ (ProbComp.eval (keyGen S H depth n)).support) :
    ∃ k otsKeys, k.length = n ∧ otsKeys.length = 2 ^ depth n ∧
      (∀ x ∈ otsKeys, x ∈ (ProbComp.eval (S.keyGen n)).support) ∧
      keys = (publicKey H k otsKeys, secretKey k otsKeys) := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff, BitString.eval_sampleList] at h
  obtain ⟨k, hk, otsKeys, hotsKeys, rfl⟩ := h
  obtain ⟨hlen, hmem⟩ := (ProbComp.mem_support_replicate_iff _ _ _).mp hotsKeys
  exact ⟨k, otsKeys, BitString.length_of_mem_support_uniformList hk, hlen, hmem, rfl⟩

/-- **Completeness**: an honest signature at a leaf `u < 2 ^ depth n` verifies. -/
theorem verify_sign (hlen : ∀ k m, (H k m).length = k.length) (n : ℕ)
    (keys : List Bool × List Bool) (hkeys : keys ∈ (ProbComp.eval (keyGen S H depth n)).support)
    {u : ℕ} (hu : u < 2 ^ depth n) (msg sig : List Bool)
    (hsig : sig ∈ (ProbComp.eval (sign S H keys.2 u msg)).support) :
    verify S H depth keys.1 u msg sig = true := by
  obtain ⟨k, otsKeys, hk, hotsLen, hots, rfl⟩ := mem_support_keyGen hkeys
  simp only [sign, secretKey, secretKeyDecoder.decode_enc, signWith, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsig
  obtain ⟨ots, hots_sig, rfl⟩ := hsig
  have hu' : u < otsKeys.length := hotsLen ▸ hu
  have hkey : otsKeys.getD u ([], []) ∈ (ProbComp.eval (S.keyGen n)).support := by
    rw [List.getD_eq_getElem _ _ hu']
    exact hots _ (List.getElem_mem hu')
  have hdepth : Nat.clog 2 (otsKeys.map Prod.fst).length = depth n := by
    rw [List.length_map, hotsLen, Nat.clog_pow _ _ (by norm_num)]
  have hvk : (otsKeys.map Prod.fst).getD u [] = (otsKeys.getD u ([], [])).1 := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu'), List.getD_eq_getElem _ _ hu',
      List.getElem_map]
  have hopen := merkleVerify_merklePath_of_clog_eq (H := H) (k := k) hdepth hu
  rw [hvk] at hopen
  have hverify := S.verify_sign n _ hkey (H k msg) (by rw [hlen, hk]) ots hots_sig
  simp only [verify, encodeSignature, signatureDecoder.decode_enc]
  simp only [publicKey, encPair_apply, unframe_frame_append, dropFrame_frame_append,
    encBits_apply, hk, hopen, hverify, Bool.and_self]

/-! ### Efficiency -/

section Efficiency

variable (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
  (encPair encBits encBits) encBits)
  (hlen : ∀ k m, (H k m).length = k.length)
  (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary)

include hcap in
/-- The depth is computable from the capacity. -/
theorem computableInPolyTime_depth : ComputableInPolyTime depth encUnary encUnary := by
  have h := (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_log_two).comp hcap
  convert h using 1
  funext n
  simp [Nat.log_pow]

private theorem computableTidilyInPolyTime_keyMap :
    ComputableTidilyInPolyTime (List.map (Prod.fst : List Bool × List Bool → List Bool))
      (encList (encPair encBits encBits)) (encList encBits) :=
  ComputableTidilyInPolyTime.map (ComputableTidilyInPolyTime.fst encBits encBits)

include hH hlen in
private theorem computableTidilyInPolyTime_publicKey' :
    ComputableTidilyInPolyTime
      (fun p : List Bool × List (List Bool × List Bool) => publicKey H p.1 p.2)
      (encPair encBits (encList (encPair encBits encBits))) encBits := by
  have hk := ComputableTidilyInPolyTime.fst encBits (encList (encPair encBits encBits))
  have hroot := (computableInPolyTime_merkleRoot hH hlen).tidy.comp
    (hk.prod (computableTidilyInPolyTime_keyMap.comp (ComputableTidilyInPolyTime.snd _ _)))
  exact (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp (hk.prod hroot)

include hH hlen in
/-- Computing the public key from the hash key and the one-time key pairs takes polynomial
time. -/
theorem computableInPolyTime_publicKey :
    ComputableInPolyTime
      (fun p : List Bool × List (List Bool × List Bool) => publicKey H p.1 p.2)
      (encPair encBits (encList (encPair encBits encBits))) encBits :=
  .of_tidy (computableTidilyInPolyTime_publicKey' hH hlen)

include hH hlen hcap in
/-- Merkle key generation is uniformly strict PPT. -/
theorem isPPTOn_keyGen :
    IsPPTOn encUnary (encPair encBits encBits) (keyGen S H depth) := by
  have hk : IsPPTOn encUnary encBits (fun n => BitString.sampleList n) :=
    ComputableInPolyTime.id'.sampleList
  have hkeys : IsPPTOn (encPair encUnary encBits) (encList (encPair encBits encBits))
      (fun p : ℕ × List Bool => OracleComp.replicate (2 ^ depth p.1) (S.keyGen p.1)) :=
    (S.isPPTOn_keyGen_comp (ComputableInPolyTime.fst encUnary encBits)).replicate
      (hcap.comp (ComputableInPolyTime.fst encUnary encBits))
  have hpost : ComputableTidilyInPolyTime
      (fun q : (ℕ × List Bool) × List (List Bool × List Bool) =>
        (publicKey H q.1.2 q.2, secretKey q.1.2 q.2))
      (encPair (encPair encUnary encBits) (encList (encPair encBits encBits)))
      (encPair encBits encBits) := by
    have hkq : ComputableTidilyInPolyTime
        (fun q : (ℕ × List Bool) × List (List Bool × List Bool) => q.1.2)
        (encPair (encPair encUnary encBits) (encList (encPair encBits encBits))) encBits :=
      (ComputableTidilyInPolyTime.snd _ _).comp (ComputableTidilyInPolyTime.fst _ _)
    have hkeysq := ComputableTidilyInPolyTime.snd (encPair encUnary encBits)
      (encList (encPair encBits encBits))
    exact ((computableTidilyInPolyTime_publicKey' hH hlen).comp (hkq.prod hkeysq)).prod
      ((ComputableTidilyInPolyTime.encode
        (encPair encBits (encList (encPair encBits encBits)))).comp (hkq.prod hkeysq))
  exact hk.bind_with (hkeys.bind_with hpost.isPPTOn)

include hH hlen in
/-- Merkle signing is uniformly strict PPT. -/
theorem isPPTOn_sign :
    IsPPTOn (encPair encBits (encPair encUnary encBits)) encBits
      (fun p => sign S H p.1 p.2.1 p.2.2) := by
  let E := encPair encBits (encPair encUnary encBits)
  have hdec : ComputableTidilyInPolyTime (fun p : List Bool × ℕ × List Bool =>
      secretKeyDecoder.decode p.1) E (encPair encBits (encList (encPair encBits encBits))) :=
    secretKeyDecoder.computableInPolyTime.tidy.comp (ComputableTidilyInPolyTime.fst _ _)
  have hk := (ComputableTidilyInPolyTime.fst _ _).comp hdec
  have hkeys := (ComputableTidilyInPolyTime.snd _ _).comp hdec
  have hu : ComputableTidilyInPolyTime (fun p : List Bool × ℕ × List Bool => p.2.1) E encUnary :=
    (ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _)
  have hmsg : ComputableTidilyInPolyTime (fun p : List Bool × ℕ × List Bool => p.2.2) E encBits :=
    (ComputableTidilyInPolyTime.snd _ _).comp (ComputableTidilyInPolyTime.snd _ _)
  have hkey : ComputableTidilyInPolyTime (fun p : List Bool × ℕ × List Bool =>
      (secretKeyDecoder.decode p.1).2.getD p.2.1 ([], [])) E (encPair encBits encBits) :=
    (ComputableTidilyInPolyTime.listGetD (encA := encPair encBits encBits) ([], [])).comp
      (hkeys.prod hu)
  have hsign : IsPPTOn E encBits (fun p : List Bool × ℕ × List Bool =>
      S.sign ((secretKeyDecoder.decode p.1).2.getD p.2.1 ([], [])).2
        (H (secretKeyDecoder.decode p.1).1 p.2.2)) :=
    S.isPPTOn_sign_comp (.of_tidy ((ComputableTidilyInPolyTime.snd _ _).comp hkey))
      (hH.comp (.of_tidy (hk.prod hmsg)))
  have hpath : ComputableTidilyInPolyTime (fun p : List Bool × ℕ × List Bool =>
      merklePath H (secretKeyDecoder.decode p.1).1
        ((secretKeyDecoder.decode p.1).2.map Prod.fst) p.2.1) E (encList encBits) :=
    (computableInPolyTime_merklePath hH hlen).tidy.comp
      (hk.prod ((computableTidilyInPolyTime_keyMap.comp hkeys).prod hu))
  have hpost : ComputableTidilyInPolyTime (fun q : (List Bool × ℕ × List Bool) × List Bool =>
      encodeSignature ((secretKeyDecoder.decode q.1.1).2.getD q.1.2.1 ([], [])).1 q.2
        (merklePath H (secretKeyDecoder.decode q.1.1).1
          ((secretKeyDecoder.decode q.1.1).2.map Prod.fst) q.1.2.1))
      (encPair E encBits) encBits := by
    have hfst := ComputableTidilyInPolyTime.fst E encBits
    exact (ComputableTidilyInPolyTime.encode
      (encPair encBits (encPair encBits (encList encBits)))).comp
        ((((ComputableTidilyInPolyTime.fst _ _).comp hkey).comp hfst).prod
          ((ComputableTidilyInPolyTime.snd E encBits).prod (hpath.comp hfst)))
  exact hsign.bind_with hpost.isPPTOn

include hH hlen hcap in
/-- Merkle verification is computable in polynomial time. -/
theorem computableInPolyTime_verify :
    ComputableInPolyTime
      (fun p : List Bool × ℕ × List Bool × List Bool => verify S H depth p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encBits (encPair encUnary (encPair encBits encBits))) encBool := by
  apply ComputableInPolyTime.of_tidy
  let E := encPair encBits (encPair encUnary (encPair encBits encBits))
  have hpk : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ × List Bool × List Bool => p.1) E encBits :=
    ComputableTidilyInPolyTime.fst _ _
  have hu : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ × List Bool × List Bool => p.2.1) E encUnary :=
    (ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _)
  have hmsg : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ × List Bool × List Bool => p.2.2.1) E encBits :=
    (ComputableTidilyInPolyTime.fst _ _).comp
      ((ComputableTidilyInPolyTime.snd _ _).comp (ComputableTidilyInPolyTime.snd _ _))
  have hsig : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ × List Bool × List Bool => p.2.2.2) E encBits :=
    (ComputableTidilyInPolyTime.snd _ _).comp
      ((ComputableTidilyInPolyTime.snd _ _).comp (ComputableTidilyInPolyTime.snd _ _))
  have hk := ComputableTidilyInPolyTime.unframe.comp hpk
  have hroot := ComputableTidilyInPolyTime.dropFrame.comp hpk
  have hd : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ × List Bool × List Bool => depth (unframe p.1).length) E encUnary :=
    (computableInPolyTime_depth hcap).tidy.comp
      ((ComputableTidilyInPolyTime.length encBool).comp hk)
  have hdec := signatureDecoder.computableInPolyTime.tidy.comp hsig
  have hvk := (ComputableTidilyInPolyTime.fst _ _).comp hdec
  have hrest := (ComputableTidilyInPolyTime.snd _ _).comp hdec
  have hots := (ComputableTidilyInPolyTime.fst _ _).comp hrest
  have hpath := (ComputableTidilyInPolyTime.snd _ _).comp hrest
  have hopen := (computableInPolyTime_merkleVerify hH hlen).tidy.comp
    ((hk.prod hd).prod ((hroot.prod hu).prod (hvk.prod hpath)))
  have hots_verify := (S.computableInPolyTime_verify_comp (.of_tidy hvk)
    (hH.comp (.of_tidy (hk.prod hmsg))) (.of_tidy hots)).tidy
  exact ComputableTidilyInPolyTime.bool_and.comp (hopen.prod hots_verify)

end Efficiency

variable (S H depth) in
/-- **Merkle's tree signature** ([Merkle1989], Section 6; [BonehShoup2023], Section 14.6.1) as
an indexed signature scheme of capacity `2 ^ depth n`, from a signature scheme `S` used as a
one-time scheme and a keyed hash `H` with digests of the key's length. -/
noncomputable def scheme (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ k m, (H k m).length = k.length)
    (hcap : ComputableInPolyTime (fun n => 2 ^ depth n) encUnary encUnary) :
    IndexedSignatureScheme where
  capacity n := 2 ^ depth n
  keyGen := keyGen S H depth
  sign := sign S H
  verify := verify S H depth
  capacity_polyTime := hcap
  keyGen_ppt := isPPTOn_keyGen hH hlen hcap
  sign_ppt := isPPTOn_sign hH hlen
  verify_polyTime := computableInPolyTime_verify hH hlen hcap
  verify_sign n keys hkeys _ hu msg sig hsig := verify_sign hlen n keys hkeys hu msg sig hsig

end MerkleSignature

end Cslib.Crypto
