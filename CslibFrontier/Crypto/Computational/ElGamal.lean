/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Probability.BitString.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PolyTime.Init

/-!
# ElGamal and Hashed ElGamal encryption and IND-CPA security under DDH

Over a `PrimeOrderGroupFamily`, multiplicative ElGamal encryption ([BonehShoup2023],
Exercise 11.5, p. 459) uses a group description `d`, a secret exponent `α : ZMod (F.order d)`,
and the public key `u = α • g`.
To encrypt a group element `m : F.Carrier d` with randomness `β : ZMod (F.order d)`, the sender
forms the ciphertext `(v, e) = (β • g, β • u + m) = (β • g, (α * β) • g + m)`. Decryption recovers
`e - α • v = m`, and the word-level operations `encodeElGamalPublicKey`, `encodeElGamalEncrypt`,
and `decodeElGamal` compute public-key generation, encryption, and decryption in polynomial time
from natural-number exponents and encoded group elements using `F.generator`, `F.order`, `F.smul`,
and `F.add`.

We prove IND-CPA security under DDH in the following settings:
1. **Shared typed-message ElGamal reduction** (`elGamalMsgCPAGameOn`,
   `elGamalMsgToDDHDistinguisher`, `advantage_elGamalMsgCPAGameOn_le`,
   `isPPT_elGamalMsgToDDHDistinguisher`, `DDH.negligible_elGamalMsgCPAGameOn`). As in
   `Encryption.gameOn`, a challenge-pair admissibility predicate
   `valid : ℕ → List Bool → Msg → Msg → Bool` sees the security parameter and the public key, and
   an inadmissible pair makes the game output `false` in both experiments. The reduction needs
   `valid` to be computable in polynomial time and to admit only messages whose encodings are
   group elements (`AdmitsGroupElements`). It is instantiated for:
   - **Bit ElGamal** (`elGamalCPAGame`, `elGamalINDCPA`, `DDH.elGamalINDCPA`): `false` and `true`
     are embedded as `0` and `g` (`bitElement`, `encodeBit`), every pair is admissible, and
     `Encryption.Adversary` chooses two challenge bits.
   - **Group-element ElGamal** (`Encryption.WordAdversary`, `elGamalGroupCPAGameOn`,
     `DDH.negligible_elGamalGroupCPAGameOn`, [BonehShoup2023], Exercise 11.5(a), p. 459): a
     two-stage word-message adversary chooses two words, and `valid` admits only encoded group
     elements, in `Set.range (F.encode d)`. Replacing the Diffie–Hellman mask `(α * β) • g` with an
     independent uniform `γ • g` masks any admissible pair perfectly
     (`uniform_smul_generator_add`). A `PrimeOrderGroupFamily` has no membership test, so `valid`
     is a parameter; the tests instantiate it on Schnorr groups.
2. **Hashed ElGamal** (`hashedElGamalEncrypt`, `hashedElGamalDecrypt`, `hashedElGamalCPAGame`,
   `DDH.negligible_hashedElGamalCPAGame`, [BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1,
   and Section 11.5.2, Attack Game 11.3, Definition 11.5, and Theorem 11.5, pp. 448–451): given a
   deterministic polynomial-time key-derivation hash function `H : F.Desc × List Bool → List Bool`,
   the sender masks a message word `m` with `pad = H (d, encode (β • u))` via
   `Cslib.BitString.listXor pad.length [pad, m]` (the one-time pad specialization of the `E'_EG`
   variant of Remark 11.1). Security reduces to `DDH` together with key-derivation security
   (`SecureKDF`, Attack Game 11.3, p. 448, and Definition 11.5, p. 449: indistinguishability of
   `H (d, encode (γ • g))` from a uniform `msgLen n`-bit key). The ciphertext length does not
   depend on the message, and `hashedElGamalCPAGame` admits every challenge pair, which is
   stronger than Attack Game 11.1's equal-length rule.

The reductions are typed distinguishers (`DDHDistinguisher`, `KDFDistinguisher`): they receive
group elements and encode them only where they build the public key and ciphertext words of the
IND-CPA adversary, whose games keep their word encodings.

## Limitations

In this module, key generation and challenge encryption in the security games sample exact uniform
exponents in `ZMod (F.order d)` at the `PMF` level (`PMF.uniformOfFintype (ZMod (F.order d))`),
because an odd prime order `F.order d` cannot be sampled with exact uniformity by a bounded-time
fair-coin `ProbComp` machine; deterministic public-key computation (`encodeElGamalPublicKey`),
encryption given randomness (`encodeElGamalEncrypt`, `encodeHashedElGamalEncrypt`), and decryption
(`decodeElGamal`, `decodeHashedElGamal`) are certified polynomial time on words. Strict-PPT
(`IsPPTOn`) key generation, KEM encapsulation/decapsulation, and encryption via
`ProbComp.sampleModNat` (connecting to `Encryption.KEMINDCPA`, `Encryption.INDCPAOn`,
`Encryption.WordINDCPA`, and `Encryption.INDCPA`) are provided in
`CslibFrontier/Crypto/Computational/ElGamal/ProbComp.lean`; non-degenerate `SecureKDF` instantiation
(`msgLen n > 0`) via `BitString.LinearHash` and the leftover hash lemma is provided in
`CslibFrontier/Crypto/Computational/ElGamal/KDF.lean`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt`: algebraic ElGamal encryption and decryption.
* `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalPublicKey`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal`: polynomial-time public-key generation,
  encryption, and decryption on encoded group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalMsgCPAGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalMsgToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.AdmitsGroupElements`: shared typed-message ElGamal IND-CPA
  experiment with an admissibility predicate, DDH reduction, and the condition that the predicate
  admits only group elements ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.bitElement`, `Cslib.Crypto.PrimeOrderGroupFamily.encodeBit`:
  embedding and polynomial-time encoding of message bits as group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalINDCPA`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalToDDHDistinguisher`: bit ElGamal IND-CPA experiment,
  security property, and DDH distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalGroupCPAGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalGroupToDDHDistinguisher`: group-element ElGamal
  IND-CPA experiment and DDH reduction ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeHashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeHashedElGamal`: algebraic and word-level Hashed ElGamal
  encryption and decryption ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1).
* `Cslib.Crypto.PrimeOrderGroupFamily.KDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kdfRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kdfIdealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.KDFInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encKDFInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.KDFDistinguisher.IsPPT`,
  `Cslib.Crypto.PrimeOrderGroupFamily.KDFDistinguisher.IsPPT.comp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.SecureKDF`: typed key-derivation distinguishers, the
  key-derivation experiments, their input record and its encoding, their uniform strict PPT
  predicate and its composition rule, and secure key derivation ([BonehShoup2023], Section 11.5.2,
  Attack Game 11.3 and Definition 11.5, pp. 448–449).
* `Cslib.Crypto.PrimeOrderGroupFamily.kdfToDDHDistinguisher`: a key-derivation distinguisher run
  on the key `H (d, encode w)` derived from a DDH candidate `w`; its random DDH game is the real
  key-derivation game.
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalToKDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalToDDHDistinguisher`: Hashed ElGamal IND-CPA
  experiment and reductions ([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.secureKDF_iff_encoded`: `SecureKDF` is the word-level
  key-derivation assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt_elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalPublicKey_eq_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalEncrypt_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal_elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal_encodeElGamalEncrypt`: ElGamal correctness.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeElGamalPublicKey`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_decodeElGamal`: polynomial-time
  certificates for honest ElGamal operations.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalMsgCPAGameOn_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_elGamalMsgToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_elGamalMsgCPAGameOn`: shared typed-message
  ElGamal IND-CPA reduction to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_elGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.elGamalINDCPA`: ElGamal IND-CPA security for bit
  messages under DDH ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalGroupCPAGameOn_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_elGamalGroupCPAGameOn`: ElGamal IND-CPA
  security for group-element messages under DDH ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecrypt_hashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeHashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_decodeHashedElGamal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRandomGame_kdfToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_kdfToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_hashedElGamalToKDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCPAGame`: Hashed ElGamal
  correctness, polynomial-time certificates, and IND-CPA security under DDH and `SecureKDF`
  ([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5 (pp. 445–446, Remark 11.1), Section 11.5.2
  (pp. 448–451, Attack Game 11.3, Definition 11.5, Theorem 11.5), and Exercise 11.5(a) (p. 459).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

/-! ### Group-element ElGamal encryption and decryption -/

/-- Algebraic ElGamal encryption of a group element `m : F.Carrier d` under public key
`u : F.Carrier d` with randomness `β : ZMod (F.order d)`. -/
def elGamalEncrypt (d : F.Desc) (u m : F.Carrier d) (β : ZMod (F.order d)) :
    F.Carrier d × F.Carrier d :=
  (β • F.generator d, β • u + m)

/-- Under a genuine public key `u = α • g`, the second ciphertext component is
`(α * β) • g + m`. -/
theorem elGamalEncrypt_smul_generator (d : F.Desc) (α β : ZMod (F.order d)) (m : F.Carrier d) :
    F.elGamalEncrypt d (α • F.generator d) m β =
      (β • F.generator d, (α * β) • F.generator d + m) := by
  simp only [elGamalEncrypt, smul_smul, mul_comm β α]

/-- Algebraic ElGamal decryption of a ciphertext pair `(v, e)` using secret key
`α : ZMod (F.order d)`. -/
def elGamalDecrypt (d : F.Desc) (α : ZMod (F.order d)) (ct : F.Carrier d × F.Carrier d) :
    F.Carrier d :=
  ct.2 - α • ct.1

/-- **ElGamal decryption correctness**: decrypting an encryption under `u = α • g` with secret key
`α` recovers the message `m`. -/
@[simp] theorem elGamalDecrypt_elGamalEncrypt (d : F.Desc) (α β : ZMod (F.order d))
    (m : F.Carrier d) :
    F.elGamalDecrypt d α (F.elGamalEncrypt d (α • F.generator d) m β) = m := by
  simp only [elGamalDecrypt, elGamalEncrypt, smul_smul, mul_comm β α, add_sub_cancel_left]

/-- Word-level ElGamal public-key computation: given `(d, a)`, compute `encode ((a : ZMod q) • g)`
as `F.smul (d, a, F.encode d (F.generator d))`. -/
def encodeElGamalPublicKey (input : F.Desc × ℕ) : List Bool :=
  F.smul (input.1, input.2, F.encode input.1 (F.generator input.1))

/-- `encodeElGamalPublicKey` computes the group encoding of `(a : ZMod (F.order d)) • g`. -/
@[simp] theorem encodeElGamalPublicKey_eq_encode (d : F.Desc) (a : ℕ) :
    F.encodeElGamalPublicKey (d, a) =
      F.encode d ((a : ZMod (F.order d)) • F.generator d) := by
  simp only [encodeElGamalPublicKey, F.smul_encode]

/-- Word-level ElGamal public-key computation is computable in polynomial time. -/
theorem computableInPolyTime_encodeElGamalPublicKey :
    ComputableInPolyTime F.encodeElGamalPublicKey (encPair F.encDesc encNat) encBits := by
  have hd := ComputableInPolyTime.fst F.encDesc encNat
  exact F.computableInPolyTime_smul.comp
    (hd.prod ((ComputableInPolyTime.snd F.encDesc encNat).prod
      (F.computableInPolyTime_generator.comp hd)))

/-- Payload `(u, m, b)` of a 4-tuple encryption input `(d, u, m, b)`. -/
abbrev encPayload {Msg : Type} (input : F.Desc × List Bool × Msg × ℕ) : List Bool × Msg × ℕ :=
  input.2

/-- Encoded public-key component `u` of a 4-tuple encryption input `(d, u, m, b)`. -/
abbrev encPk {Msg : Type} (input : F.Desc × List Bool × Msg × ℕ) : List Bool :=
  (F.encPayload input).1

/-- Message and randomness pair `(m, b)` of a 4-tuple encryption input `(d, u, m, b)`. -/
abbrev encMsgRand {Msg : Type} (input : F.Desc × List Bool × Msg × ℕ) : Msg × ℕ :=
  (F.encPayload input).2

/-- Message component `m` of a 4-tuple encryption input `(d, u, m, b)`. -/
abbrev encMsg {Msg : Type} (input : F.Desc × List Bool × Msg × ℕ) : Msg :=
  (F.encMsgRand input).1

/-- Randomness component `b` of a 4-tuple encryption input `(d, u, m, b)`. -/
abbrev encRand {Msg : Type} (input : F.Desc × List Bool × Msg × ℕ) : ℕ :=
  (F.encMsgRand input).2

/-- Payload `(a, v, c)` of a 4-tuple decryption input `(d, a, v, c)`. -/
abbrev decPayload (input : F.Desc × ℕ × List Bool × List Bool) : ℕ × List Bool × List Bool :=
  input.2

/-- Secret-key exponent `a` of a 4-tuple decryption input `(d, a, v, c)`. -/
abbrev decSk (input : F.Desc × ℕ × List Bool × List Bool) : ℕ :=
  (F.decPayload input).1

/-- Ciphertext components `(v, c)` of a 4-tuple decryption input `(d, a, v, c)`. -/
abbrev decCt (input : F.Desc × ℕ × List Bool × List Bool) : List Bool × List Bool :=
  (F.decPayload input).2

/-- Encoded ephemeral element `v` of a 4-tuple decryption input `(d, a, v, c)`. -/
abbrev decEph (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  (F.decCt input).1

/-- Encoded body `c` of a 4-tuple decryption input `(d, a, v, c)`. -/
abbrev decBody (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  (F.decCt input).2

/-- Word-level ElGamal encryption: given `(d, encode u, encode m, b)`, compute
`(encode (b • g), encode (b • u + m))`. -/
def encodeElGamalEncrypt (input : F.Desc × List Bool × List Bool × ℕ) : List Bool × List Bool :=
  (F.smul (input.1, F.encRand input, F.encode input.1 (F.generator input.1)),
    F.add (input.1, F.smul (input.1, F.encRand input, F.encPk input), F.encMsg input))

/-- `encodeElGamalEncrypt` evaluates `elGamalEncrypt` on encoded group elements. -/
@[simp] theorem encodeElGamalEncrypt_encode (d : F.Desc) (u m : F.Carrier d) (b : ℕ) :
    F.encodeElGamalEncrypt (d, F.encode d u, F.encode d m, b) =
      (F.encode d (F.elGamalEncrypt d u m (b : ZMod (F.order d))).1,
        F.encode d (F.elGamalEncrypt d u m (b : ZMod (F.order d))).2) := by
  simp only [encodeElGamalEncrypt, elGamalEncrypt, F.smul_encode, F.add_encode]

/-- Word-level ElGamal encryption is computable in polynomial time. -/
theorem computableInPolyTime_encodeElGamalEncrypt :
    ComputableInPolyTime F.encodeElGamalEncrypt
      (encPair F.encDesc (encPair encBits (encPair encBits encNat)))
      (encPair encBits encBits) := by
  have hd := ComputableInPolyTime.fst F.encDesc (encPair encBits (encPair encBits encNat))
  have h2 := ComputableInPolyTime.snd F.encDesc (encPair encBits (encPair encBits encNat))
  have hu := (ComputableInPolyTime.fst encBits (encPair encBits encNat)).comp h2
  have h3 := (ComputableInPolyTime.snd encBits (encPair encBits encNat)).comp h2
  have hm := (ComputableInPolyTime.fst encBits encNat).comp h3
  have hb := (ComputableInPolyTime.snd encBits encNat).comp h3
  have hg := F.computableInPolyTime_generator.comp hd
  have hv := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hg))
  have hbu := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hu))
  exact hv.prod (F.computableInPolyTime_add.comp (hd.prod (hbu.prod hm)))

/-- Decryption on encoded group elements: given `(d, a, encode v, encode e)`, compute
`encode (e - a • v)` as `F.add (d, encode e, F.smul (d, F.order d - a % F.order d, encode v))`. -/
def decodeElGamal (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  F.add (input.1, F.decBody input,
    F.smul (input.1, F.order input.1 - F.decSk input % F.order input.1, F.decEph input))

/-- `decodeElGamal` computes `encode (elGamalDecrypt d a (v, e))` on encoded group elements. -/
theorem decodeElGamal_encode (d : F.Desc) (a : ℕ) (v e : F.Carrier d) :
    F.decodeElGamal (d, a, F.encode d v, F.encode d e) =
      F.encode d (F.elGamalDecrypt d (a : ZMod (F.order d)) (v, e)) := by
  have hneg : ((F.order d - a % F.order d : ℕ) : ZMod (F.order d)) = -(a : ZMod (F.order d)) := by
    rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (F.prime_order d).pos)), ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  simp only [decodeElGamal, F.smul_encode, hneg, neg_smul, F.add_encode, elGamalDecrypt,
    sub_eq_add_neg]

/-- Encoded ElGamal decryption of an honest encryption recovers the encoded message. -/
@[simp] theorem decodeElGamal_elGamalEncrypt (d : F.Desc) (a : ℕ) (β : ZMod (F.order d))
    (m : F.Carrier d) :
    F.decodeElGamal (d, a,
      F.encode d (F.elGamalEncrypt d ((a : ZMod (F.order d)) • F.generator d) m β).1,
      F.encode d (F.elGamalEncrypt d ((a : ZMod (F.order d)) • F.generator d) m β).2) =
      F.encode d m := by
  rw [F.decodeElGamal_encode, F.elGamalDecrypt_elGamalEncrypt]

/-- Word-level ElGamal decryption of `encodeElGamalEncrypt` under `encodeElGamalPublicKey` recovers
the encoded message. -/
theorem decodeElGamal_encodeElGamalEncrypt (d : F.Desc) (a b : ℕ) (m : F.Carrier d) :
    F.decodeElGamal (d, a,
      (F.encodeElGamalEncrypt (d, F.encodeElGamalPublicKey (d, a), F.encode d m, b)).1,
      (F.encodeElGamalEncrypt (d, F.encodeElGamalPublicKey (d, a), F.encode d m, b)).2) =
      F.encode d m := by
  simp only [encodeElGamalPublicKey_eq_encode, encodeElGamalEncrypt_encode,
    decodeElGamal_elGamalEncrypt]

/-- Encoded ElGamal decryption is computable in polynomial time. -/
theorem computableInPolyTime_decodeElGamal :
    ComputableInPolyTime F.decodeElGamal
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by
  have hd := ComputableTidilyInPolyTime.fst F.encDesc (encPair encNat (encPair encBits encBits))
  have h2 := ComputableTidilyInPolyTime.snd F.encDesc (encPair encNat (encPair encBits encBits))
  have ha := (ComputableTidilyInPolyTime.fst encNat (encPair encBits encBits)).comp h2
  have h3 := (ComputableTidilyInPolyTime.snd encNat (encPair encBits encBits)).comp h2
  have hv := (ComputableTidilyInPolyTime.fst encBits encBits).comp h3
  have he := (ComputableTidilyInPolyTime.snd encBits encBits).comp h3
  have horder := F.computableInPolyTime_order.tidy.comp hd
  have hexp := ComputableTidilyInPolyTime.binary_sub' horder (.binary_mod' ha horder)
  have hsmul := F.computableInPolyTime_smul.tidy.comp (hd.prod (hexp.prod hv))
  exact ComputableInPolyTime.of_tidy
    (F.computableInPolyTime_add.tidy.comp (hd.prod (he.prod hsmul)))

/-! ### Shared typed-message ElGamal IND-CPA reduction ([BonehShoup2023], Exercise 11.5(a)) -/

/-- The IND-CPA experiment for multiplicative ElGamal encryption over message type `Msg` via a
word-level message encoder `encodeMsg : F.Desc → Msg → List Bool`, with challenge-pair
admissibility predicate `valid` ([BonehShoup2023], Exercise 11.5(a), p. 459, played in Attack
Game 11.1, p. 436): draw `d ← setup n` and a uniform secret key `α : ZMod (F.order d)`, and pass
the encoded public key `pk = (d, encode (α • g))` to `adversary.choose`. If
`valid n pk m₀ m₁` holds, encrypt the selected message `m` under a fresh uniform exponent
`β : ZMod (F.order d)` via `F.add (d, encode ((α * β) • g), encodeMsg d m)` and pass the saved
state and encoded ciphertext to `adversary.guess`; otherwise output `false`, in both experiments,
as `Encryption.gameOn` does. -/
noncomputable def elGamalMsgCPAGameOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encodeMsg : F.Desc → Msg → List Bool) (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  if valid n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let ct := encPair encBits encBits
      (F.encode d (β • F.generator d),
        F.add (d, F.encode d ((α * β) • F.generator d), encodeMsg d m))
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- The DDH distinguisher constructed from a typed-message ElGamal IND-CPA adversary
([BonehShoup2023], Exercise 11.5(a), p. 459): given group parameters `d` and elements `u`, `v`,
`w`, pass the encoded public key `pk = (d, encode u)` to the adversary; if `valid n pk m₀ m₁`
holds, mask the selected encoded message `encodeMsg d m` with `encode w` using `F.add`, send the
ciphertext `(encode v, _)` and return the adversary's guess, and otherwise return `false`. -/
def elGamalMsgToDDHDistinguisher {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encodeMsg : F.Desc → Msg → List Bool)
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) : F.DDHDistinguisher :=
  fun n d u v w => do
    let pk := encPair F.encDesc encBits (d, F.encode d u)
    let choice ← adversary.choose n pk
    if valid n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
      let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
      let ct := encPair encBits encBits (F.encode d v, F.add (d, F.encode d w, encodeMsg d m))
      adversary.guess n choice.2 ct
    else
      return false

/-- In the real DDH game, `elGamalMsgToDDHDistinguisher` simulates `elGamalMsgCPAGameOn`
exactly. -/
theorem ddhRealGame_elGamalMsgToDDHDistinguisher {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (encodeMsg : F.Desc → Msg → List Bool)
    (setup : ℕ → PMF F.Desc) (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary bit) n =
      F.elGamalMsgCPAGameOn valid encodeMsg setup adversary bit n := by
  simp only [ddhRealGame, eval_ddhRealExperiment, elGamalMsgToDDHDistinguisher,
    elGamalMsgCPAGameOn, ProbComp.eval_bind, PMF.monad_bind_eq_bind, apply_ite ProbComp.eval,
    ProbComp.eval_pure, PMF.monad_pure_eq_pure]
  pmf_swap with d α choice
  split_ifs <;> first | rfl | exact PMF.bind_const _ _

/-- The admissibility predicate `valid` admits only group elements under `encodeMsg`: at every
public key `(d, u)`, an admissible pair `(m₀, m₁)` has both `encodeMsg d m₀` and `encodeMsg d m₁`
in `Set.range (F.encode d)`. -/
def AdmitsGroupElements {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (valid : ℕ → List Bool → Msg → Msg → Bool) : Prop :=
  ∀ n d u m₀ m₁, valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
    (∃ x₀ : F.Carrier d, encodeMsg d m₀ = F.encode d x₀) ∧
      (∃ x₁ : F.Carrier d, encodeMsg d m₁ = F.encode d x₁)

/-- When `valid` admits only group elements under `encodeMsg`, the uniform element `c • g` of the
random DDH game perfectly masks both admissible candidate messages, so the experiments for
`bit = false` and `bit = true` are identical. -/
theorem ddhRandomGame_elGamalMsgToDDHDistinguisher_false_eq_true {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (encodeMsg : F.Desc → Msg → List Bool)
    (setup : ℕ → PMF F.Desc) (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hsound : F.AdmitsGroupElements encodeMsg valid) :
    F.ddhRandomGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary false) n =
      F.ddhRandomGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary true) n := by
  simp only [ddhRandomGame, eval_ddhRandomExperiment, elGamalMsgToDDHDistinguisher,
    Encryption.ChoiceOut.msg₀, Encryption.ChoiceOut.msg₁, Encryption.ChoiceOut.msgs,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind, Bool.false_eq_true, ↓reduceIte,
    apply_ite ProbComp.eval, ProbComp.eval_pure]
  pmf_swap with d α β choice
  by_cases hv : valid n (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))
      choice.1.1 choice.1.2 = true
  · obtain ⟨⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩⟩ := hsound n d _ choice.1.1 choice.1.2 hv
    simp only [hv, ↓reduceIte, hx₀, hx₁, F.add_encode]
    exact (F.uniform_smul_generator_add d x₀
        (fun x => ProbComp.eval (adversary.guess n choice.2
          (encPair encBits encBits (F.encode d (β • F.generator d), F.encode d x))))).trans
      (F.uniform_smul_generator_add d x₁
        (fun x => ProbComp.eval (adversary.guess n choice.2
          (encPair encBits encBits (F.encode d (β • F.generator d), F.encode d x))))).symm
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]

/-- **Quantitative reduction of typed-message ElGamal IND-CPA to DDH** ([BonehShoup2023],
Exercise 11.5(a), p. 459): when `valid` admits only group elements under `encodeMsg`, the IND-CPA
distinguishing advantage of `adversary` is bounded by the sum of the DDH advantages of
`elGamalMsgToDDHDistinguisher valid encodeMsg adversary false` and
`elGamalMsgToDDHDistinguisher valid encodeMsg adversary true`. -/
theorem advantage_elGamalMsgCPAGameOn_le {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (encodeMsg : F.Desc → Msg → List Bool)
    (setup : ℕ → PMF F.Desc) (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hsound : F.AdmitsGroupElements encodeMsg valid) :
    Game.advantage (F.elGamalMsgCPAGameOn valid encodeMsg setup adversary false n)
      (F.elGamalMsgCPAGameOn valid encodeMsg setup adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary false) n)
        (F.ddhRandomGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary true) n)
        (F.ddhRandomGame setup
          (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary true) n) := by
  rw [← F.ddhRealGame_elGamalMsgToDDHDistinguisher valid encodeMsg setup adversary false n,
    ← F.ddhRealGame_elGamalMsgToDDHDistinguisher valid encodeMsg setup adversary true n]
  game_trans
    [F.ddhRandomGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary false) n,
     F.ddhRandomGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary true) n]
    using [le_rfl,
      F.ddhRandomGame_elGamalMsgToDDHDistinguisher_false_eq_true valid encodeMsg setup adversary n
        hsound,
      le_rfl]

/-- `elGamalMsgToDDHDistinguisher` is uniform strict PPT whenever `valid` and `encodeMsg` are
computable in polynomial time and `adversary` is uniform strict PPT. -/
theorem isPPT_elGamalMsgToDDHDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    {encodeMsg : F.Desc → Msg → List Bool}
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary bit).IsPPT := by
  let E := encPair F.encDDHInput (Encryption.encChoiceOut encMsg)
  have hpk : ComputableInPolyTime
      (fun x : F.DDHInput => encPair F.encDesc encBits (x.groupParameters, F.encode _ x.leftPublic))
      F.encDDHInput encBits :=
    ComputableInPolyTime.encoding_comp (by fun_prop)
  have hn : ComputableInPolyTime (fun p : F.DDHInput × Encryption.ChoiceOut Msg => p.1.secParam)
      E encUnary := by fun_prop
  have hd : ComputableInPolyTime
      (fun p : F.DDHInput × Encryption.ChoiceOut Msg => p.1.groupParameters) E F.encDesc := by
    fun_prop
  have hv : ComputableInPolyTime
      (fun p : F.DDHInput × Encryption.ChoiceOut Msg => F.encode _ p.1.rightPublic) E encBits := by
    fun_prop
  have hw : ComputableInPolyTime
      (fun p : F.DDHInput × Encryption.ChoiceOut Msg => F.encode _ p.1.candidateShared) E
      encBits := by
    fun_prop
  have hst : ComputableInPolyTime (fun p : F.DDHInput × Encryption.ChoiceOut Msg => p.2.2) E
      encBits := by
    fun_prop
  have hm₀ : ComputableInPolyTime (fun p : F.DDHInput × Encryption.ChoiceOut Msg => p.2.1.1) E
      encMsg := by
    fun_prop
  have hm₁ : ComputableInPolyTime (fun p : F.DDHInput × Encryption.ChoiceOut Msg => p.2.1.2) E
      encMsg := by
    fun_prop
  have hm : ComputableInPolyTime
      (fun p : F.DDHInput × Encryption.ChoiceOut Msg => if bit then p.2.1.2 else p.2.1.1) E
      encMsg := by
    cases bit
    · exact hm₀
    · exact hm₁
  have hvalidStep := (hvalid.comp (hn.prod
    ((hpk.comp (ComputableInPolyTime.fst F.encDDHInput (Encryption.encChoiceOut encMsg))).prod
      (hm₀.prod hm₁)))).tidy
  have hguessStep := hA.guess.preprocess
    (prepare := fun p : F.DDHInput × Encryption.ChoiceOut Msg =>
      (p.1.secParam, p.2.2, encPair encBits encBits
        (F.encode _ p.1.rightPublic,
          F.add (p.1.groupParameters, F.encode _ p.1.candidateShared,
            encodeMsg p.1.groupParameters (if bit then p.2.1.2 else p.2.1.1)))))
    (hn.prod (hst.prod (hv.prod (F.computableInPolyTime_add.comp
      (hd.prod (hw.prod (hencMsg.comp (hd.prod hm)))))).encoding_comp))
  simp only [DDHDistinguisher.IsPPT, elGamalMsgToDDHDistinguisher]
  refine (hA.choose.on.preprocess
    (prepare := fun x : F.DDHInput =>
      (x.secParam, encPair F.encDesc encBits (x.groupParameters, F.encode _ x.leftPublic)))
    ((show ComputableInPolyTime (fun x : F.DDHInput => x.secParam) _ encUnary by fun_prop).prod
      hpk)).bind_with ?_
  exact IsPPTOn.cond hvalidStep hguessStep (ComputableTidilyInPolyTime.const false).isPPTOn

/-- **Typed-message ElGamal encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a), p. 459): for a polynomial-time admissibility predicate `valid`
that admits only group elements under `encodeMsg`, every uniform strict PPT adversary has
negligible advantage in `elGamalMsgCPAGameOn valid encodeMsg`. -/
theorem DDH.negligible_elGamalMsgCPAGameOn {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    {Msg : Type} {encMsg : Msg ↪ List Bool} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encodeMsg : F.Desc → Msg → List Bool}
    (hDDH : F.DDH setup)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hsound : F.AdmitsGroupElements encodeMsg valid)
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage (F.elGamalMsgCPAGameOn valid encodeMsg setup adversary false n)
        (F.elGamalMsgCPAGameOn valid encodeMsg setup adversary true n) := by
  have h₀ := hDDH _ (F.isPPT_elGamalMsgToDDHDistinguisher hvalid hencMsg hA false)
  have h₁ := hDDH _ (F.isPPT_elGamalMsgToDDHDistinguisher hvalid hencMsg hA true)
  negligible using fun n =>
    F.advantage_elGamalMsgCPAGameOn_le valid encodeMsg setup adversary n hsound

/-! ### Bit encryption and IND-CPA security under DDH -/

/-- Embed a message bit `b : Bool` into `F.Carrier d` as `0` (for `false`) or `g` (for `true`). -/
def bitElement (d : F.Desc) (b : Bool) : F.Carrier d :=
  if b then F.generator d else 0

/-- Distinct message bits map to distinct group elements. -/
theorem bitElement_injective (d : F.Desc) : Function.Injective (F.bitElement d) := by
  intro b₁ b₂ h
  cases b₁ <;> cases b₂
  · rfl
  · exact absurd h.symm (F.generator_ne_zero d)
  · exact absurd h (F.generator_ne_zero d)
  · rfl

/-- Encode a message bit `b : Bool` as an encoded element of `F.Carrier d` using `F.smul`. -/
def encodeBit (d : F.Desc) (b : Bool) : List Bool :=
  F.smul (d, if b then 1 else 0, F.encode d (F.generator d))

/-- `encodeBit` computes the group encoding of `bitElement`. -/
@[simp] theorem encodeBit_eq_encode_bitElement (d : F.Desc) (b : Bool) :
    F.encodeBit d b = F.encode d (F.bitElement d b) := by
  cases b <;> simp [encodeBit, bitElement, F.smul_encode]

/-- Every pair of bit messages encodes group elements, so the always-true predicate admits only
group elements under `encodeBit`. -/
theorem admitsGroupElements_encodeBit :
    F.AdmitsGroupElements F.encodeBit (fun _ _ _ _ => true) :=
  fun _ d _ m₀ m₁ _ =>
    ⟨⟨F.bitElement d m₀, F.encodeBit_eq_encode_bitElement d m₀⟩,
     ⟨F.bitElement d m₁, F.encodeBit_eq_encode_bitElement d m₁⟩⟩

/-- `encodeBit` is computable in polynomial time from the group description and the bit. -/
theorem computableInPolyTime_encodeBit :
    ComputableInPolyTime (fun p : F.Desc × Bool => F.encodeBit p.1 p.2)
      (encPair F.encDesc encBool) encBits := by
  have hd := ComputableInPolyTime.fst F.encDesc encBool
  exact F.computableInPolyTime_smul.comp
    (hd.prod (((ComputableInPolyTime.snd F.encDesc encBool).ite' (.const 1) (.const 0)).prod
      (F.computableInPolyTime_generator.comp hd)))

/-- The IND-CPA experiment for ElGamal bit encryption ([BonehShoup2023], Exercise 11.5, p. 459):
draw `d` from `setup n` and a uniform secret key `α : ZMod (F.order d)`, pass the encoded public
key `(d, encode (α • g))` to `adversary.choose`, encrypt the selected challenge bit under a fresh
uniform exponent `β : ZMod (F.order d)`, and pass the saved state and encoded ciphertext to
`adversary.guess`. -/
noncomputable def elGamalCPAGame (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d),
      F.encode d ((α * β) • F.generator d + F.bitElement d m))
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- `elGamalCPAGame` is the unrestricted `encodeBit` specialization of `elGamalMsgCPAGameOn`. -/
theorem elGamalCPAGame_eq_elGamalMsgCPAGameOn (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    F.elGamalCPAGame setup adversary bit n =
      F.elGamalMsgCPAGameOn (fun _ _ _ _ => true) F.encodeBit setup adversary bit n := by
  simp only [elGamalCPAGame, elGamalMsgCPAGameOn, ↓reduceIte, F.encodeBit_eq_encode_bitElement,
    F.add_encode]

/-- IND-CPA security of ElGamal bit encryption over `F` for a setup law `setup`: every uniform
strict PPT `Encryption.Adversary` has negligible distinguishing advantage between challenge bit
`false` and challenge bit `true`. -/
def elGamalINDCPA (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.elGamalCPAGame setup adversary false n)
    (fun adversary n => F.elGamalCPAGame setup adversary true n)
    Encryption.Adversary.IsPPT

/-- The DDH distinguisher constructed from an IND-CPA adversary ([BonehShoup2023], proof of
Exercise 11.5(a), p. 459): given group parameters `d` and elements `u`, `v`, `w`, pass the encoded
public key `(d, encode u)` to the adversary, mask the encoded challenge bit with `encode w` using
`F.add`, send the ciphertext `(encode v, _)` and return the adversary's guess. It is the
unrestricted `encodeBit` instance of `elGamalMsgToDDHDistinguisher`. -/
abbrev elGamalToDDHDistinguisher (adversary : Encryption.Adversary) (bit : Bool) :
    F.DDHDistinguisher :=
  F.elGamalMsgToDDHDistinguisher (fun _ _ _ _ => true) F.encodeBit adversary bit

/-- In the real DDH game, `elGamalToDDHDistinguisher` simulates `elGamalCPAGame` exactly. -/
@[simp] theorem ddhRealGame_elGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary bit) n =
      F.elGamalCPAGame setup adversary bit n := by
  rw [F.ddhRealGame_elGamalMsgToDDHDistinguisher, F.elGamalCPAGame_eq_elGamalMsgCPAGameOn]

/-- In the random DDH game, the uniform element `c • g` perfectly masks the challenge bit, so the
experiments for `bit = false` and `bit = true` are identical. -/
theorem ddhRandomGame_elGamalToDDHDistinguisher_false_eq_true (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    F.ddhRandomGame setup (F.elGamalToDDHDistinguisher adversary false) n =
      F.ddhRandomGame setup (F.elGamalToDDHDistinguisher adversary true) n :=
  F.ddhRandomGame_elGamalMsgToDDHDistinguisher_false_eq_true _ F.encodeBit setup adversary n
    F.admitsGroupElements_encodeBit

/-- **Quantitative reduction of ElGamal IND-CPA to DDH** ([BonehShoup2023], Exercise 11.5(a),
p. 459): the IND-CPA distinguishing advantage of `adversary` is bounded by the sum of the DDH
advantages of `elGamalToDDHDistinguisher adversary false` and
`elGamalToDDHDistinguisher adversary true`. -/
theorem advantage_elGamalCPAGame_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    Game.advantage (F.elGamalCPAGame setup adversary false n)
      (F.elGamalCPAGame setup adversary true n) ≤
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary false) n)
        (F.ddhRandomGame setup (F.elGamalToDDHDistinguisher adversary false) n) +
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary true) n)
        (F.ddhRandomGame setup (F.elGamalToDDHDistinguisher adversary true) n) := by
  rw [F.elGamalCPAGame_eq_elGamalMsgCPAGameOn, F.elGamalCPAGame_eq_elGamalMsgCPAGameOn]
  exact F.advantage_elGamalMsgCPAGameOn_le _ F.encodeBit setup adversary n
    F.admitsGroupElements_encodeBit

/-- `elGamalToDDHDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPT_elGamalToDDHDistinguisher {adversary : Encryption.Adversary}
    (hA : adversary.IsPPT) (bit : Bool) : (F.elGamalToDDHDistinguisher adversary bit).IsPPT :=
  F.isPPT_elGamalMsgToDDHDistinguisher
    (ComputableTidilyInPolyTime.const true).computableInPolyTime F.computableInPolyTime_encodeBit hA
    bit

/-- **ElGamal bit encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a), p. 459). -/
theorem DDH.elGamalINDCPA {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) : F.elGamalINDCPA setup := by
  intro adversary hA
  have h₀ := hDDH _ (F.isPPT_elGamalToDDHDistinguisher hA false)
  have h₁ := hDDH _ (F.isPPT_elGamalToDDHDistinguisher hA true)
  negligible using F.advantage_elGamalCPAGame_le setup adversary

/-! ### Group-element ElGamal IND-CPA security under DDH -/

/-- The IND-CPA experiment for group-element ElGamal encryption with challenge-pair admissibility
predicate `valid` ([BonehShoup2023], Exercise 11.5(a), p. 459): specialization of
`elGamalMsgCPAGameOn` to word messages (`Encryption.WordAdversary`) with identity message
encoding. The message space of Exercise 11.5 is the group, so `valid` is meant to admit only
encoded group elements (`AdmitsGroupElements (fun _ m => m) valid`). -/
noncomputable abbrev elGamalGroupCPAGameOn (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (setup : ℕ → PMF F.Desc) (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game :=
  F.elGamalMsgCPAGameOn valid (fun _ m => m) setup adversary bit n

/-- The DDH distinguisher constructed from a group-element ElGamal IND-CPA adversary
([BonehShoup2023], Exercise 11.5(a), p. 459): specialization of `elGamalMsgToDDHDistinguisher` to
identity message encoding. -/
abbrev elGamalGroupToDDHDistinguisher (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (adversary : Encryption.WordAdversary) (bit : Bool) : F.DDHDistinguisher :=
  F.elGamalMsgToDDHDistinguisher valid (fun _ m => m) adversary bit

/-- **Quantitative reduction of group-element ElGamal IND-CPA to DDH** ([BonehShoup2023],
Exercise 11.5(a), p. 459): when `valid` admits only encoded group elements, the IND-CPA
distinguishing advantage of `adversary` is bounded by the sum of the DDH advantages of
`elGamalGroupToDDHDistinguisher valid adversary false` and
`elGamalGroupToDDHDistinguisher valid adversary true`. -/
theorem advantage_elGamalGroupCPAGameOn_le
    (valid : ℕ → List Bool → List Bool → List Bool → Bool) (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (n : ℕ)
    (hsound : F.AdmitsGroupElements (fun _ m => m) valid) :
    Game.advantage (F.elGamalGroupCPAGameOn valid setup adversary false n)
      (F.elGamalGroupCPAGameOn valid setup adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher valid adversary false) n)
        (F.ddhRandomGame setup (F.elGamalGroupToDDHDistinguisher valid adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher valid adversary true) n)
        (F.ddhRandomGame setup (F.elGamalGroupToDDHDistinguisher valid adversary true) n) :=
  F.advantage_elGamalMsgCPAGameOn_le valid (fun _ m => m) setup adversary n hsound

/-- **Group-element ElGamal encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a), p. 459): for a polynomial-time admissibility predicate `valid`
that admits only encoded group elements, every uniform strict PPT `Encryption.WordAdversary` has
negligible advantage in `elGamalGroupCPAGameOn valid`. -/
theorem DDH.negligible_elGamalGroupCPAGameOn {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hDDH : F.DDH setup)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool)
    (hsound : F.AdmitsGroupElements (fun _ m => m) valid)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) :
    Negligible fun n =>
      Game.advantage (F.elGamalGroupCPAGameOn valid setup adversary false n)
        (F.elGamalGroupCPAGameOn valid setup adversary true n) :=
  hDDH.negligible_elGamalMsgCPAGameOn hvalid hsound (.snd F.encDesc encBits) hA

/-! ### Hashed ElGamal encryption and IND-CPA security ([BonehShoup2023], Section 11.5) -/

/-- Algebraic Hashed ElGamal encryption ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1):
given key-derivation hash function `H : F.Desc × List Bool → List Bool`, public key
`u : F.Carrier d`, message word `m : List Bool`, and randomness `β : ZMod (F.order d)`, derive
`pad = H (d, encode (β • u))` and output
`(β • g, Cslib.BitString.listXor pad.length [pad, m])`. -/
def hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool) (d : F.Desc) (u : F.Carrier d)
    (m : List Bool) (β : ZMod (F.order d)) : F.Carrier d × List Bool :=
  let pad := H (d, F.encode d (β • u))
  (β • F.generator d, Cslib.BitString.listXor pad.length [pad, m])

/-- Under a genuine public key `u = α • g`, Hashed ElGamal masks `m` with
`pad = H (d, encode ((α * β) • g))` via `Cslib.BitString.listXor pad.length [pad, m]`. -/
theorem hashedElGamalEncrypt_smul_generator (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α β : ZMod (F.order d)) (m : List Bool) :
    F.hashedElGamalEncrypt H d (α • F.generator d) m β =
      let pad := H (d, F.encode d ((α * β) • F.generator d))
      (β • F.generator d, Cslib.BitString.listXor pad.length [pad, m]) := by
  simp only [hashedElGamalEncrypt, smul_smul, mul_comm β α]

/-- Algebraic Hashed ElGamal decryption ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1):
given secret key `α : ZMod (F.order d)` and ciphertext `(v, c)`, derive
`pad = H (d, encode (α • v))` and recover `Cslib.BitString.listXor pad.length [pad, c]`. -/
def hashedElGamalDecrypt (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α : ZMod (F.order d)) (ct : F.Carrier d × List Bool) : List Bool :=
  let pad := H (d, F.encode d (α • ct.1))
  Cslib.BitString.listXor pad.length [pad, ct.2]

/-- **Hashed ElGamal decryption correctness**: when the message word `m` has the same length as the
derived pad `H (d, encode ((α * β) • g))`, decrypting an encryption under `u = α • g` with secret
key `α` recovers `m`. -/
@[simp] theorem hashedElGamalDecrypt_hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (α β : ZMod (F.order d)) {m : List Bool}
    (hlen : m.length = (H (d, F.encode d ((α * β) • F.generator d))).length) :
    F.hashedElGamalDecrypt H d α (F.hashedElGamalEncrypt H d (α • F.generator d) m β) = m := by
  simp only [hashedElGamalDecrypt, hashedElGamalEncrypt_smul_generator, smul_smul]
  exact Cslib.BitString.listXor_pair_self_left_of_length _ hlen

/-- Word-level Hashed ElGamal encryption: given `(d, encode u, m, b)`, derive
`pad = H (d, encode (b • u))` and compute
`(encode (b • g), Cslib.BitString.listXor pad.length [pad, m])`. -/
def encodeHashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (input : F.Desc × List Bool × List Bool × ℕ) : List Bool × List Bool :=
  let pad := H (input.1, F.smul (input.1, F.encRand input, F.encPk input))
  (F.smul (input.1, F.encRand input, F.encode input.1 (F.generator input.1)),
    Cslib.BitString.listXor pad.length [pad, F.encMsg input])

/-- `encodeHashedElGamalEncrypt` evaluates `hashedElGamalEncrypt` on encoded group elements. -/
@[simp] theorem encodeHashedElGamalEncrypt_encode (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (u : F.Carrier d) (m : List Bool) (b : ℕ) :
    F.encodeHashedElGamalEncrypt H (d, F.encode d u, m, b) =
      (F.encode d (F.hashedElGamalEncrypt H d u m (b : ZMod (F.order d))).1,
        (F.hashedElGamalEncrypt H d u m (b : ZMod (F.order d))).2) := by
  simp only [encodeHashedElGamalEncrypt, hashedElGamalEncrypt, F.smul_encode]

private theorem computableInPolyTime_listXor_pair {α : Type} {encIn : α ↪ List Bool}
    {pad msg : α → List Bool}
    (hpad : ComputableInPolyTime pad encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    ComputableInPolyTime
      (fun a => Cslib.BitString.listXor (pad a).length [pad a, msg a])
      encIn encBits :=
  .bitsXorWithInput ((ComputableInPolyTime.encoding_length encBits).comp hpad)
    (hpad.cons' (hmsg.cons' (.const [])))

/-- Word-level Hashed ElGamal encryption is computable in polynomial time whenever `H` is. -/
theorem computableInPolyTime_encodeHashedElGamalEncrypt {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    ComputableInPolyTime (F.encodeHashedElGamalEncrypt H)
      (encPair F.encDesc (encPair encBits (encPair encBits encNat)))
      (encPair encBits encBits) := by
  have hd := ComputableInPolyTime.fst F.encDesc (encPair encBits (encPair encBits encNat))
  have h2 := ComputableInPolyTime.snd F.encDesc (encPair encBits (encPair encBits encNat))
  have hu := (ComputableInPolyTime.fst encBits (encPair encBits encNat)).comp h2
  have h3 := (ComputableInPolyTime.snd encBits (encPair encBits encNat)).comp h2
  have hm := (ComputableInPolyTime.fst encBits encNat).comp h3
  have hb := (ComputableInPolyTime.snd encBits encNat).comp h3
  have hg := F.computableInPolyTime_generator.comp hd
  have hv := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hg))
  have hbu := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hu))
  have hpad := hH.comp (hd.prod hbu)
  exact hv.prod (computableInPolyTime_listXor_pair hpad hm)

/-- Word-level Hashed ElGamal decryption: given `(d, a, encode v, c)`, derive
`pad = H (d, encode (a • v))` and compute `Cslib.BitString.listXor pad.length [pad, c]`. -/
def decodeHashedElGamal (H : F.Desc × List Bool → List Bool)
    (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  let pad := H (input.1, F.smul (input.1, F.decSk input, F.decEph input))
  Cslib.BitString.listXor pad.length [pad, F.decBody input]

/-- `decodeHashedElGamal` computes `hashedElGamalDecrypt` on encoded group elements. -/
@[simp] theorem decodeHashedElGamal_encode (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (a : ℕ) (v : F.Carrier d) (c : List Bool) :
    F.decodeHashedElGamal H (d, a, F.encode d v, c) =
      F.hashedElGamalDecrypt H d (a : ZMod (F.order d)) (v, c) := by
  simp only [decodeHashedElGamal, hashedElGamalDecrypt, F.smul_encode]

/-- Word-level Hashed ElGamal decryption of an honest encryption recovers `m` whenever `m` has the
same length as the derived pad. -/
theorem decodeHashedElGamal_hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (a : ℕ) (β : ZMod (F.order d)) {m : List Bool}
    (hlen :
      m.length =
        (H (d, F.encode d (((a : ZMod (F.order d)) * β) • F.generator d))).length) :
    F.decodeHashedElGamal H (d, a,
      F.encode d (F.hashedElGamalEncrypt H d ((a : ZMod (F.order d)) • F.generator d) m β).1,
      (F.hashedElGamalEncrypt H d ((a : ZMod (F.order d)) • F.generator d) m β).2) = m := by
  rw [F.decodeHashedElGamal_encode, F.hashedElGamalDecrypt_hashedElGamalEncrypt H d _ β hlen]

/-- Word-level Hashed ElGamal decryption is computable in polynomial time whenever `H` is. -/
theorem computableInPolyTime_decodeHashedElGamal {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    ComputableInPolyTime (F.decodeHashedElGamal H)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by
  have hd := ComputableInPolyTime.fst F.encDesc (encPair encNat (encPair encBits encBits))
  have h2 := ComputableInPolyTime.snd F.encDesc (encPair encNat (encPair encBits encBits))
  have ha := (ComputableInPolyTime.fst encNat (encPair encBits encBits)).comp h2
  have h3 := (ComputableInPolyTime.snd encNat (encPair encBits encBits)).comp h2
  have hv := (ComputableInPolyTime.fst encBits encBits).comp h3
  have hc := (ComputableInPolyTime.snd encBits encBits).comp h3
  have hav := F.computableInPolyTime_smul.comp (hd.prod (ha.prod hv))
  exact computableInPolyTime_listXor_pair (hH.comp (hd.prod hav)) hc

/-- The IND-CPA experiment for Hashed ElGamal encryption ([BonehShoup2023], Section 11.5,
pp. 445–446, Remark 11.1, and Section 11.5.2, Theorem 11.5, pp. 449–451): draw `d ← setup n` and a
uniform secret key `α : ZMod (F.order d)`, pass the encoded public key `(d, encode (α • g))` to
`adversary.choose`, encrypt the selected message word `m` under a fresh uniform exponent
`β : ZMod (F.order d)` by masking with `pad = H (d, encode ((α * β) • g))` via
`Cslib.BitString.listXor pad.length [pad, m]`, and pass the saved state and encoded ciphertext to
`adversary.guess`. -/
noncomputable def hashedElGamalCPAGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad := H (d, F.encode d ((α * β) • F.generator d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d), Cslib.BitString.listXor pad.length [pad, m])
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- A key-derivation distinguisher over the family ([BonehShoup2023], Section 11.5.2, Attack
Game 11.3, p. 448): given the security parameter, public group parameters `d`, two elements of
`F.Carrier d` and a candidate key word, it outputs a bit. `SecureKDF` states its efficiency on
encodings. -/
abbrev KDFDistinguisher : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → List Bool → ProbComp Bool

/-- The real key-derivation security experiment ([BonehShoup2023], Section 11.5.2, Attack Game 11.3,
Experiment `0`, p. 448): draw `d ← setup n` and independent uniform `a, b, c : ZMod (F.order d)`,
and give the distinguisher `a • g`, `b • g` and the derived key `H (d, encode (c • g))`. -/
noncomputable def kdfRealGame (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (distinguisher : F.KDFDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let a ← PMF.uniformOfFintype (ZMod (F.order d))
  let b ← PMF.uniformOfFintype (ZMod (F.order d))
  let c ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n d (a • F.generator d) (b • F.generator d)
    (H (d, F.encode d (c • F.generator d))))

/-- The ideal key-derivation security experiment ([BonehShoup2023], Section 11.5.2,
Attack Game 11.3, Experiment `1`, p. 448): draw `d ← setup n`, independent uniform
`a, b : ZMod (F.order d)` and an independent uniform `msgLen n`-bit key
`key ← Cslib.BitString.uniformList (msgLen n)`, and give the distinguisher `a • g`, `b • g` and
`key`. -/
noncomputable def kdfIdealGame (setup : ℕ → PMF F.Desc) (msgLen : ℕ → ℕ)
    (distinguisher : F.KDFDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let a ← PMF.uniformOfFintype (ZMod (F.order d))
  let b ← PMF.uniformOfFintype (ZMod (F.order d))
  let key ← Cslib.BitString.uniformList (msgLen n)
  ProbComp.eval (distinguisher n d (a • F.generator d) (b • F.generator d) key)

/-- The input of a key-derivation distinguisher: a CDH input and a candidate key word, which is
`H (d, encode (c • g))` in the real experiment and uniform in the ideal one. -/
structure KDFInput extends F.CDHInput where
  /-- The candidate key word. -/
  key : List Bool

/-- The encoding of a key-derivation input: the fields of its CDH input followed by the key word,
each framed except the last. This is the layout of `encDDHInput` with the key word in place of the
encoded candidate shared element. -/
enc_structure encKDFInput (F : PrimeOrderGroupFamily) : KDFInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  leftPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  rightPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  key : encBits

variable {F} in
/-- A key-derivation distinguisher is uniform strict PPT: one machine reading the `encKDFInput`
encoding of its security parameter, group parameters, two group elements and key word realizes
it. -/
def KDFDistinguisher.IsPPT (distinguisher : F.KDFDistinguisher) : Prop :=
  IsPPTOn F.encKDFInput encBool fun x =>
    distinguisher x.secParam x.groupParameters x.leftPublic x.rightPublic x.key

variable {F} in
/-- A PPT key-derivation distinguisher run on computed inputs is uniform strict PPT. -/
theorem KDFDistinguisher.IsPPT.comp {distinguisher : F.KDFDistinguisher}
    (hD : distinguisher.IsPPT)
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    {u v : (a : α) → F.Carrier (d a)} {key : α → List Bool}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => F.encode (d a) (v a)) enc encBits)
    (hkey : ComputableInPolyTime key enc encBits) :
    IsPPTOn enc encBool fun a => distinguisher (n a) (d a) (u a) (v a) (key a) :=
  IsPPTOn.preprocess hD (F.encKDFInput_mk_polyTime hn hd hu hv hkey)

/-- Secure key derivation for `H` over `F` ([BonehShoup2023], Section 11.5.2, Attack Game 11.3,
p. 448, and Definition 11.5, p. 449): every uniform strict PPT key-derivation distinguisher
(`KDFDistinguisher.IsPPT`) has negligible advantage between `kdfRealGame` and `kdfIdealGame`. No
nondegenerate `SecureKDF` instance (`msgLen n > 0`, e.g., via the leftover hash lemma) is
constructed in this module. -/
def SecureKDF (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ) : Prop :=
  Game.Indistinguishable (F.kdfRealGame setup H) (F.kdfIdealGame setup msgLen)
    KDFDistinguisher.IsPPT

/-- **`SecureKDF` is the word-level key-derivation assumption.** Quantifying over distinguishers
that read `(1ⁿ, d, encode u, encode v, key)` as words, each with one uniform strict PPT machine on
its flat layout, gives the same assumption as quantifying over typed distinguishers, as for DDH
(`ddh_iff_encoded`). -/
theorem secureKDF_iff_encoded (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ) :
    F.SecureKDF setup H msgLen ↔
      ∀ W : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool,
        IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
          encBool (fun x => W x.1 x.2) →
        Negligible fun n => Game.advantage
          (F.kdfRealGame setup H (fun n d u v key => W n (d, F.encode d u, F.encode d v, key)) n)
          (F.kdfIdealGame setup msgLen
            (fun n d u v key => W n (d, F.encode d u, F.encode d v, key)) n) := by
  set E := encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  constructor
  · intro h W hW
    exact h _ (hW.preprocess (prepare := fun x : F.KDFInput => (x.secParam, x.groupParameters,
      F.encode _ x.leftPublic, F.encode _ x.rightPublic, x.key)) (by fun_prop))
  · intro h D hD
    obtain ⟨W, hWppt, hW⟩ := hD.exists_bool_extension
    have := h (fun n t => W (E (n, t))) (hWppt.preprocess ComputableInPolyTime.id'.encoding_comp)
    have hgame (n : ℕ) (d : F.Desc) (u v : F.Carrier d) (key : List Bool) :
        ProbComp.eval (W (E (n, d, F.encode d u, F.encode d v, key))) =
          ProbComp.eval (D n d u v key) :=
      hW ⟨⟨n, d, u, v⟩, key⟩
    simpa only [kdfRealGame, kdfIdealGame, hgame] using this

/-- Run a key-derivation distinguisher as a DDH distinguisher: derive the candidate key
`H (d, encode w)` from the candidate shared element `w`. -/
def kdfToDDHDistinguisher (H : F.Desc × List Bool → List Bool)
    (distinguisher : F.KDFDistinguisher) : F.DDHDistinguisher :=
  fun n d u v w => distinguisher n d u v (H (d, F.encode d w))

/-- In the random DDH game, `kdfToDDHDistinguisher H` runs the real key-derivation game. -/
@[simp] theorem ddhRandomGame_kdfToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (distinguisher : F.KDFDistinguisher) (n : ℕ) :
    F.ddhRandomGame setup (F.kdfToDDHDistinguisher H distinguisher) n =
      F.kdfRealGame setup H distinguisher n := by
  simp only [ddhRandomGame, eval_ddhRandomExperiment, kdfToDDHDistinguisher, kdfRealGame,
    PMF.monad_bind_eq_bind]

/-- `kdfToDDHDistinguisher H` is uniform strict PPT whenever `H` is polynomial time and the
key-derivation distinguisher is uniform strict PPT. -/
theorem isPPT_kdfToDDHDistinguisher {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {distinguisher : F.KDFDistinguisher} (hD : distinguisher.IsPPT) :
    (F.kdfToDDHDistinguisher H distinguisher).IsPPT :=
  hD.comp (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (hH.comp (by fun_prop))

/-- The KDF distinguisher constructed from a Hashed ElGamal IND-CPA adversary ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, pp. 449–451): given `(d, u, v, pad)`, pass `(d, encode u)`
as the public key, mask the selected message word with `pad` via
`Cslib.BitString.listXor pad.length [pad, m]`, send the ciphertext `(encode v, _)` and return the
adversary's guess. -/
def hashedElGamalToKDFDistinguisher (adversary : Encryption.WordAdversary) (bit : Bool) :
    F.KDFDistinguisher :=
  fun n d u v pad => do
    let pk := encPair F.encDesc encBits (d, F.encode d u)
    let choice ← adversary.choose n pk
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
    let ct := encPair encBits encBits
      (F.encode d v, Cslib.BitString.listXor pad.length [pad, m])
    adversary.guess n choice.2 ct

/-- The DDH distinguisher constructed from a Hashed ElGamal IND-CPA adversary ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, pp. 449–451): `hashedElGamalToKDFDistinguisher` run with
the pad `H (d, encode w)` derived from the candidate shared element `w`. -/
abbrev hashedElGamalToDDHDistinguisher (H : F.Desc × List Bool → List Bool)
    (adversary : Encryption.WordAdversary) (bit : Bool) : F.DDHDistinguisher :=
  F.kdfToDDHDistinguisher H (F.hashedElGamalToKDFDistinguisher adversary bit)

/-- In the real DDH game, `hashedElGamalToDDHDistinguisher` simulates `hashedElGamalCPAGame`
exactly. -/
@[simp] theorem ddhRealGame_hashedElGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary bit) n =
      F.hashedElGamalCPAGame setup H adversary bit n := by
  simp only [ddhRealGame, eval_ddhRealExperiment, kdfToDDHDistinguisher,
    hashedElGamalToKDFDistinguisher, hashedElGamalCPAGame, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  pmf_swap

/-- `hashedElGamalToKDFDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPT_hashedElGamalToKDFDistinguisher {adversary : Encryption.WordAdversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    (F.hashedElGamalToKDFDistinguisher adversary bit).IsPPT := by
  let E := encPair F.encKDFInput (Encryption.encChoiceOut encBits)
  have hm : ComputableInPolyTime
      (fun p : F.KDFInput × Encryption.ChoiceOut (List Bool) =>
        if bit then p.2.1.2 else p.2.1.1) E encBits :=
    .ite' (encC := encBool) (.const bit) (by fun_prop) (by fun_prop)
  simp only [KDFDistinguisher.IsPPT, hashedElGamalToKDFDistinguisher]
  refine (hA.choose.on.preprocess
    (prepare := fun x : F.KDFInput =>
      (x.secParam, encPair F.encDesc encBits (x.groupParameters, F.encode _ x.leftPublic)))
    (.prod (by fun_prop) (.encoding_comp (by fun_prop)))).bind_with ?_
  exact hA.guess.preprocess
    (prepare := fun p : F.KDFInput × Encryption.ChoiceOut (List Bool) =>
      (p.1.secParam, p.2.2, encPair encBits encBits
        (F.encode _ p.1.rightPublic,
          Cslib.BitString.listXor p.1.key.length [p.1.key, if bit then p.2.1.2 else p.2.1.1])))
    (.prod (by fun_prop) (.prod (by fun_prop)
      (.encoding_comp (.prod (by fun_prop) (computableInPolyTime_listXor_pair (by fun_prop) hm)))))

/-- In `kdfIdealGame`, the uniform `msgLen n`-bit pad masks any challenge message word perfectly
via `Cslib.BitString.listXor pad.length [pad, m]`, so `hashedElGamalToKDFDistinguisher` accepts
with the same law for `bit = false` and `bit = true`. -/
theorem kdfIdealGame_hashedElGamalToKDFDistinguisher_false_eq_true (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : Encryption.WordAdversary) (n : ℕ) :
    F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary false) n =
      F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary true) n := by
  simp only [kdfIdealGame, hashedElGamalToKDFDistinguisher, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind, Bool.false_eq_true, ↓reduceIte]
  refine congrArg (PMF.bind _) (funext fun d => congrArg (PMF.bind _) (funext fun α => ?_))
  refine congrArg (PMF.bind _) (funext fun β => ?_)
  rw [PMF.bind_comm, PMF.bind_comm (Cslib.BitString.uniformList (msgLen n))]
  refine congrArg (PMF.bind _) (funext fun choice => ?_)
  have hpad (m : List Bool) :
      ((Cslib.BitString.uniformList (msgLen n)).bind fun pad =>
        ProbComp.eval (adversary.guess n choice.2
          (encPair encBits encBits
            (F.encode d (β • F.generator d),
              Cslib.BitString.listXor pad.length [pad, m])))) =
      ((Cslib.BitString.uniformList (msgLen n)).bind fun pad =>
        ProbComp.eval (adversary.guess n choice.2
          (encPair encBits encBits (F.encode d (β • F.generator d), pad)))) := by
    have hmap := congrArg
      (fun p : PMF (List Bool) =>
        p.bind fun pad =>
          ProbComp.eval (adversary.guess n choice.2
            (encPair encBits encBits (F.encode d (β • F.generator d), pad))))
      (Cslib.BitString.uniformList_map_listXor_length (msgLen n) m)
    simpa only [PMF.bind_map, Function.comp_def] using hmap
  exact (hpad choice.1.1).trans (hpad choice.1.2).symm

/-- **Quantitative reduction of Hashed ElGamal IND-CPA to DDH and `SecureKDF`**
([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451): the IND-CPA distinguishing
advantage of `adversary` is bounded by the sum of the two DDH advantages of
`hashedElGamalToDDHDistinguisher` and the two KDF advantages of
`hashedElGamalToKDFDistinguisher`. The hybrids of the proof are the random DDH game, which is the
real KDF game (`ddhRandomGame_kdfToDDHDistinguisher`), and the ideal KDF game, where the uniform
pad hides the challenge bit. -/
theorem advantage_hashedElGamalCPAGame_le (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (adversary : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
      (F.hashedElGamalCPAGame setup H adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary false) n)
        (F.ddhRandomGame setup (F.hashedElGamalToDDHDistinguisher H adversary false) n) +
      Game.advantage
        (F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary false) n)
        (F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary false) n) +
      Game.advantage
        (F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary true) n)
        (F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary true) n) +
      Game.advantage
        (F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary true) n)
        (F.ddhRandomGame setup (F.hashedElGamalToDDHDistinguisher H adversary true) n) := by
  simp only [ddhRealGame_hashedElGamalToDDHDistinguisher, ddhRandomGame_kdfToDDHDistinguisher]
  game_trans
    [F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary false) n,
     F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary false) n,
     F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary true) n,
     F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary true) n]
    using [le_rfl, le_rfl,
      F.kdfIdealGame_hashedElGamalToKDFDistinguisher_false_eq_true setup msgLen adversary n,
      le_rfl, le_rfl]

/-- **Hashed ElGamal encryption is IND-CPA secure under DDH and `SecureKDF`**
([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451): when `H` is computable in
polynomial time, every uniform strict PPT `Encryption.WordAdversary` has negligible IND-CPA
distinguishing advantage. Note that `SecureKDF` is assumed as a hypothesis; no nondegenerate
`SecureKDF` instance (`msgLen n > 0`) is constructed in this module. -/
theorem DDH.negligible_hashedElGamalCPAGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool} {msgLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hKDF : F.SecureKDF setup H msgLen)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) :
    Negligible fun n =>
      Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
        (F.hashedElGamalCPAGame setup H adversary true n) := by
  have hkdf₀ := hKDF _ (F.isPPT_hashedElGamalToKDFDistinguisher hA false)
  have hkdf₁ := hKDF _ (F.isPPT_hashedElGamalToKDFDistinguisher hA true)
  have hddh₀ := hDDH _ (F.isPPT_kdfToDDHDistinguisher hH
    (F.isPPT_hashedElGamalToKDFDistinguisher hA false))
  have hddh₁ := hDDH _ (F.isPPT_kdfToDDHDistinguisher hH
    (F.isPPT_hashedElGamalToKDFDistinguisher hA true))
  negligible using F.advantage_hashedElGamalCPAGame_le setup H msgLen adversary

end Cslib.Crypto.PrimeOrderGroupFamily
