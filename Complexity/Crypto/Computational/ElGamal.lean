/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiffieHellman
public import Complexity.Crypto.Computational.Encryption.Basic
public import Complexity.Probability.BitString.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

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
   `isPPTOn_elGamalMsgToDDHDistinguisher`, `DDH.negligible_elGamalMsgCPAGameOn`). As in
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
`Complexity/Crypto/Computational/ElGamal/ProbComp.lean`; non-degenerate `SecureKDF` instantiation
(`msgLen n > 0`) via `BitString.LinearHash` and the leftover hash lemma is provided in
`Complexity/Crypto/Computational/ElGamal/KDF.lean`.

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
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalIdealDDHGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalUniformPadGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kdfRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kdfIdealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.SecureKDF`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalToKDFDistinguisher`: Hashed ElGamal IND-CPA
  experiments, hybrids, and reductions ([BonehShoup2023], Section 11.5.2, Attack Game 11.3,
  Definition 11.5, and Theorem 11.5, pp. 448–451).

## Main results

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
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_elGamalMsgToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_elGamalMsgCPAGameOn`: shared typed-message
  ElGamal IND-CPA reduction to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_elGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.elGamalINDCPA`: ElGamal IND-CPA security for bit
  messages under DDH ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalGroupCPAGameOn_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_elGamalGroupCPAGameOn`: ElGamal IND-CPA
  security for group-element messages under DDH ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecrypt_hashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeHashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_decodeHashedElGamal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_hashedElGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_hashedElGamalToKDFDistinguisher`,
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
  have hd : ComputableInPolyTime (fun input : F.Desc × ℕ => input.1)
      (encPair F.encDesc encNat) F.encDesc := by fun_prop
  have ha : ComputableInPolyTime (fun input : F.Desc × ℕ => input.2)
      (encPair F.encDesc encNat) encNat := by fun_prop
  have hg := F.computableInPolyTime_generator.comp hd
  exact F.computableInPolyTime_smul.comp (hd.prod (ha.prod hg))

/-- Word-level ElGamal encryption: given `(d, encode u, encode m, b)`, compute
`(encode (b • g), encode (b • u + m))`. -/
def encodeElGamalEncrypt (input : F.Desc × List Bool × List Bool × ℕ) : List Bool × List Bool :=
  let d := input.1
  let u := input.2.1
  let m := input.2.2.1
  let b := input.2.2.2
  (F.smul (d, b, F.encode d (F.generator d)),
    F.add (d, F.smul (d, b, u), m))

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
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits encNat))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.1) encIn F.encDesc := by fun_prop
  have hu : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.1) encIn encBits := by fun_prop
  have hm : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.2.1) encIn encBits := by fun_prop
  have hb : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.2.2) encIn encNat := by fun_prop
  have hg := F.computableInPolyTime_generator.comp hd
  have hv := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hg))
  have hbu := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hu))
  have he := F.computableInPolyTime_add.comp (hd.prod (hbu.prod hm))
  exact hv.prod he

/-- Decryption on encoded group elements: given `(d, a, encode v, encode e)`, compute
`encode (e - a • v)` as `F.add (d, encode e, F.smul (d, F.order d - a % F.order d, encode v))`. -/
def decodeElGamal (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  F.add (input.1, input.2.2.2,
    F.smul (input.1, F.order input.1 - input.2.1 % F.order input.1, input.2.2.1))

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
  have hd : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) F.encDesc := by fun_prop
  have ha : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat := by fun_prop
  have hv : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by fun_prop
  have he : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by fun_prop
  have horder : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => F.order input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat :=
    F.computableInPolyTime_order.tidy.comp hd
  have hexp : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool =>
        F.order input.1 - input.2.1 % F.order input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat :=
    .binary_sub' horder (.binary_mod' ha horder)
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
  if valid n pk choice.1.1 choice.1.2 then
    let m := if bit then choice.1.2 else choice.1.1
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let ct := encPair encBits encBits
      (F.encode d (β • F.generator d),
        F.add (d, F.encode d ((α * β) • F.generator d), encodeMsg d m))
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- The DDH distinguisher constructed from a typed-message ElGamal IND-CPA adversary
([BonehShoup2023], Exercise 11.5(a), p. 459): given `(d, u, v, w)`, pass `pk = (d, u)` as the
public key; if `valid n pk m₀ m₁` holds, mask the selected encoded message `encodeMsg d m` with `w`
using `F.add` and return the adversary's guess, and otherwise return `false`. -/
def elGamalMsgToDDHDistinguisher {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encodeMsg : F.Desc → Msg → List Bool)
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  if valid n pk choice.1.1 choice.1.2 then
    let m := if bit then choice.1.2 else choice.1.1
    let ct := encPair encBits encBits
      (input.2.2.1, F.add (input.1, input.2.2.2, encodeMsg input.1 m))
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
  simp only [ddhRealGame, elGamalMsgToDDHDistinguisher, elGamalMsgCPAGameOn, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind, apply_ite ProbComp.eval, ProbComp.eval_pure, PMF.monad_pure_eq_pure]
  congr 1; funext d
  congr 1; funext α
  rw [PMF.bind_comm]
  congr 1; funext choice
  split_ifs <;> first | rfl | exact PMF.bind_const _ _

/-- The admissibility predicate `valid` admits only group elements under `encodeMsg`: at every
public key `(d, u)`, an admissible pair `(m₀, m₁)` has both `encodeMsg d m₀` and `encodeMsg d m₁`
in `Set.range (F.encode d)`. -/
def AdmitsGroupElements {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (valid : ℕ → List Bool → Msg → Msg → Bool) : Prop :=
  ∀ n d u m₀ m₁, valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
    (∃ x₀ : F.Carrier d, encodeMsg d m₀ = F.encode d x₀) ∧
      (∃ x₁ : F.Carrier d, encodeMsg d m₁ = F.encode d x₁)

/-- When `valid` admits only group elements under `encodeMsg`, the uniform element `γ • g` of the
ideal DDH game perfectly masks both admissible candidate messages, so the experiments for
`bit = false` and `bit = true` are identical. -/
theorem ddhIdealGame_elGamalMsgToDDHDistinguisher_false_eq_true {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (encodeMsg : F.Desc → Msg → List Bool)
    (setup : ℕ → PMF F.Desc) (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hsound : F.AdmitsGroupElements encodeMsg valid) :
    F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary false) n =
      F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary true) n := by
  simp only [ddhIdealGame, elGamalMsgToDDHDistinguisher, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind, Bool.false_eq_true, ↓reduceIte, apply_ite ProbComp.eval,
    ProbComp.eval_pure]
  congr 1; funext d
  congr 1; funext α
  congr 1; funext β
  rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))
    (ProbComp.eval (adversary.choose n _))]
  congr 1; funext choice
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
        (F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary true) n)
        (F.ddhIdealGame setup
          (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary true) n) := by
  rw [← F.ddhRealGame_elGamalMsgToDDHDistinguisher valid encodeMsg setup adversary false n,
    ← F.ddhRealGame_elGamalMsgToDDHDistinguisher valid encodeMsg setup adversary true n]
  refine (Game.advantage_triangle _
    (F.ddhIdealGame setup
      (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary false) n) _).trans ?_
  rw [F.ddhIdealGame_elGamalMsgToDDHDistinguisher_false_eq_true valid encodeMsg setup adversary n
      hsound,
    Game.advantage_comm
      (F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary true) n)]

/-- `elGamalMsgToDDHDistinguisher` is uniform strict PPT whenever `valid` and `encodeMsg` are
computable in polynomial time and `adversary` is uniform strict PPT. -/
theorem isPPTOn_elGamalMsgToDDHDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    {encodeMsg : F.Desc → Msg → List Bool}
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool
      (fun input => F.elGamalMsgToDDHDistinguisher valid encodeMsg adversary bit input.1
        input.2) := by
  let EIn := encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  let E2 := encPair EIn (encPair (encPair encMsg encMsg) encBits)
  have hchoose := hA.choose.on
  have hguess := hA.guess
  have hadd := F.computableInPolyTime_add
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (Msg × Msg) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1)
      E2 encMsg := by
    cases bit <;> fun_prop
  have hencM : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (Msg × Msg) × List Bool =>
        encodeMsg p.1.2.1 (if bit then p.2.1.2 else p.2.1.1))
      E2 encBits :=
    hencMsg.comp ((by fun_prop : ComputableInPolyTime _ _ F.encDesc).prod hm)
  have hvalidArg : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (Msg × Msg) × List Bool =>
        (p.1.1, encPair F.encDesc encBits (p.1.2.1, p.1.2.2.1), p.2.1.1, p.2.1.2))
      E2 (encPair encUnary (encPair encBits (encPair encMsg encMsg))) := by
    fun_prop
  have hvalidStep : ComputableTidilyInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (Msg × Msg) × List Bool =>
        valid p.1.1 (encPair F.encDesc encBits (p.1.2.1, p.1.2.2.1)) p.2.1.1 p.2.1.2)
      E2 encBool :=
    (hvalid.comp hvalidArg).tidy
  have hguessStep : IsPPTOn E2 encBool
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (Msg × Msg) × List Bool =>
        adversary.guess p.1.1 p.2.2 (encPair encBits encBits
          (p.1.2.2.2.1,
            F.add (p.1.2.1, p.1.2.2.2.2, encodeMsg p.1.2.1 (if bit then p.2.1.2 else p.2.1.1))))) :=
    hguess.preprocess
      (prepare := fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (Msg × Msg) × List Bool =>
        (p.1.1, p.2.2, encPair encBits encBits
          (p.1.2.2.2.1,
            F.add (p.1.2.1, p.1.2.2.2.2, encodeMsg p.1.2.1 (if bit then p.2.1.2 else p.2.1.1)))))
      (by fun_prop)
  unfold elGamalMsgToDDHDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
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
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hsound : F.AdmitsGroupElements encodeMsg valid)
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage (F.elGamalMsgCPAGameOn valid encodeMsg setup adversary false n)
        (F.elGamalMsgCPAGameOn valid encodeMsg setup adversary true n) :=
  negligible_of_le
    ((hDDH _ (F.isPPTOn_elGamalMsgToDDHDistinguisher hvalid hencMsg hA false)).add
      (hDDH _ (F.isPPTOn_elGamalMsgToDDHDistinguisher hvalid hencMsg hA true)))
    fun n => F.advantage_elGamalMsgCPAGameOn_le valid encodeMsg setup adversary n hsound

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
  have hd : ComputableTidilyInPolyTime (fun p : F.Desc × Bool => p.1)
      (encPair F.encDesc encBool) F.encDesc := by fun_prop
  have hgen : ComputableTidilyInPolyTime
      (fun p : F.Desc × Bool => F.encode p.1 (F.generator p.1))
      (encPair F.encDesc encBool) encBits :=
    F.computableInPolyTime_generator.tidy.comp hd
  have hbit : ComputableTidilyInPolyTime (fun p : F.Desc × Bool => if p.2 then 1 else 0)
      (encPair F.encDesc encBool) encNat :=
    (ComputableTidilyInPolyTime.snd _ _).cond
      (ComputableTidilyInPolyTime.const 1) (ComputableTidilyInPolyTime.const 0)
  exact ComputableInPolyTime.of_tidy
    (F.computableInPolyTime_smul.tidy.comp (hd.prod (hbit.prod hgen)))

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
  let m := if bit then choice.1.2 else choice.1.1
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
Exercise 11.5(a), p. 459): given `(d, u, v, w)`, pass `(d, u)` as the public key, encrypt the
selected challenge bit by masking with `w`, and return the adversary's guess. -/
abbrev elGamalToDDHDistinguisher (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  F.elGamalMsgToDDHDistinguisher (fun _ _ _ _ => true) F.encodeBit adversary bit n input

/-- In the real DDH game, `elGamalToDDHDistinguisher` simulates `elGamalCPAGame` exactly. -/
@[simp] theorem ddhRealGame_elGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary bit) n =
      F.elGamalCPAGame setup adversary bit n := by
  rw [F.ddhRealGame_elGamalMsgToDDHDistinguisher, F.elGamalCPAGame_eq_elGamalMsgCPAGameOn]

/-- In the ideal DDH game, the uniform element `γ • g` perfectly masks the challenge bit, so the
experiments for `bit = false` and `bit = true` are identical. -/
theorem ddhIdealGame_elGamalToDDHDistinguisher_false_eq_true (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n =
      F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n :=
  F.ddhIdealGame_elGamalMsgToDDHDistinguisher_false_eq_true _ F.encodeBit setup adversary n
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
        (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n) +
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary true) n)
        (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n) := by
  rw [F.elGamalCPAGame_eq_elGamalMsgCPAGameOn, F.elGamalCPAGame_eq_elGamalMsgCPAGameOn]
  exact F.advantage_elGamalMsgCPAGameOn_le _ F.encodeBit setup adversary n
    F.admitsGroupElements_encodeBit

/-- `elGamalToDDHDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_elGamalToDDHDistinguisher {adversary : Encryption.Adversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.elGamalToDDHDistinguisher adversary bit input.1 input.2) :=
  F.isPPTOn_elGamalMsgToDDHDistinguisher
    (ComputableTidilyInPolyTime.const true).computableInPolyTime F.computableInPolyTime_encodeBit hA
    bit

/-- **ElGamal bit encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a), p. 459). -/
theorem DDH.elGamalINDCPA {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) : F.elGamalINDCPA setup := by
  intro adversary hA
  exact negligible_of_le
    ((hDDH _ (F.isPPTOn_elGamalToDDHDistinguisher hA false)).add
      (hDDH _ (F.isPPTOn_elGamalToDDHDistinguisher hA true)))
    (F.advantage_elGamalCPAGame_le setup adversary)

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
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  F.elGamalMsgToDDHDistinguisher valid (fun _ m => m) adversary bit n input

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
        (F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher valid adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher valid adversary true) n)
        (F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher valid adversary true) n) :=
  F.advantage_elGamalMsgCPAGameOn_le valid (fun _ m => m) setup adversary n hsound

/-- **Group-element ElGamal encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a), p. 459): for a polynomial-time admissibility predicate `valid`
that admits only encoded group elements, every uniform strict PPT `Encryption.WordAdversary` has
negligible advantage in `elGamalGroupCPAGameOn valid`. -/
theorem DDH.negligible_elGamalGroupCPAGameOn {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    (hDDH : F.DDH setup)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool)
    (hsound : F.AdmitsGroupElements (fun _ m => m) valid)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) :
    Negligible fun n =>
      Game.advantage (F.elGamalGroupCPAGameOn valid setup adversary false n)
        (F.elGamalGroupCPAGameOn valid setup adversary true n) :=
  hDDH.negligible_elGamalMsgCPAGameOn hvalid hsound (by fun_prop) hA

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
  let d := input.1
  let u := input.2.1
  let m := input.2.2.1
  let b := input.2.2.2
  let pad := H (d, F.smul (d, b, u))
  (F.smul (d, b, F.encode d (F.generator d)),
    Cslib.BitString.listXor pad.length [pad, m])

/-- `encodeHashedElGamalEncrypt` evaluates `hashedElGamalEncrypt` on encoded group elements. -/
@[simp] theorem encodeHashedElGamalEncrypt_encode (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (u : F.Carrier d) (m : List Bool) (b : ℕ) :
    F.encodeHashedElGamalEncrypt H (d, F.encode d u, m, b) =
      (F.encode d (F.hashedElGamalEncrypt H d u m (b : ZMod (F.order d))).1,
        (F.hashedElGamalEncrypt H d u m (b : ZMod (F.order d))).2) := by
  simp only [encodeHashedElGamalEncrypt, hashedElGamalEncrypt, F.smul_encode]

/-- Word-level Hashed ElGamal encryption is computable in polynomial time whenever `H` is. -/
theorem computableInPolyTime_encodeHashedElGamalEncrypt {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    ComputableInPolyTime (F.encodeHashedElGamalEncrypt H)
      (encPair F.encDesc (encPair encBits (encPair encBits encNat)))
      (encPair encBits encBits) := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits encNat))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.1) encIn F.encDesc := by fun_prop
  have hu : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.1) encIn encBits := by fun_prop
  have hm : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.2.1) encIn encBits := by fun_prop
  have hb : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.2.2) encIn encNat := by fun_prop
  have hg := F.computableInPolyTime_generator.comp hd
  have hv := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hg))
  have hbu := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hu))
  have hpad := hH.comp (hd.prod hbu)
  have hxor : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ =>
        let pad := H (input.1, F.smul (input.1, input.2.2.2, input.2.1))
        Cslib.BitString.listXor pad.length [pad, input.2.2.1])
      encIn encBits := by fun_prop
  exact hv.prod hxor

/-- Word-level Hashed ElGamal decryption: given `(d, a, encode v, c)`, derive
`pad = H (d, encode (a • v))` and compute `Cslib.BitString.listXor pad.length [pad, c]`. -/
def decodeHashedElGamal (H : F.Desc × List Bool → List Bool)
    (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  let pad := H (input.1, F.smul (input.1, input.2.1, input.2.2.1))
  Cslib.BitString.listXor pad.length [pad, input.2.2.2]

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
  let encIn := encPair F.encDesc (encPair encNat (encPair encBits encBits))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.1) encIn F.encDesc := by fun_prop
  have ha : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.1) encIn encNat := by fun_prop
  have hv : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.1) encIn encBits := by fun_prop
  have hc : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.2) encIn encBits := by fun_prop
  have hav := F.computableInPolyTime_smul.comp (hd.prod (ha.prod hv))
  have hpad := hH.comp (hd.prod hav)
  unfold decodeHashedElGamal
  fun_prop

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
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad := H (d, F.encode d ((α * β) • F.generator d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d), Cslib.BitString.listXor pad.length [pad, m])
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- Hybrid 1 for Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5,
pp. 449–451): replace the Diffie–Hellman shared element `(α * β) • g` with an independent uniform
group element `γ • g`. -/
noncomputable def hashedElGamalIdealDDHGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad := H (d, F.encode d (γ • F.generator d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d), Cslib.BitString.listXor pad.length [pad, m])
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- Hybrid 2 for Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5,
pp. 449–451): replace the derived key `H (d, encode (γ • g))` with an independent uniform
`msgLen n`-bit key `pad ← Cslib.BitString.uniformList (msgLen n)`. -/
noncomputable def hashedElGamalUniformPadGame (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad ← Cslib.BitString.uniformList (msgLen n)
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d), Cslib.BitString.listXor pad.length [pad, m])
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- The real key-derivation security experiment ([BonehShoup2023], Section 11.5.2, Attack Game 11.3,
Experiment `0`, p. 448): draw `d ← setup n` and independent uniform `α, β, γ : ZMod (F.order d)`,
and give the distinguisher `(d, encode (α • g), encode (β • g), H (d, encode (γ • g)))`. -/
noncomputable def kdfRealGame (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      H (d, F.encode d (γ • F.generator d))))

/-- The ideal key-derivation security experiment ([BonehShoup2023], Section 11.5.2,
Attack Game 11.3, Experiment `1`, p. 448): draw `d ← setup n`, independent uniform
`α, β : ZMod (F.order d)`, and an independent uniform `msgLen n`-bit key
`pad ← Cslib.BitString.uniformList (msgLen n)`, and give the distinguisher
`(d, encode (α • g), encode (β • g), pad)`. -/
noncomputable def kdfIdealGame (setup : ℕ → PMF F.Desc) (msgLen : ℕ → ℕ)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad ← Cslib.BitString.uniformList (msgLen n)
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d), pad))

/-- Secure key derivation for `H` over `F` ([BonehShoup2023], Section 11.5.2, Attack Game 11.3,
p. 448, and Definition 11.5, p. 449): every uniform strict PPT distinguisher has negligible
advantage between `kdfRealGame` and `kdfIdealGame`. No nondegenerate `SecureKDF` instance
(`msgLen n > 0`, e.g., via the leftover hash lemma) is constructed in this module. -/
def SecureKDF (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ) : Prop :=
  Game.Indistinguishable (F.kdfRealGame setup H) (F.kdfIdealGame setup msgLen)
    fun distinguisher =>
      IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encBool (fun input => distinguisher input.1 input.2)

/-- The DDH distinguisher constructed from a Hashed ElGamal IND-CPA adversary ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, pp. 449–451): given `(d, u, v, w)`, pass `(d, u)` as the
public key, mask the selected message word with `pad = H (d, w)` via
`Cslib.BitString.listXor pad.length [pad, m]`, and return the adversary's guess. -/
def hashedElGamalToDDHDistinguisher (H : F.Desc × List Bool → List Bool)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let pad := H (input.1, input.2.2.2)
  let ct := encPair encBits encBits
    (input.2.2.1, Cslib.BitString.listXor pad.length [pad, m])
  adversary.guess n choice.2 ct

/-- In the real DDH game, `hashedElGamalToDDHDistinguisher` simulates `hashedElGamalCPAGame`
exactly. -/
@[simp] theorem ddhRealGame_hashedElGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary bit) n =
      F.hashedElGamalCPAGame setup H adversary bit n := by
  simp only [ddhRealGame, hashedElGamalToDDHDistinguisher, hashedElGamalCPAGame, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  rw [PMF.bind_comm]

/-- In the ideal DDH game, `hashedElGamalToDDHDistinguisher` simulates `hashedElGamalIdealDDHGame`
exactly. -/
@[simp] theorem ddhIdealGame_hashedElGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.ddhIdealGame setup (F.hashedElGamalToDDHDistinguisher H adversary bit) n =
      F.hashedElGamalIdealDDHGame setup H adversary bit n := by
  simp only [ddhIdealGame, hashedElGamalToDDHDistinguisher, hashedElGamalIdealDDHGame,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- `hashedElGamalToDDHDistinguisher` is uniform strict PPT whenever `H` is polynomial time and
`adversary` is uniform strict PPT. -/
theorem isPPTOn_hashedElGamalToDDHDistinguisher {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.hashedElGamalToDDHDistinguisher H adversary bit input.1 input.2) := by
  have hchoose := hA.choose.on
  have hguess := hA.guess
  let E :=
    encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      (encPair (encPair encBits encBits) encBits)
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (List Bool × List Bool) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1) E encBits := by
    cases bit <;> fun_prop
  have hpad : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (List Bool × List Bool) × List Bool =>
        H (p.1.2.1, p.1.2.2.2.2)) E encBits :=
    hH.comp (by fun_prop)
  unfold hashedElGamalToDDHDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
          (List Bool × List Bool) × List Bool =>
      let pad := H (p.1.2.1, p.1.2.2.2.2)
      (p.1.1, p.2.2, encPair encBits encBits
        (p.1.2.2.2.1,
          Cslib.BitString.listXor pad.length [pad, if bit then p.2.1.2 else p.2.1.1])))
    (by fun_prop)

/-- The KDF distinguisher constructed from a Hashed ElGamal IND-CPA adversary ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, pp. 449–451): given `(d, u, v, pad)`, pass `(d, u)` as the
public key, mask the selected message word with `pad` via
`Cslib.BitString.listXor pad.length [pad, m]`, and return the adversary's guess. -/
def hashedElGamalToKDFDistinguisher (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let pad := input.2.2.2
  let ct := encPair encBits encBits
    (input.2.2.1, Cslib.BitString.listXor pad.length [pad, m])
  adversary.guess n choice.2 ct

/-- In the real KDF game, `hashedElGamalToKDFDistinguisher` simulates `hashedElGamalIdealDDHGame`
exactly. -/
@[simp] theorem kdfRealGame_hashedElGamalToKDFDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary bit) n =
      F.hashedElGamalIdealDDHGame setup H adversary bit n := by
  simp only [kdfRealGame, hashedElGamalToKDFDistinguisher, hashedElGamalIdealDDHGame,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- In the ideal KDF game, `hashedElGamalToKDFDistinguisher` simulates
`hashedElGamalUniformPadGame` exactly. -/
@[simp] theorem kdfIdealGame_hashedElGamalToKDFDistinguisher (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary bit) n =
      F.hashedElGamalUniformPadGame setup msgLen adversary bit n := by
  simp only [kdfIdealGame, hashedElGamalToKDFDistinguisher, hashedElGamalUniformPadGame,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- `hashedElGamalToKDFDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_hashedElGamalToKDFDistinguisher {adversary : Encryption.WordAdversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.hashedElGamalToKDFDistinguisher adversary bit input.1 input.2) := by
  have hchoose := hA.choose.on
  have hguess := hA.guess
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (List Bool × List Bool) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encBits encBits) encBits))
      encBits := by
    cases bit <;> fun_prop
  unfold hashedElGamalToKDFDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
          (List Bool × List Bool) × List Bool =>
      (p.1.1, p.2.2, encPair encBits encBits
        (p.1.2.2.2.1,
          Cslib.BitString.listXor p.1.2.2.2.2.length
            [p.1.2.2.2.2, if bit then p.2.1.2 else p.2.1.1])))
    (by fun_prop)

/-- In `hashedElGamalUniformPadGame`, the uniform `msgLen n`-bit pad masks any challenge message
word perfectly via `Cslib.BitString.listXor pad.length [pad, m]`, so the experiments for
`bit = false` and `bit = true` are identical. -/
theorem hashedElGamalUniformPadGame_false_eq_true (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : Encryption.WordAdversary) (n : ℕ) :
    F.hashedElGamalUniformPadGame setup msgLen adversary false n =
      F.hashedElGamalUniformPadGame setup msgLen adversary true n := by
  simp only [hashedElGamalUniformPadGame, PMF.monad_bind_eq_bind,
    Bool.false_eq_true, ↓reduceIte]
  congr 1; funext d
  congr 1; funext α
  congr 1; funext choice
  congr 1; funext β
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
`hashedElGamalToKDFDistinguisher`. -/
theorem advantage_hashedElGamalCPAGame_le (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (adversary : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
      (F.hashedElGamalCPAGame setup H adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary false) n)
        (F.ddhIdealGame setup (F.hashedElGamalToDDHDistinguisher H adversary false) n) +
      Game.advantage
        (F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary false) n)
        (F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary false) n) +
      Game.advantage
        (F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary true) n)
        (F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary true) n) +
      Game.advantage
        (F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary true) n)
        (F.ddhIdealGame setup (F.hashedElGamalToDDHDistinguisher H adversary true) n) := by
  have h1 := Game.advantage_triangle
    (F.hashedElGamalCPAGame setup H adversary false n)
    (F.hashedElGamalIdealDDHGame setup H adversary false n)
    (F.hashedElGamalCPAGame setup H adversary true n)
  have h2 := Game.advantage_triangle
    (F.hashedElGamalIdealDDHGame setup H adversary false n)
    (F.hashedElGamalUniformPadGame setup msgLen adversary false n)
    (F.hashedElGamalCPAGame setup H adversary true n)
  have h3 := Game.advantage_triangle
    (F.hashedElGamalUniformPadGame setup msgLen adversary true n)
    (F.hashedElGamalIdealDDHGame setup H adversary true n)
    (F.hashedElGamalCPAGame setup H adversary true n)
  rw [F.hashedElGamalUniformPadGame_false_eq_true setup msgLen adversary n] at h2
  calc Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
        (F.hashedElGamalCPAGame setup H adversary true n)
      ≤ Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
          (F.hashedElGamalIdealDDHGame setup H adversary false n) +
        (Game.advantage (F.hashedElGamalIdealDDHGame setup H adversary false n)
          (F.hashedElGamalUniformPadGame setup msgLen adversary true n) +
        (Game.advantage
          (F.hashedElGamalUniformPadGame setup msgLen adversary true n)
          (F.hashedElGamalIdealDDHGame setup H adversary true n) +
        Game.advantage
          (F.hashedElGamalIdealDDHGame setup H adversary true n)
          (F.hashedElGamalCPAGame setup H adversary true n))) :=
        h1.trans (add_le_add le_rfl (h2.trans (add_le_add le_rfl h3)))
    _ = _ := by
        simp only [ddhRealGame_hashedElGamalToDDHDistinguisher,
          ddhIdealGame_hashedElGamalToDDHDistinguisher,
          kdfRealGame_hashedElGamalToKDFDistinguisher,
          kdfIdealGame_hashedElGamalToKDFDistinguisher,
          F.hashedElGamalUniformPadGame_false_eq_true setup msgLen adversary n,
          Game.advantage_comm (F.hashedElGamalIdealDDHGame setup H adversary true n)
            (F.hashedElGamalUniformPadGame setup msgLen adversary true n),
          Game.advantage_comm (F.hashedElGamalCPAGame setup H adversary true n)
            (F.hashedElGamalIdealDDHGame setup H adversary true n),
          add_assoc]

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
        (F.hashedElGamalCPAGame setup H adversary true n) :=
  negligible_of_le
    ((((hDDH _ (F.isPPTOn_hashedElGamalToDDHDistinguisher hH hA false)).add
      (hKDF _ (F.isPPTOn_hashedElGamalToKDFDistinguisher hA false))).add
      (hKDF _ (F.isPPTOn_hashedElGamalToKDFDistinguisher hA true))).add
      (hDDH _ (F.isPPTOn_hashedElGamalToDDHDistinguisher hH hA true)))
    (F.advantage_hashedElGamalCPAGame_le setup H msgLen adversary)

end Cslib.Crypto.PrimeOrderGroupFamily
