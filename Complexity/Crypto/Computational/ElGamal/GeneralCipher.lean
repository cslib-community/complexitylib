/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.ElGamal.KDF
public import Complexity.Crypto.Computational.ElGamal.ProbComp
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Crypto.Game.Statistical
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Event
import Complexity.Probability.StatisticalDistance
import Complexity.Tactic.PPT

/-!
# General-Cipher Hashed ElGamal ([BonehShoup2023], Section 11.5, Theorem 11.5)

This module generalizes Hashed ElGamal ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1,
and Section 11.5.2, Theorem 11.5, pp. 448–451) from the one-time pad specialization in
`Complexity/Crypto/Computational/ElGamal.lean` to an arbitrary semantically secure symmetric cipher
$\mathcal{E}_s$.

* **Paraphrase of [BonehShoup2023], Section 11.5 (p. 445) and Remark 11.1 (p. 446):** over a cyclic
  group $G$ of prime order $q$ with generator $g$, a symmetric cipher $\mathcal{E}_s = (E_s, D_s)$
  over $(\mathcal{K}, \mathcal{M}, \mathcal{C})$, and a key-derivation hash function $H$, key
  generation samples $\alpha \leftarrow \mathbb{Z}_q$ and outputs $(pk = \alpha \cdot g, sk =
  \alpha)$. In the $\mathcal{E}'_{\mathrm{EG}}$ variant of Remark 11.1 (which derives $k$ from
  $w = \beta \cdot u$ alone), encryption of $m \in \mathcal{M}$ under $pk = u$ samples
  $\beta \leftarrow \mathbb{Z}_q$, sets $v = \beta \cdot g$, $w = \beta \cdot u$, $k = H(w)$,
  $c \leftarrow E_s(k, m)$, and outputs $(v, c)$; decryption of $(v, c)$ under $sk = \alpha$ sets
  $w = \alpha \cdot v$, $k = H(w)$, and outputs $D_s(k, c)$.
* **Paraphrase of [BonehShoup2023], Section 11.5.2, Theorem 11.5 and Equation (11.14)
  (pp. 449–451):** if DDH holds for $G$, $H$ is a secure KDF, and $\mathcal{E}_s$ is semantically
  secure, then Hashed ElGamal is semantically secure; for every CPA adversary $\mathcal{A}$ there
  exist elementary wrapper adversaries $\mathcal{B}_{\mathrm{ddh}}$, $\mathcal{B}_{\mathrm{kdf}}$,
  and $\mathcal{B}_s$ such that
  $\mathrm{SSadv}[\mathcal{A}, \mathcal{E}_{\mathrm{EG}}] \le
  2 \cdot \mathrm{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, G] +
  2 \cdot \mathrm{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
  \mathrm{SSadv}[\mathcal{B}_s, \mathcal{E}_s]$.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherDecrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeHashedElGamalCipherEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeHashedElGamalCipher`: algebraic and word-level Hashed
  ElGamal encryption and decryption with a general symmetric cipher
  ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherCPAGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherIdealDDHGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherUniformKeyGameOn`: PMF-level IND-CPA
  experiments and hybrids for general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5.2,
  Theorem 11.5, pp. 449–451).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDDHHiddenBitDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToKDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToKDFHiddenBitDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDEMAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.seededSetupProb`: per-bit and hidden-bit DDH and KDF
  reductions, symmetric-cipher (`DEMOneTimeINDCPAOn`) reduction adversary, and executable seeded
  setup sampler for Theorem 11.5 ([BonehShoup2023], Section 11.5.2, pp. 449–451).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherDecrypt_hashedElGamalCipherEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeHashedElGamalCipher_hashedElGamalCipherEncrypt`:
  decryption correctness for general-cipher Hashed ElGamal.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le_two_mul`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le_demGameOn`:
  two-distinguisher and single hidden-bit distinguisher quantitative bounds for Theorem 11.5
  (matching Equation `(11.14)` of [BonehShoup2023], p. 449), together with the native
  approximate-sampling (`sampleExp`, adding `4 / 2 ^ n`) bridge to standalone
  symmetric-cipher security (`Encryption.demGameOn`).
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCipherCPAGameOn` and its
  `DEMOneTimeINDCPAOn` / `linearHashKDF` specializations
  (`negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeINDCPAOn`,
  `negligible_hashedElGamalCipherCPAGameOn_linearHashKDF`):
  Theorem 11.5 IND-CPA security in `hashedElGamalCipherCPAGameOn` from `DDH`, `SecureKDF`, and
  `DEMOneTimeINDCPAOn`, plus unconditional KDF instantiation via `linearHashKDF`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5 (pp. 445–446, Remark 11.1) and Section 11.5.2
  (pp. 448–451, Attack Game 11.3, Definition 11.5, Theorem 11.5).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Encryption Game
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Algebraic and word-level general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5) -/

/-- Algebraic Hashed ElGamal encryption with a general deterministic symmetric cipher `encSym`
([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1): given key-derivation hash function
`H : F.Desc × List Bool → List Bool`, public key `u : F.Carrier d`, message `m : Msg`, and
randomness `β : ZMod (F.order d)`, derive `k = H (d, encode (β • u))` and output
`(β • g, encSym k m)`. -/
def hashedElGamalCipherEncrypt {Msg Cipher : Type} (H : F.Desc × List Bool → List Bool)
    (encSym : List Bool → Msg → Cipher) (d : F.Desc) (u : F.Carrier d) (m : Msg)
    (β : ZMod (F.order d)) : F.Carrier d × Cipher :=
  (β • F.generator d, encSym (H (d, F.encode d (β • u))) m)

/-- Under a genuine public key `u = α • g`, `hashedElGamalCipherEncrypt` derives the symmetric key
`H (d, encode ((α * β) • g))`. -/
theorem hashedElGamalCipherEncrypt_smul_generator {Msg Cipher : Type}
    (H : F.Desc × List Bool → List Bool) (encSym : List Bool → Msg → Cipher) (d : F.Desc)
    (α β : ZMod (F.order d)) (m : Msg) :
    F.hashedElGamalCipherEncrypt H encSym d (α • F.generator d) m β =
      (β • F.generator d, encSym (H (d, F.encode d ((α * β) • F.generator d))) m) := by
  simp only [hashedElGamalCipherEncrypt, smul_smul, mul_comm β α]

/-- Algebraic Hashed ElGamal decryption with a general symmetric cipher `decSym`
([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1): given secret key `α : ZMod (F.order d)`
and ciphertext `(v, c)`, derive `k = H (d, encode (α • v))` and recover `decSym k c`. -/
def hashedElGamalCipherDecrypt {Msg Cipher : Type} (H : F.Desc × List Bool → List Bool)
    (decSym : List Bool → Cipher → Msg) (d : F.Desc) (α : ZMod (F.order d))
    (ct : F.Carrier d × Cipher) : Msg :=
  decSym (H (d, F.encode d (α • ct.1))) ct.2

/-- **General-cipher Hashed ElGamal decryption correctness**: whenever `decSym k (encSym k m) = m`
holds for the derived key `k = H (d, encode ((α * β) • g))`, decrypting an encryption under
`u = α • g` with secret key `α` recovers `m`. -/
@[simp] theorem hashedElGamalCipherDecrypt_hashedElGamalCipherEncrypt {Msg Cipher : Type}
    (H : F.Desc × List Bool → List Bool) (encSym : List Bool → Msg → Cipher)
    (decSym : List Bool → Cipher → Msg) (d : F.Desc) (α β : ZMod (F.order d)) {m : Msg}
    (hdec :
      let k := H (d, F.encode d ((α * β) • F.generator d))
      decSym k (encSym k m) = m) :
    F.hashedElGamalCipherDecrypt H decSym d α
      (F.hashedElGamalCipherEncrypt H encSym d (α • F.generator d) m β) = m := by
  simp only [hashedElGamalCipherDecrypt, hashedElGamalCipherEncrypt_smul_generator, smul_smul]
  exact hdec

/-- `hashedElGamalEncrypt` is the one-time pad specialization of `hashedElGamalCipherEncrypt`. -/
theorem hashedElGamalEncrypt_eq_hashedElGamalCipherEncrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (u : F.Carrier d) (m : List Bool) (β : ZMod (F.order d)) :
    F.hashedElGamalEncrypt H d u m β =
      F.hashedElGamalCipherEncrypt H
        (fun pad msg => Cslib.BitString.listXor pad.length [pad, msg]) d u m β :=
  rfl

/-- `hashedElGamalDecrypt` is the one-time pad specialization of `hashedElGamalCipherDecrypt`. -/
theorem hashedElGamalDecrypt_eq_hashedElGamalCipherDecrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (α : ZMod (F.order d)) (ct : F.Carrier d × List Bool) :
    F.hashedElGamalDecrypt H d α ct =
      F.hashedElGamalCipherDecrypt H
        (fun pad c => Cslib.BitString.listXor pad.length [pad, c]) d α ct :=
  rfl

/-- Word-level Hashed ElGamal encryption with a general symmetric cipher `encSym`: given
`(d, encode u, m, b)`, derive `k = H (d, encode (b • u))` and compute
`(encode (b • g), encSym (k, m))`. -/
def encodeHashedElGamalCipherEncrypt {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (encSym : List Bool × Msg → List Bool)
    (input : F.Desc × List Bool × Msg × ℕ) : List Bool × List Bool :=
  let d := input.1
  let u := input.2.1
  let m := input.2.2.1
  let b := input.2.2.2
  let k := H (d, F.smul (d, b, u))
  (F.smul (d, b, F.encode d (F.generator d)), encSym (k, m))

/-- `encodeHashedElGamalCipherEncrypt` evaluates `hashedElGamalCipherEncrypt` on encoded group
elements. -/
@[simp] theorem encodeHashedElGamalCipherEncrypt_encode {Msg : Type}
    (H : F.Desc × List Bool → List Bool) (encSym : List Bool × Msg → List Bool)
    (d : F.Desc) (u : F.Carrier d) (m : Msg) (b : ℕ) :
    F.encodeHashedElGamalCipherEncrypt H encSym (d, F.encode d u, m, b) =
      (F.encode d
        (F.hashedElGamalCipherEncrypt H (fun k msg => encSym (k, msg)) d u m
          (b : ZMod (F.order d))).1,
        (F.hashedElGamalCipherEncrypt H (fun k msg => encSym (k, msg)) d u m
          (b : ZMod (F.order d))).2) := by
  simp only [encodeHashedElGamalCipherEncrypt, hashedElGamalCipherEncrypt, F.smul_encode]

/-- Word-level general-cipher Hashed ElGamal encryption is computable in polynomial time whenever
`H` and `encSym` are. -/
theorem computableInPolyTime_encodeHashedElGamalCipherEncrypt {Msg : Type}
    {encMsg : Msg ↪ List Bool} {H : F.Desc × List Bool → List Bool}
    {encSym : List Bool × Msg → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencSym : ComputableInPolyTime encSym (encPair encBits encMsg) encBits) :
    ComputableInPolyTime (F.encodeHashedElGamalCipherEncrypt H encSym)
      (encPair F.encDesc (encPair encBits (encPair encMsg encNat)))
      (encPair encBits encBits) := by
  let E := encPair F.encDesc (encPair encBits (encPair encMsg encNat))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × List Bool × Msg × ℕ => input.1) E F.encDesc := by fun_prop
  have hgen : ComputableInPolyTime
      (fun input : F.Desc × List Bool × Msg × ℕ => F.encode input.1 (F.generator input.1))
      E encBits :=
    F.computableInPolyTime_generator.comp hd
  have hv : ComputableInPolyTime
      (fun input : F.Desc × List Bool × Msg × ℕ =>
        F.smul (input.1, input.2.2.2, F.encode input.1 (F.generator input.1))) E encBits :=
    F.computableInPolyTime_smul.comp (hd.prod ((by fun_prop :
      ComputableInPolyTime (fun input : F.Desc × List Bool × Msg × ℕ => input.2.2.2)
        E encNat).prod hgen))
  have hw : ComputableInPolyTime
      (fun input : F.Desc × List Bool × Msg × ℕ => F.smul (input.1, input.2.2.2, input.2.1))
      E encBits :=
    F.computableInPolyTime_smul.comp (by fun_prop)
  have hk : ComputableInPolyTime
      (fun input : F.Desc × List Bool × Msg × ℕ =>
        H (input.1, F.smul (input.1, input.2.2.2, input.2.1))) E encBits :=
    hH.comp (hd.prod hw)
  have hc : ComputableInPolyTime
      (fun input : F.Desc × List Bool × Msg × ℕ =>
        encSym (H (input.1, F.smul (input.1, input.2.2.2, input.2.1)), input.2.2.1))
      E encBits :=
    hencSym.comp (hk.prod (by fun_prop))
  unfold encodeHashedElGamalCipherEncrypt
  exact hv.prod hc

/-- Word-level Hashed ElGamal decryption with a general symmetric cipher `decSym`: given
`(d, a, encode v, c)`, derive `k = H (d, encode (a • v))` and compute `decSym (k, c)`. -/
def decodeHashedElGamalCipher {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (decSym : List Bool × List Bool → Msg)
    (input : F.Desc × ℕ × List Bool × List Bool) : Msg :=
  decSym (H (input.1, F.smul (input.1, input.2.1, input.2.2.1)), input.2.2.2)

/-- `decodeHashedElGamalCipher` computes `hashedElGamalCipherDecrypt` on encoded group elements. -/
@[simp] theorem decodeHashedElGamalCipher_encode {Msg : Type}
    (H : F.Desc × List Bool → List Bool) (decSym : List Bool × List Bool → Msg)
    (d : F.Desc) (a : ℕ) (v : F.Carrier d) (c : List Bool) :
    F.decodeHashedElGamalCipher H decSym (d, a, F.encode d v, c) =
      F.hashedElGamalCipherDecrypt H (fun k ct => decSym (k, ct)) d (a : ZMod (F.order d))
        (v, c) := by
  simp only [decodeHashedElGamalCipher, hashedElGamalCipherDecrypt, F.smul_encode]

/-- Word-level general-cipher Hashed ElGamal decryption of an honest encryption recovers `m`
whenever `decSym` inverts `encSym` on the derived key. -/
theorem decodeHashedElGamalCipher_hashedElGamalCipherEncrypt {Msg : Type}
    (H : F.Desc × List Bool → List Bool) (encSym : List Bool × Msg → List Bool)
    (decSym : List Bool × List Bool → Msg) (d : F.Desc) (a : ℕ) (β : ZMod (F.order d)) {m : Msg}
    (hdec :
      let k := H (d, F.encode d (((a : ZMod (F.order d)) * β) • F.generator d))
      decSym (k, encSym (k, m)) = m) :
    F.decodeHashedElGamalCipher H decSym (d, a,
      F.encode d
        (F.hashedElGamalCipherEncrypt H (fun k msg => encSym (k, msg)) d
          ((a : ZMod (F.order d)) • F.generator d) m β).1,
      (F.hashedElGamalCipherEncrypt H (fun k msg => encSym (k, msg)) d
        ((a : ZMod (F.order d)) • F.generator d) m β).2) = m := by
  rw [F.decodeHashedElGamalCipher_encode,
    F.hashedElGamalCipherDecrypt_hashedElGamalCipherEncrypt H _ _ d _ β hdec]

/-- Word-level general-cipher Hashed ElGamal decryption is computable in polynomial time whenever
`H` and `decSym` are. -/
theorem computableInPolyTime_decodeHashedElGamalCipher {Msg : Type}
    {encMsg : Msg ↪ List Bool} {H : F.Desc × List Bool → List Bool}
    {decSym : List Bool × List Bool → Msg}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hdecSym : ComputableInPolyTime decSym (encPair encBits encBits) encMsg) :
    ComputableInPolyTime (F.decodeHashedElGamalCipher H decSym)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encMsg := by
  let E := encPair F.encDesc (encPair encNat (encPair encBits encBits))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.1) E F.encDesc := by fun_prop
  have hw : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool =>
        F.smul (input.1, input.2.1, input.2.2.1)) E encBits :=
    F.computableInPolyTime_smul.comp (by fun_prop)
  have hk : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool =>
        H (input.1, F.smul (input.1, input.2.1, input.2.2.1))) E encBits :=
    hH.comp (hd.prod hw)
  unfold decodeHashedElGamalCipher
  exact hdecSym.comp (hk.prod (by fun_prop))

/-! ### PMF-level general-cipher Hashed ElGamal IND-CPA games and Theorem 11.5 reductions -/

/-- The IND-CPA experiment for general-cipher Hashed ElGamal (`Game 0`, [BonehShoup2023],
Section 11.5, pp. 445–446, Remark 11.1, and Section 11.5.2, Theorem 11.5, Figure 11.4,
pp. 449–450) with challenge-pair admissibility predicate `valid`: draw `d ← setup n` and a uniform
secret key `α : ZMod (F.order d)`, and pass `pk = (d, encode (α • g))` to `adversary.choose`. If
`valid n pk m₀ m₁` holds, encrypt the selected message `m` under a fresh uniform exponent
`β : ZMod (F.order d)` and derived symmetric key `k = H (d, encode ((α * β) • g))` via
`c ← encryptSym n k m`, and pass `(encode (β • g), c)` to `adversary.guess`; otherwise output
`false`, in both experiments. -/
noncomputable def hashedElGamalCipherCPAGameOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  if valid n pk choice.1.1 choice.1.2 then
    let m := if bit then choice.1.2 else choice.1.1
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let k := H (d, F.encode d ((α * β) • F.generator d))
    let c ← ProbComp.eval (encryptSym n k m)
    let ct := encPair encBits encBits (F.encode d (β • F.generator d), c)
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- Unrestricted general-cipher Hashed ElGamal IND-CPA experiment: `hashedElGamalCipherCPAGameOn`
with every challenge pair admissible. -/
noncomputable abbrev hashedElGamalCipherCPAGame {Msg : Type} (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game :=
  F.hashedElGamalCipherCPAGameOn (fun _ _ _ _ => true) setup H encryptSym adversary bit n

/-- `hashedElGamalCPAGame` is the specialization of `hashedElGamalCipherCPAGame` to one-time pad
XOR encryption. -/
theorem hashedElGamalCPAGame_eq_hashedElGamalCipherCPAGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.hashedElGamalCPAGame setup H adversary bit n =
      F.hashedElGamalCipherCPAGame setup H
        (fun _ pad m => pure (Cslib.BitString.listXor pad.length [pad, m])) adversary bit n := by
  simp only [hashedElGamalCPAGame, hashedElGamalCipherCPAGame, hashedElGamalCipherCPAGameOn,
    ↓reduceIte, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.pure_bind]

/-- **Game 1** for general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of
Theorem 11.5, p. 450): replace the Diffie–Hellman shared element `(α * β) • g` with an independent
uniform group element `γ • g`. -/
noncomputable def hashedElGamalCipherIdealDDHGameOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  if valid n pk choice.1.1 choice.1.2 then
    let m := if bit then choice.1.2 else choice.1.1
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let γ ← PMF.uniformOfFintype (ZMod (F.order d))
    let k := H (d, F.encode d (γ • F.generator d))
    let c ← ProbComp.eval (encryptSym n k m)
    let ct := encPair encBits encBits (F.encode d (β • F.generator d), c)
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- Unrestricted Game 1 for general-cipher Hashed ElGamal. -/
noncomputable abbrev hashedElGamalCipherIdealDDHGame {Msg : Type} (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game :=
  F.hashedElGamalCipherIdealDDHGameOn (fun _ _ _ _ => true) setup H encryptSym adversary bit n

/-- **Game 2** for general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of
Theorem 11.5, p. 450): replace the derived key `H (d, encode (γ • g))` with an independent uniform
`keyLen n`-bit key `k ← Cslib.BitString.uniformList (keyLen n)`. -/
noncomputable def hashedElGamalCipherUniformKeyGameOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  if valid n pk choice.1.1 choice.1.2 then
    let m := if bit then choice.1.2 else choice.1.1
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let k ← Cslib.BitString.uniformList (keyLen n)
    let c ← ProbComp.eval (encryptSym n k m)
    let ct := encPair encBits encBits (F.encode d (β • F.generator d), c)
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- Unrestricted Game 2 for general-cipher Hashed ElGamal. -/
noncomputable abbrev hashedElGamalCipherUniformKeyGame {Msg : Type} (setup : ℕ → PMF F.Desc)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game :=
  F.hashedElGamalCipherUniformKeyGameOn (fun _ _ _ _ => true) setup keyLen encryptSym adversary
    bit n

/-- Running the unrestricted `hashedElGamalCipherCPAGame` on `adversary.restrict valid` has the same
output distribution as running `hashedElGamalCipherCPAGameOn valid` on `adversary`. -/
theorem hashedElGamalCipherCPAGame_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.hashedElGamalCipherCPAGame setup H encryptSym (adversary.restrict valid) bit n =
      F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary bit n := by
  simp only [hashedElGamalCipherCPAGame, hashedElGamalCipherCPAGameOn,
    Encryption.AdversaryOf.restrict, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    List.headD_cons, List.tail_cons]
  congr 1; funext d
  congr 1; funext α
  congr 1; funext choice
  cases valid n (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))
      choice.1.1 choice.1.2 <;>
    simp [PMF.bind_const]

/-- Running the unrestricted `hashedElGamalCipherIdealDDHGame` on `adversary.restrict valid` has the
same output distribution as running `hashedElGamalCipherIdealDDHGameOn valid` on `adversary`. -/
theorem hashedElGamalCipherIdealDDHGame_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.hashedElGamalCipherIdealDDHGame setup H encryptSym (adversary.restrict valid) bit n =
      F.hashedElGamalCipherIdealDDHGameOn valid setup H encryptSym adversary bit n := by
  simp only [hashedElGamalCipherIdealDDHGame, hashedElGamalCipherIdealDDHGameOn,
    Encryption.AdversaryOf.restrict, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    List.headD_cons, List.tail_cons]
  congr 1; funext d
  congr 1; funext α
  congr 1; funext choice
  cases valid n (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))
      choice.1.1 choice.1.2 <;>
    simp [PMF.bind_const]

/-- Running the unrestricted `hashedElGamalCipherUniformKeyGame` on `adversary.restrict valid` has
the same output distribution as running `hashedElGamalCipherUniformKeyGameOn valid` on
`adversary`. -/
theorem hashedElGamalCipherUniformKeyGame_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym (adversary.restrict valid) bit n =
      F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary bit n := by
  simp only [hashedElGamalCipherUniformKeyGame, hashedElGamalCipherUniformKeyGameOn,
    Encryption.AdversaryOf.restrict, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    List.headD_cons, List.tail_cons]
  congr 1; funext d
  congr 1; funext α
  congr 1; funext choice
  cases valid n (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))
      choice.1.1 choice.1.2 <;>
    simp [PMF.bind_const]

/-- Per-bit DDH distinguisher constructed from a general-cipher Hashed ElGamal IND-CPA adversary
([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5, p. 450): given `(d, u, v, w)`, pass
`pk = (d, u)` to `adversary.choose`, encrypt the selected message `m` under `k = H (d, w)` via
`c ← encryptSym n k m`, and return `adversary.guess` on `(v, c)`. -/
def hashedElGamalCipherToDDHDistinguisher {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let k := H (input.1, input.2.2.2)
  let c ← encryptSym n k m
  let ct := encPair encBits encBits (input.2.2.1, c)
  adversary.guess n choice.2 ct

/-- In the real DDH game, `hashedElGamalCipherToDDHDistinguisher` simulates
`hashedElGamalCipherCPAGame` exactly. -/
@[simp] theorem ddhRealGame_hashedElGamalCipherToDDHDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.hashedElGamalCipherToDDHDistinguisher H encryptSym adversary bit) n =
      F.hashedElGamalCipherCPAGame setup H encryptSym adversary bit n := by
  simp only [ddhRealGame, hashedElGamalCipherToDDHDistinguisher, hashedElGamalCipherCPAGame,
    hashedElGamalCipherCPAGameOn, ↓reduceIte, ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  rw [PMF.bind_comm]

/-- In the ideal DDH game, `hashedElGamalCipherToDDHDistinguisher` simulates
`hashedElGamalCipherIdealDDHGame` exactly. -/
@[simp] theorem ddhIdealGame_hashedElGamalCipherToDDHDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.ddhIdealGame setup (F.hashedElGamalCipherToDDHDistinguisher H encryptSym adversary bit) n =
      F.hashedElGamalCipherIdealDDHGame setup H encryptSym adversary bit n := by
  simp only [ddhIdealGame, hashedElGamalCipherToDDHDistinguisher, hashedElGamalCipherIdealDDHGame,
    hashedElGamalCipherIdealDDHGameOn, ↓reduceIte, ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- `hashedElGamalCipherToDDHDistinguisher` is uniform strict PPT whenever `H` is polynomial time
and `encryptSym` and `adversary` are uniform strict PPT. -/
theorem isPPTOn_hashedElGamalCipherToDDHDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {H : F.Desc × List Bool → List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : Encryption.AdversaryOf Msg}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool
      (fun input =>
        F.hashedElGamalCipherToDDHDistinguisher H encryptSym adversary bit input.1 input.2) := by
  let E0 := encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  let E1 := encPair E0 (encPair (encPair encMsg encMsg) encBits)
  let E2 := encPair E1 encBits
  have hchoose := hA.choose.on
  have hguess := hA.guess
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Msg × Msg) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1) E1 encMsg := by
    cases bit <;> fun_prop
  have hk : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Msg × Msg) × List Bool =>
        H (p.1.2.1, p.1.2.2.2.2)) E1 encBits :=
    hH.comp (by fun_prop)
  unfold hashedElGamalCipherToDDHDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  refine (hencryptSym.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Msg × Msg) × List Bool =>
      (p.1.1, H (p.1.2.1, p.1.2.2.2.2), if bit then p.2.1.2 else p.2.1.1))
    (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        ((ℕ × F.Desc × List Bool × List Bool × List Bool) × (Msg × Msg) × List Bool) × List Bool =>
      (p.1.1.1, p.1.2.2, encPair encBits encBits (p.1.1.2.2.2.1, p.2)))
    (by fun_prop)

/-- Single hidden-bit DDH distinguisher $\mathcal{B}_{\mathrm{ddh}}$ ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, Figure 11.4 and Equation `(11.17)`, p. 450): sample a uniform
challenge bit `bit ← ProbComp.uniform Bool`, run `hashedElGamalCipherToDDHDistinguisher` on `bit`,
and output `guess ^^ bit`. -/
noncomputable def hashedElGamalCipherToDDHHiddenBitDistinguisher {Msg : Type}
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let bit ← ProbComp.uniform Bool
  let guess ← F.hashedElGamalCipherToDDHDistinguisher H encryptSym adversary bit n input
  return (guess ^^ bit)

/-- `hashedElGamalCipherToDDHHiddenBitDistinguisher` is uniform strict PPT whenever `H` is
polynomial time and `encryptSym` and `adversary` are uniform strict PPT. -/
theorem isPPTOn_hashedElGamalCipherToDDHHiddenBitDistinguisher {Msg : Type}
    {encMsg : Msg ↪ List Bool} {H : F.Desc × List Bool → List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : Encryption.AdversaryOf Msg}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool
      (fun input =>
        F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym adversary
          input.1 input.2) := by
  let E0 := encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  have hFalse := F.isPPTOn_hashedElGamalCipherToDDHDistinguisher hH hencryptSym hA false
  have hTrue := F.isPPTOn_hashedElGamalCipherToDDHDistinguisher hH hencryptSym hA true
  have hStep : IsPPTOn (encPair E0 encBool) encBool
      (fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × Bool =>
        F.hashedElGamalCipherToDDHDistinguisher H encryptSym adversary p.2 p.1.1 p.1.2) := by
    refine (IsPPTOn.cond (condition := Prod.snd) (by fun_prop)
      (hTrue.preprocess (prepare := Prod.fst) (by fun_prop))
      (hFalse.preprocess (prepare := Prod.fst) (by fun_prop))).congr ?_
    intro ⟨input, bit⟩
    cases bit <;> rfl
  have hXor : ComputableInPolyTime
      (fun p : ((ℕ × F.Desc × List Bool × List Bool × List Bool) × Bool) × Bool => p.2 ^^ p.1.2)
      (encPair (encPair E0 encBool) encBool) encBool := by
    fun_prop
  unfold hashedElGamalCipherToDDHHiddenBitDistinguisher
  exact (isPPTOn_uniform_bool E0).bind_with (hStep.bind_with hXor.isPPTOn)

/-- Per-bit KDF distinguisher constructed from a general-cipher Hashed ElGamal IND-CPA adversary
([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5, pp. 450–451): given `(d, u, v, k)`, pass
`pk = (d, u)` to `adversary.choose`, encrypt the selected message `m` under `k` via
`c ← encryptSym n k m`, and return `adversary.guess` on `(v, c)`. -/
def hashedElGamalCipherToKDFDistinguisher {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let c ← encryptSym n input.2.2.2 m
  let ct := encPair encBits encBits (input.2.2.1, c)
  adversary.guess n choice.2 ct

/-- In the real KDF game, `hashedElGamalCipherToKDFDistinguisher` simulates
`hashedElGamalCipherIdealDDHGame` exactly. -/
@[simp] theorem kdfRealGame_hashedElGamalCipherToKDFDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.kdfRealGame setup H (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit) n =
      F.hashedElGamalCipherIdealDDHGame setup H encryptSym adversary bit n := by
  simp only [kdfRealGame, hashedElGamalCipherToKDFDistinguisher, hashedElGamalCipherIdealDDHGame,
    hashedElGamalCipherIdealDDHGameOn, ↓reduceIte, ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- In the ideal KDF game, `hashedElGamalCipherToKDFDistinguisher` simulates
`hashedElGamalCipherUniformKeyGame` exactly. -/
@[simp] theorem kdfIdealGame_hashedElGamalCipherToKDFDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.kdfIdealGame setup keyLen
        (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit) n =
      F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym adversary bit n := by
  simp only [kdfIdealGame, hashedElGamalCipherToKDFDistinguisher, hashedElGamalCipherUniformKeyGame,
    hashedElGamalCipherUniformKeyGameOn, ↓reduceIte, ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- `hashedElGamalCipherToKDFDistinguisher` is uniform strict PPT whenever `encryptSym` and
`adversary` are. -/
theorem isPPTOn_hashedElGamalCipherToKDFDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : Encryption.AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool
      (fun input =>
        F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit input.1 input.2) := by
  let E0 := encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  let E1 := encPair E0 (encPair (encPair encMsg encMsg) encBits)
  have hchoose := hA.choose.on
  have hguess := hA.guess
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Msg × Msg) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1) E1 encMsg := by
    cases bit <;> fun_prop
  unfold hashedElGamalCipherToKDFDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  refine (hencryptSym.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Msg × Msg) × List Bool =>
      (p.1.1, p.1.2.2.2.2, if bit then p.2.1.2 else p.2.1.1))
    (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        ((ℕ × F.Desc × List Bool × List Bool × List Bool) × (Msg × Msg) × List Bool) × List Bool =>
      (p.1.1.1, p.1.2.2, encPair encBits encBits (p.1.1.2.2.2.1, p.2)))
    (by fun_prop)

/-- Single hidden-bit KDF distinguisher $\mathcal{B}_{\mathrm{kdf}}$ ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, Equation `(11.18)`, pp. 450–451): sample a uniform challenge
bit `bit ← ProbComp.uniform Bool`, run `hashedElGamalCipherToKDFDistinguisher` on `bit`, and output
`guess ^^ bit`. -/
noncomputable def hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let bit ← ProbComp.uniform Bool
  let guess ← F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit n input
  return (guess ^^ bit)

/-- `hashedElGamalCipherToKDFHiddenBitDistinguisher` is uniform strict PPT whenever `encryptSym` and
`adversary` are. -/
theorem isPPTOn_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    {encMsg : Msg ↪ List Bool} {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : Encryption.AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool
      (fun input =>
        F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary
          input.1 input.2) := by
  let E0 := encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  have hFalse := F.isPPTOn_hashedElGamalCipherToKDFDistinguisher hencryptSym hA false
  have hTrue := F.isPPTOn_hashedElGamalCipherToKDFDistinguisher hencryptSym hA true
  have hStep : IsPPTOn (encPair E0 encBool) encBool
      (fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × Bool =>
        F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary p.2 p.1.1 p.1.2) := by
    refine (IsPPTOn.cond (condition := Prod.snd) (by fun_prop)
      (hTrue.preprocess (prepare := Prod.fst) (by fun_prop))
      (hFalse.preprocess (prepare := Prod.fst) (by fun_prop))).congr ?_
    intro ⟨input, bit⟩
    cases bit <;> rfl
  have hXor : ComputableInPolyTime
      (fun p : ((ℕ × F.Desc × List Bool × List Bool × List Bool) × Bool) × Bool => p.2 ^^ p.1.2)
      (encPair (encPair E0 encBool) encBool) encBool := by
    fun_prop
  unfold hashedElGamalCipherToKDFHiddenBitDistinguisher
  exact (isPPTOn_uniform_bool E0).bind_with (hStep.bind_with hXor.isPPTOn)

/-- **Quantitative reduction of general-cipher Hashed ElGamal IND-CPA to DDH, `SecureKDF`, and
Game 2 via two per-bit distinguishers** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
pp. 449–451): the IND-CPA advantage in `hashedElGamalCipherCPAGameOn valid` is bounded by the sum of
the two per-bit DDH advantages, the two per-bit KDF advantages, and the Game 2 advantage in
`hashedElGamalCipherUniformKeyGameOn valid`. -/
theorem advantage_hashedElGamalCipherCPAGameOn_le {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    Game.advantage
      (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary false n)
      (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym (adversary.restrict valid) false) n)
        (F.ddhIdealGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym
            (adversary.restrict valid) false) n) +
      Game.advantage
        (F.kdfRealGame setup H
          (F.hashedElGamalCipherToKDFDistinguisher encryptSym (adversary.restrict valid) false) n)
        (F.kdfIdealGame setup keyLen
          (F.hashedElGamalCipherToKDFDistinguisher encryptSym (adversary.restrict valid) false) n) +
      Game.advantage
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary false n)
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary true n) +
      Game.advantage
        (F.kdfRealGame setup H
          (F.hashedElGamalCipherToKDFDistinguisher encryptSym (adversary.restrict valid) true) n)
        (F.kdfIdealGame setup keyLen
          (F.hashedElGamalCipherToKDFDistinguisher encryptSym (adversary.restrict valid) true) n) +
      Game.advantage
        (F.ddhRealGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym (adversary.restrict valid) true) n)
        (F.ddhIdealGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym
            (adversary.restrict valid) true) n) := by
  let A' := adversary.restrict valid
  rw [← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary false n,
    ← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary true n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary false n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary true n]
  simp only [ddhRealGame_hashedElGamalCipherToDDHDistinguisher,
    ddhIdealGame_hashedElGamalCipherToDDHDistinguisher,
    kdfRealGame_hashedElGamalCipherToKDFDistinguisher,
    kdfIdealGame_hashedElGamalCipherToKDFDistinguisher]
  have h1 := Game.advantage_triangle
    (F.hashedElGamalCipherCPAGame setup H encryptSym A' false n)
    (F.hashedElGamalCipherIdealDDHGame setup H encryptSym A' false n)
    (F.hashedElGamalCipherCPAGame setup H encryptSym A' true n)
  have h2 := Game.advantage_triangle
    (F.hashedElGamalCipherIdealDDHGame setup H encryptSym A' false n)
    (F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' false n)
    (F.hashedElGamalCipherCPAGame setup H encryptSym A' true n)
  have h3 := Game.advantage_triangle
    (F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' false n)
    (F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' true n)
    (F.hashedElGamalCipherCPAGame setup H encryptSym A' true n)
  have h4 := Game.advantage_triangle
    (F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' true n)
    (F.hashedElGamalCipherIdealDDHGame setup H encryptSym A' true n)
    (F.hashedElGamalCipherCPAGame setup H encryptSym A' true n)
  rw [Game.advantage_comm
      (F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' true n)
      (F.hashedElGamalCipherIdealDDHGame setup H encryptSym A' true n),
    Game.advantage_comm
      (F.hashedElGamalCipherIdealDDHGame setup H encryptSym A' true n)
      (F.hashedElGamalCipherCPAGame setup H encryptSym A' true n)] at h4
  exact (h1.trans (add_le_add le_rfl (h2.trans (add_le_add le_rfl
    (h3.trans (add_le_add le_rfl h4)))))).trans_eq (by ac_rfl)

private theorem ddhRealGame_hashedElGamalCipherToDDHHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.ddhRealGame setup
        (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherCPAGame setup H encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [← ddhRealGame_hashedElGamalCipherToDDHDistinguisher, ddhRealGame,
    hashedElGamalCipherToDDHHiddenBitDistinguisher, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind]
  conv_lhs =>
    enter [2, d, 2, α]
    rw [PMF.bind_comm]
  conv_lhs =>
    enter [2, d]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  rfl

private theorem ddhIdealGame_hashedElGamalCipherToDDHHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.ddhIdealGame setup
        (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherIdealDDHGame setup H encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [← ddhIdealGame_hashedElGamalCipherToDDHDistinguisher, ddhIdealGame,
    hashedElGamalCipherToDDHHiddenBitDistinguisher, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind]
  conv_lhs =>
    enter [2, d, 2, α, 2, β]
    rw [PMF.bind_comm]
  conv_lhs =>
    enter [2, d, 2, α]
    rw [PMF.bind_comm]
  conv_lhs =>
    enter [2, d]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  rfl

private theorem kdfRealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.kdfRealGame setup H
        (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherIdealDDHGame setup H encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [← kdfRealGame_hashedElGamalCipherToKDFDistinguisher, kdfRealGame,
    hashedElGamalCipherToKDFHiddenBitDistinguisher, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind]
  conv_lhs =>
    enter [2, d, 2, α, 2, β]
    rw [PMF.bind_comm]
  conv_lhs =>
    enter [2, d, 2, α]
    rw [PMF.bind_comm]
  conv_lhs =>
    enter [2, d]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  rfl

private theorem kdfIdealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.kdfIdealGame setup keyLen
        (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [← kdfIdealGame_hashedElGamalCipherToKDFDistinguisher, kdfIdealGame,
    hashedElGamalCipherToKDFHiddenBitDistinguisher, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind]
  conv_lhs =>
    enter [2, d, 2, α, 2, β]
    rw [PMF.bind_comm]
  conv_lhs =>
    enter [2, d, 2, α]
    rw [PMF.bind_comm]
  conv_lhs =>
    enter [2, d]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  rfl

/-- **Quantitative reduction of general-cipher Hashed ElGamal IND-CPA to DDH, `SecureKDF`, and
Game 2 via single hidden-bit distinguishers** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
Equation `(11.14)`, p. 449):
$$\mathsf{SSadv}[\mathcal{A}, \mathcal{E}_{\mathrm{EG}}] \le
  2 \cdot \mathsf{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] +
  2 \cdot \mathsf{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
  \mathsf{Adv}_{\mathrm{Game\,2}}[\mathcal{A}].$$ -/
theorem advantage_hashedElGamalCipherCPAGameOn_le_two_mul {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    Game.advantage
      (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary false n)
      (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary true n) ≤
      2 * Game.advantage
        (F.ddhRealGame setup
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n)
        (F.ddhIdealGame setup
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n) +
      2 * Game.advantage
        (F.kdfRealGame setup H
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n)
        (F.kdfIdealGame setup keyLen
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n) +
      Game.advantage
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary false n)
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary true n) := by
  let A' := adversary.restrict valid
  rw [← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary false n,
    ← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary true n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary false n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary true n,
    F.ddhRealGame_hashedElGamalCipherToDDHHiddenBitDistinguisher,
    F.ddhIdealGame_hashedElGamalCipherToDDHHiddenBitDistinguisher,
    F.kdfRealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher,
    F.kdfIdealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher]
  have h1 := advantage_le_two_mul_uniform_bool_xor
    (fun bit => F.hashedElGamalCipherCPAGame setup H encryptSym A' bit n)
    (fun bit => F.hashedElGamalCipherIdealDDHGame setup H encryptSym A' bit n)
  have h2 := advantage_le_two_mul_uniform_bool_xor
    (fun bit => F.hashedElGamalCipherIdealDDHGame setup H encryptSym A' bit n)
    (fun bit => F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' bit n)
  exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by ring)

/-- **General-cipher Hashed ElGamal IND-CPA security from DDH, `SecureKDF`, and Game 2
indistinguishability** ([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451): whenever `H`
and `valid` are polynomial-time computable, `encryptSym` is uniform strict PPT, and every uniform
strict PPT adversary has negligible advantage in Game 2 (`hashedElGamalCipherUniformKeyGameOn`),
every uniform strict PPT adversary has negligible advantage in
`hashedElGamalCipherCPAGameOn valid`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn {F : PrimeOrderGroupFamily}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {setup : ℕ → PMF F.Desc} {H : F.Desc × List Bool → List Bool} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH setup) (hKDF : F.SecureKDF setup H keyLen)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary)
    (hSym : Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary false n)
        (F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary true n)) :
    Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary false n)
        (F.hashedElGamalCipherCPAGameOn valid setup H encryptSym adversary true n) := by
  have hA' := hA.restrict hvalid
  have hddh := (hDDH _
    (F.isPPTOn_hashedElGamalCipherToDDHHiddenBitDistinguisher hH hencryptSym hA')).const_mul 2
  have hkdf := (hKDF _
    (F.isPPTOn_hashedElGamalCipherToKDFHiddenBitDistinguisher hencryptSym hA')).const_mul 2
  exact negligible_of_le ((hddh.add hkdf).add hSym)
    (F.advantage_hashedElGamalCipherCPAGameOn_le_two_mul valid setup H keyLen encryptSym adversary)

/-! ### Reduction from Game 2 (`hashedElGamalCipherUniformKeyGameOn`) to `DEMOneTimeINDCPAOn` -/

/-- One-time symmetric-cipher reduction adversary $\mathcal{B}_s$ for general-cipher Hashed ElGamal
([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5, p. 451): given an efficiently samplable
group-description generator `setupProb : ℕ → ProbComp F.Desc` and a PKE adversary `adversary`,
`choose n _` samples `d ← setupProb n` and `a, b ← F.sampleExp n d`, sets
`u = encode (a • g)` and `v = encode (b • g)`, runs `choice ← adversary.choose n (d, u)`, and saves
`(v, choice.2)`; `guess n state ctSym` unpacks `(v, st)` and runs
`adversary.guess n st (v, ctSym)`. -/
noncomputable def hashedElGamalCipherToDEMAdversary {Msg : Type}
    (setupProb : ℕ → ProbComp F.Desc)
    (adversary : Encryption.AdversaryOf Msg) : Encryption.AdversaryOf Msg where
  choose n _ := do
    let d ← setupProb n
    let a ← F.sampleExp n d
    let b ← F.sampleExp n d
    let u := F.encodeElGamalPublicKey (d, a)
    let v := F.encodeElGamalPublicKey (d, b)
    let choice ← adversary.choose n (encPair F.encDesc encBits (d, u))
    return (choice.1, encPair encBits encBits (v, choice.2))
  guess n state ctSym :=
    adversary.guess n (dropFrame state)
      (encPair encBits encBits (unframe state, ctSym))

/-- `hashedElGamalCipherToDEMAdversary setupProb adversary` is an admissible uniform strict PPT
`Encryption.AdversaryOf Msg` whenever `setupProb` and `adversary` are. -/
theorem isPPT_hashedElGamalCipherToDEMAdversary {Msg : Type} {encMsg : Msg ↪ List Bool}
    {setupProb : ℕ → ProbComp F.Desc}
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Encryption.AdversaryOf.IsPPT encMsg
      (F.hashedElGamalCipherToDEMAdversary setupProb adversary) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 F.encDesc
  let E2 := encPair E1 encNat
  let E3 := encPair E2 encNat
  let E4 := encPair E3 (encPair (encPair encMsg encMsg) encBits)
  have hn0 : ComputableInPolyTime (fun p : ℕ × List Bool => p.1) E0 encUnary := by
    dsimp only [E0]; fun_prop
  have hn1 : ComputableInPolyTime (fun p : (ℕ × List Bool) × F.Desc => p.1.1) E1 encUnary := by
    dsimp only [E1, E0]; fun_prop
  have hd1 : ComputableInPolyTime (fun p : (ℕ × List Bool) × F.Desc => p.2) E1 F.encDesc := by
    dsimp only [E1]; fun_prop
  have hn2 : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × F.Desc) × ℕ => p.1.1.1) E2 encUnary := by
    dsimp only [E2, E1, E0]; fun_prop
  have hd2 : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × F.Desc) × ℕ => p.1.2) E2 F.encDesc := by
    dsimp only [E2, E1]; fun_prop
  have hd3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ => p.1.1.2) E3 F.encDesc := by
    dsimp only [E3, E2, E1]; fun_prop
  have ha3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ => p.1.2) E3 encNat := by
    dsimp only [E3, E2]; fun_prop
  have hu3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ =>
        F.encodeElGamalPublicKey (p.1.1.2, p.1.2)) E3 encBits :=
    F.computableInPolyTime_encodeElGamalPublicKey.comp (hd3.prod ha3)
  have hpk3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ =>
        encPair F.encDesc encBits (p.1.1.2, F.encodeElGamalPublicKey (p.1.1.2, p.1.2)))
      E3 encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp (hd3.prod hu3)
  have hn3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ => p.1.1.1.1) E3 encUnary := by
    dsimp only [E3, E2, E1, E0]; fun_prop
  have hchoose3 : IsPPTOn E3 (encPair (encPair encMsg encMsg) encBits)
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ =>
        adversary.choose p.1.1.1.1
          (encPair F.encDesc encBits (p.1.1.2, F.encodeElGamalPublicKey (p.1.1.2, p.1.2)))) :=
    hA.choose.on.preprocess (hn3.prod hpk3)
  have hd4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool => p.1.1.1.2)
      E4 F.encDesc := by
    dsimp only [E4, E3, E2, E1]; fun_prop
  have hb4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool => p.1.2)
      E4 encNat := by
    dsimp only [E4, E3]; fun_prop
  have hv4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool =>
        F.encodeElGamalPublicKey (p.1.1.1.2, p.1.2)) E4 encBits :=
    F.computableInPolyTime_encodeElGamalPublicKey.comp (hd4.prod hb4)
  have hst4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool =>
        encPair encBits encBits (F.encodeElGamalPublicKey (p.1.1.1.2, p.1.2), p.2.2))
      E4 encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp
      (hv4.prod (by dsimp only [E4]; fun_prop))
  have hret4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool =>
        (p.2.1, encPair encBits encBits (F.encodeElGamalPublicKey (p.1.1.1.2, p.1.2), p.2.2)))
      E4 (encPair (encPair encMsg encMsg) encBits) :=
    (by dsimp only [E4]; fun_prop : ComputableInPolyTime _ E4 (encPair encMsg encMsg)).prod hst4
  let EG := encPair encUnary (encPair encBits encBits)
  have hstG : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => dropFrame p.2.1)
      EG encBits :=
    ComputableInPolyTime.dropFrame.comp (by dsimp only [EG]; fun_prop)
  have hvG : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => unframe p.2.1)
      EG encBits :=
    ComputableInPolyTime.unframe.comp (by dsimp only [EG]; fun_prop)
  have hctG : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => encPair encBits encBits (unframe p.2.1, p.2.2))
      EG encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp (hvG.prod (by dsimp only [EG]; fun_prop))
  have hargG : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        (p.1, dropFrame p.2.1, encPair encBits encBits (unframe p.2.1, p.2.2)))
      EG EG :=
    (by dsimp only [EG]; fun_prop : ComputableInPolyTime _ EG encUnary).prod (hstG.prod hctG)
  refine ⟨?_, hA.guess.preprocess hargG⟩
  unfold Probability.IsPPT hashedElGamalCipherToDEMAdversary
  exact (hsetup.preprocess hn0).bind_with
    ((F.isPPTOn_sampleExp hn1 hd1).bind_with
      ((F.isPPTOn_sampleExp hn2 hd2).bind_with
        (hchoose3.bind_with hret4.isPPTOn)))

/-- For each bit `bit : Bool`, the Game 2 distribution `hashedElGamalCipherUniformKeyGameOn` over
`fun m => ProbComp.eval (setupProb m)` with `keyLen n = n` is within `2 / 2 ^ n` in
`Game.advantage` of the standalone one-time symmetric experiment `Encryption.demGameOn` on
`hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)` (two approximate exponent
draws via `sampleExp`, each within `1 / 2 ^ n` of uniform). -/
theorem advantage_hashedElGamalCipherUniformKeyGameOn_demGameOn_le {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ)
    (hkeyLen : keyLen n = n)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary bit n)
      (ProbComp.eval
        (Encryption.demGameOn validSym encryptSym
          (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) bit n)) ≤
      2 / 2 ^ n := by
  let k (d : F.Desc) (α β : ZMod (F.order d)) : Game :=
    let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
    (ProbComp.eval (adversary.choose n pk)).bind fun choice =>
      if valid n pk choice.1.1 choice.1.2 then
        (Cslib.BitString.uniformList n).bind fun key =>
          (ProbComp.eval (encryptSym n key (if bit then choice.1.2 else choice.1.1))).bind fun c =>
            ProbComp.eval (adversary.guess n choice.2
              (encPair encBits encBits (F.encode d (β • F.generator d), c)))
      else
        PMF.pure false
  have hgame2 :
      F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary bit n =
      (ProbComp.eval (setupProb n)).bind fun d =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β => k d α β := by
    simp only [hashedElGamalCipherUniformKeyGameOn, hkeyLen, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, k]
    congr 1; funext d
    congr 1; funext α
    conv_rhs => rw [PMF.bind_comm]
    congr 1; funext choice
    split_ifs <;> simp [PMF.bind_const]
  have hdem :
      ProbComp.eval
        (Encryption.demGameOn validSym encryptSym
          (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) bit n) =
      (ProbComp.eval (setupProb n)).bind fun d =>
        (ProbComp.eval (F.sampleExp n d)).bind fun a =>
          (ProbComp.eval (F.sampleExp n d)).bind fun b =>
            k d (a : ZMod (F.order d)) (b : ZMod (F.order d)) := by
    simp only [Encryption.demGameOn, hashedElGamalCipherToDEMAdversary,
      Encryption.AdversaryOf.restrict, ProbComp.eval_bind, ProbComp.eval_pure,
      Cslib.BitString.eval_sampleList, apply_ite ProbComp.eval,
      PMF.bind_bind, PMF.pure_bind, encPair_apply, encBits_apply,
      unframe_frame_append, dropFrame_frame_append, List.headD_cons, List.tail_cons,
      encodeElGamalPublicKey_eq_encode, k]
    rw [PMF.bind_comm]
    congr 1; funext d
    rw [PMF.bind_comm]
    congr 1; funext a
    rw [PMF.bind_comm]
    congr 1; funext b
    rw [PMF.bind_comm]
    congr 1; funext choice
    by_cases hv :
        valid n (encPair F.encDesc encBits (d, F.encode d ((a : ZMod (F.order d)) • F.generator d)))
          choice.1.1 choice.1.2 = true
    · have hvs := hvalid_imp d (F.encode d ((a : ZMod (F.order d)) • F.generator d))
        choice.1.1 choice.1.2 hv
      simp only [encPair_apply, encBits_apply] at hv
      simp [hv, hvs]
    · simp only [Bool.not_eq_true, encPair_apply, encBits_apply] at hv
      by_cases hvs : validSym n [] choice.1.1 choice.1.2 = true <;>
        simp [hv, hvs, PMF.bind_const]
  rw [hgame2, hdem]
  refine Game.advantage_bind_le_nnreal (ProbComp.eval (setupProb n)) _ _ fun d => ?_
  rw [Game.advantage_comm]
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (ProbComp.eval (F.sampleExp n d)).bind fun b =>
        k d α (b : ZMod (F.order d))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n d (fun α =>
    (ProbComp.eval (F.sampleExp n d)).bind fun b => k d α (b : ZMod (F.order d)))
  have h2 := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun α => F.advantage_bind_sampleExp_le n d (k d α))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n := add_le_add h1 h2
    _ = 2 / 2 ^ n := by ring

/-- **Quantitative bridge from Game 2 (`hashedElGamalCipherUniformKeyGameOn`) to standalone
symmetric-cipher security (`Encryption.demGameOn`)**: the Game 2 advantage is bounded by the
`Encryption.demGameOn` advantage of
`hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)` plus `4 / 2 ^ n`. -/
theorem advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hkeyLen : keyLen n = n)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary false n)
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary true n) ≤
      Game.advantage
        (ProbComp.eval
          (Encryption.demGameOn validSym encryptSym
            (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) false n))
        (ProbComp.eval
          (Encryption.demGameOn validSym encryptSym
            (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) true n)) +
      4 / 2 ^ n := by
  have hf := F.advantage_hashedElGamalCipherUniformKeyGameOn_demGameOn_le
    valid validSym setupProb keyLen encryptSym adversary false n hkeyLen hvalid_imp
  have ht := F.advantage_hashedElGamalCipherUniformKeyGameOn_demGameOn_le
    valid validSym setupProb keyLen encryptSym adversary true n hkeyLen hvalid_imp
  have htri1 := Game.advantage_triangle
    (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
      keyLen encryptSym adversary false n)
    (ProbComp.eval
      (Encryption.demGameOn validSym encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) false n))
    (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
      keyLen encryptSym adversary true n)
  have htri2 := Game.advantage_triangle
    (ProbComp.eval
      (Encryption.demGameOn validSym encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) false n))
    (ProbComp.eval
      (Encryption.demGameOn validSym encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) true n))
    (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
      keyLen encryptSym adversary true n)
  rw [Game.advantage_comm
    (ProbComp.eval
      (Encryption.demGameOn validSym encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb
          (adversary.restrict valid)) true n))] at htri2
  have hcomb := htri1.trans (add_le_add hf (htri2.trans (add_le_add le_rfl ht)))
  calc _ ≤ (2 : ℝ≥0) / 2 ^ n +
        (Game.advantage
          (ProbComp.eval
            (Encryption.demGameOn validSym encryptSym
              (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) false n))
          (ProbComp.eval
            (Encryption.demGameOn validSym encryptSym
              (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) true n)) +
        2 / 2 ^ n) := hcomb
    _ = _ := by ring

/-- **Native approximate-sampling version of Equation `(11.14)` for Theorem 11.5 via DDH,
`SecureKDF`, and standalone symmetric-cipher security (`Encryption.demGameOn`)** ([BonehShoup2023],
Section 11.5.2, Theorem 11.5, Equation `(11.14)`, p. 449): combining the exact PMF-level Equation
`(11.14)` bound `advantage_hashedElGamalCipherCPAGameOn_le_two_mul` with the `sampleExp`
Game 2 bridge `advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn` adds `4 / 2 ^ n` for the
two approximate exponent draws per branch:
$$\mathsf{SSadv}[\mathcal{A}, \mathcal{E}_{\mathrm{EG}}] \le
  2 \cdot \mathsf{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] +
  2 \cdot \mathsf{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
  \mathsf{SSadv}[\mathcal{B}_s, \mathcal{E}_s] + \frac{4}{2^n}.$$ -/
theorem advantage_hashedElGamalCipherCPAGameOn_le_demGameOn {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (H : F.Desc × List Bool → List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hkeyLen : keyLen n = n)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherCPAGameOn valid (fun m => ProbComp.eval (setupProb m))
        H encryptSym adversary false n)
      (F.hashedElGamalCipherCPAGameOn valid (fun m => ProbComp.eval (setupProb m))
        H encryptSym adversary true n) ≤
      2 * Game.advantage
        (F.ddhRealGame (fun m => ProbComp.eval (setupProb m))
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n)
        (F.ddhIdealGame (fun m => ProbComp.eval (setupProb m))
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n) +
      2 * Game.advantage
        (F.kdfRealGame (fun m => ProbComp.eval (setupProb m)) H
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n)
        (F.kdfIdealGame (fun m => ProbComp.eval (setupProb m)) keyLen
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n) +
      Game.advantage
        (ProbComp.eval
          (Encryption.demGameOn validSym encryptSym
            (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) false n))
        (ProbComp.eval
          (Encryption.demGameOn validSym encryptSym
            (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) true n)) +
      4 / 2 ^ n := by
  have h1 := F.advantage_hashedElGamalCipherCPAGameOn_le_two_mul
    valid (fun m => ProbComp.eval (setupProb m)) H keyLen encryptSym adversary n
  have h2 := F.advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn
    valid validSym setupProb keyLen encryptSym adversary n hkeyLen hvalid_imp
  exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by ring)

/-- One-time symmetric IND-CPA security (`Encryption.DEMOneTimeINDCPAOn`) implies negligibility of
the Game 2 advantage (`hashedElGamalCipherUniformKeyGameOn`) whenever the setup law is efficiently
samplable (`setupProb : ℕ → ProbComp F.Desc`), `keyLen n = n`, and `valid` implies `validSym`. -/
theorem negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeINDCPAOn {Msg : Type}
    {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDEM : Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hkeyLen : ∀ n, keyLen n = n)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
          keyLen encryptSym adversary false n)
        (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
          keyLen encryptSym adversary true n) := by
  have hA' := hA.restrict hvalid
  have hdem := hDEM (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))
    (F.isPPT_hashedElGamalCipherToDEMAdversary hsetup hA')
  have herr : Negligible (fun n : ℕ => (4 : ℝ≥0) / 2 ^ n) := by
    simpa only [div_eq_mul_inv, inv_pow, Nat.cast_ofNat] using
      (negligible_geometric (ratio := 2⁻¹) (by norm_num)).polynomiallyBounded_mul
        (p := fun _ => 4) (by fun_prop)
  exact negligible_of_le (hdem.add herr) fun n =>
    F.advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn
      valid validSym setupProb keyLen encryptSym adversary n (hkeyLen n) (hvalid_imp n)

/-- **Boneh–Shoup Theorem 11.5 from DDH, `SecureKDF`, and `Encryption.DEMOneTimeINDCPAOn`**
([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451): for any efficiently samplable setup
`setupProb : ℕ → ProbComp F.Desc` (`setup n = ProbComp.eval (setupProb n)`), `keyLen n = n`, and
admissibility predicate `valid` implying `validSym`, if `F.DDH`, `F.SecureKDF`, and
`Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym` hold, then every uniform strict PPT
adversary has negligible advantage in `hashedElGamalCipherCPAGameOn valid`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeINDCPAOn
    {F : PrimeOrderGroupFamily} {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {H : F.Desc × List Bool → List Bool} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hKDF : F.SecureKDF (fun n => ProbComp.eval (setupProb n)) H keyLen)
    (hDEM : Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hkeyLen : ∀ n, keyLen n = n)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherCPAGameOn valid (fun n => ProbComp.eval (setupProb n))
          H encryptSym adversary false n)
        (F.hashedElGamalCipherCPAGameOn valid (fun n => ProbComp.eval (setupProb n))
          H encryptSym adversary true n) :=
  hDDH.negligible_hashedElGamalCipherCPAGameOn hKDF hvalid hH hencryptSym hA
    (F.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeINDCPAOn
      hDEM hsetup hkeyLen hvalid hvalid_imp hA)

/-- Executable `ProbComp` sampler for `F.seededSetup`: sample `d ← setupProb n`, then conditional on
`d`, sample a uniform seed `s ← Cslib.BitString.sampleList (seedLen n d)` and output `(d, s)`. -/
noncomputable def seededSetupProb (setupProb : ℕ → ProbComp F.Desc)
    (seedLen : ℕ → F.Desc → ℕ) (n : ℕ) : ProbComp F.withSeed.Desc := do
  let d ← setupProb n
  let s ← Cslib.BitString.sampleList (seedLen n d)
  return (d, s)

/-- `ProbComp.eval (F.seededSetupProb setupProb seedLen n)` equals
`F.seededSetup (fun m => ProbComp.eval (setupProb m)) seedLen n`. -/
@[simp] theorem eval_seededSetupProb (setupProb : ℕ → ProbComp F.Desc)
    (seedLen : ℕ → F.Desc → ℕ) (n : ℕ) :
    ProbComp.eval (F.seededSetupProb setupProb seedLen n) =
      F.seededSetup (fun m => ProbComp.eval (setupProb m)) seedLen n := by
  simp only [seededSetupProb, seededSetup, ProbComp.eval_bind, ProbComp.eval_pure,
    Cslib.BitString.eval_sampleList, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

/-- `F.seededSetupProb setupProb seedLen` is uniform strict PPT whenever `setupProb` is uniform
strict PPT and `seedLen` is computable in polynomial time in unary. -/
theorem isPPTOn_seededSetupProb {setupProb : ℕ → ProbComp F.Desc}
    {seedLen : ℕ → F.Desc → ℕ}
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hseed : ComputableInPolyTime (fun p : ℕ × F.Desc => seedLen p.1 p.2)
      (encPair encUnary F.encDesc) encUnary) :
    IsPPTOn encUnary F.withSeed.encDesc (F.seededSetupProb setupProb seedLen) := by
  let E1 := encPair encUnary F.encDesc
  let E2 := encPair E1 encBits
  have hsample : IsPPTOn E1 encBits
      (fun p : ℕ × F.Desc => Cslib.BitString.sampleList (seedLen p.1 p.2)) :=
    ComputableInPolyTime.sampleList hseed
  have hret : ComputableInPolyTime
      (fun p : (ℕ × F.Desc) × List Bool => (p.1.2, p.2))
      E2 F.withSeed.encDesc := by
    dsimp only [E2, E1, withSeed]
    fun_prop
  unfold seededSetupProb
  exact hsetup.bind_with (hsample.bind_with hret.isPPTOn)

/-- **General-cipher Hashed ElGamal IND-CPA security with `linearHashKDF` from `DDH` and
`Encryption.DEMOneTimeINDCPAOn` alone** ([BonehShoup2023], Section 8.10.4, Theorem 8.11, p. 334, and
Section 11.5.2, Theorem 11.5, pp. 449–451): combining `DDH.withSeed`, `secureKDF_linearHashKDF`,
`isPPTOn_seededSetupProb`, and `DDH.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeINDCPAOn`
yields IND-CPA security of general-cipher Hashed ElGamal instantiated with `linearHashKDF` under
`F.DDH` and `Encryption.DEMOneTimeINDCPAOn` alone, with no separate KDF assumption. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_linearHashKDF {F : PrimeOrderGroupFamily}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen bound : F.Desc → ℕ} {qMin : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hDEM : Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hkey_poly : ComputableInPolyTime keyLen F.encDesc encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hq0 : ∀ n, 0 < qMin n)
    (hkey : ∀ n, ∀ d ∈ (ProbComp.eval (setupProb n)).support, keyLen d = n)
    (hbound : ∀ n, ∀ d ∈ (ProbComp.eval (setupProb n)).support,
      ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq : ∀ n, ∀ d ∈ (ProbComp.eval (setupProb n)).support, qMin n ≤ F.order d)
    (hneg : Negligible fun n => (2 : ℝ≥0) ^ n / (qMin n : ℝ≥0))
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.withSeed.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.withSeed.hashedElGamalCipherCPAGameOn valid
          (F.seededSetup (fun m => ProbComp.eval (setupProb m))
            (F.linearHashSeedLen (fun n => n) bound))
          (F.linearHashKDF keyLen bound) encryptSym adversary false n)
        (F.withSeed.hashedElGamalCipherCPAGameOn valid
          (F.seededSetup (fun m => ProbComp.eval (setupProb m))
            (F.linearHashSeedLen (fun n => n) bound))
          (F.linearHashKDF keyLen bound) encryptSym adversary true n) := by
  have hseed_poly := F.computableInPolyTime_linearHashSeedLen ComputableInPolyTime.id' hbound_poly
  have hsetup_seeded := F.isPPTOn_seededSetupProb hsetup hseed_poly
  have hDDH_seeded :
      F.withSeed.DDH (fun n => ProbComp.eval (F.seededSetupProb setupProb
        (F.linearHashSeedLen (fun n => n) bound) n)) := by
    simp only [F.eval_seededSetupProb]
    exact hDDH.withSeed hseed_poly
  have hKDF_seeded :
      F.withSeed.SecureKDF (fun n => ProbComp.eval (F.seededSetupProb setupProb
        (F.linearHashSeedLen (fun n => n) bound) n))
        (F.linearHashKDF keyLen bound) (fun n => n) := by
    simp only [F.eval_seededSetupProb]
    exact F.secureKDF_linearHashKDF (fun m => ProbComp.eval (setupProb m))
      keyLen bound (fun n => n) hq0 hkey hbound hq hneg
  simpa only [F.eval_seededSetupProb] using
    hDDH_seeded.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeINDCPAOn
      hKDF_seeded hDEM hsetup_seeded (fun _ => rfl) hvalid hvalid_imp
      (F.computableInPolyTime_linearHashKDF hkey_poly hbound_poly) hencryptSym hA

end Cslib.Crypto.PrimeOrderGroupFamily
