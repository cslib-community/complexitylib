/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ElGamal.KDF
public import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
public import CslibFrontier.Crypto.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PMFSwap

/-!
# General-Cipher Hashed ElGamal ([BonehShoup2023], Section 11.5, Theorem 11.5)

This module generalizes Hashed ElGamal ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1,
and Section 11.5.2, Theorem 11.5, pp. 448–451) from the one-time pad specialization in
`CslibFrontier/Crypto/Computational/ElGamal.lean` to an arbitrary semantically secure symmetric
cipher
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
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherRandomDDHGameOn`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherUniformKeyGameOn`: PMF-level IND-CPA
  experiments and hybrids for general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5.2,
  Theorem 11.5, pp. 449–451).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDDHHiddenBitDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToKDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToKDFHiddenBitDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherToDEMAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.seededSetupProb`: per-bit and hidden-bit DDH and KDF
  reductions, symmetric-cipher (`DEMOneTimeKeyINDCPAOn` / `DEMOneTimeINDCPAOn`) reduction adversary,
  and executable seeded setup sampler for Theorem 11.5 ([BonehShoup2023], Section 11.5.2,
  pp. 449–451). The KDF reductions are typed `KDFDistinguisher`s, and each DDH reduction runs its
  KDF reduction on the key derived from the candidate shared element (`kdfToDDHDistinguisher`), so
  the random DDH game is the real KDF game (`ddhRandomGame_kdfToDDHDistinguisher`).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCipherDecrypt_hashedElGamalCipherEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeHashedElGamalCipher_hashedElGamalCipherEncrypt`:
  decryption correctness for general-cipher Hashed ElGamal.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le_two_mul`,
  `PrimeOrderGroupFamily.advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn`,
  `PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le_demKeyGameOn`,
  `PrimeOrderGroupFamily.advantage_hashedElGamalCipherUniformKeyGameOn_le_demGameOn`,
  `PrimeOrderGroupFamily.advantage_hashedElGamalCipherCPAGameOn_le_demGameOn`:
  two-distinguisher and single hidden-bit distinguisher quantitative bounds for Theorem 11.5
  (matching Equation `(11.14)` of [BonehShoup2023], p. 449), together with the native
  approximate-sampling (`sampleExp`, adding `4 / 2 ^ n`) bridge to standalone
  symmetric-cipher security at arbitrary (`Encryption.demKeyGameOn`) and normalized (`n`-bit,
  `Encryption.demGameOn`) key lengths.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCipherCPAGameOn`,
  `PrimeOrderGroupFamily.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeKeyINDCPAOn`,
  `PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeKeyINDCPAOn`,
  `DDH.negligible_hashedElGamalCipherCPAGameOn_linearHashKDF_of_demOneTimeKeyINDCPAOn`,
  and their normalized `n`-bit-key specializations
  (`PrimeOrderGroupFamily.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeINDCPAOn`,
  `PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeINDCPAOn`,
  `PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCipherCPAGameOn_linearHashKDF`):
  Theorem 11.5 IND-CPA security in `hashedElGamalCipherCPAGameOn` from `DDH`, `SecureKDF`, and
  `DEMOneTimeKeyINDCPAOn` (or `DEMOneTimeINDCPAOn`), plus the `linearHashKDF` instantiation at
  arbitrary and normalized key lengths, which replaces the `SecureKDF` hypothesis by a lower bound
  `qMin n` on the group order of every description in the support of the setup sampler, with
  `2 ^ outLen n / qMin n` (or `2 ^ n / qMin n`) negligible.

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
  let k := H (input.1, F.smul (input.1, F.encRand input, F.encPk input))
  (F.smul (input.1, F.encRand input, F.encode input.1 (F.generator input.1)),
    encSym (k, F.encMsg input))

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
      (encPair encBits encBits) :=
  let hd := ComputableInPolyTime.fst F.encDesc (encPair encBits (encPair encMsg encNat))
  let hr := ComputableInPolyTime.snd F.encDesc (encPair encBits (encPair encMsg encNat))
  let hb := hr.snd'.snd'
  (F.computableInPolyTime_smul.comp'
    (hd.prod (hb.prod (F.computableInPolyTime_generator.comp' hd)))).prod
    (hencSym.comp'
      ((hH.comp'
        (hd.prod (F.computableInPolyTime_smul.comp' (hd.prod (hb.prod hr.fst'))))).prod
        hr.snd'.fst'))

/-- Word-level Hashed ElGamal decryption with a general symmetric cipher `decSym`: given
`(d, a, encode v, c)`, derive `k = H (d, encode (a • v))` and compute `decSym (k, c)`. -/
def decodeHashedElGamalCipher {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (decSym : List Bool × List Bool → Msg)
    (input : F.Desc × ℕ × List Bool × List Bool) : Msg :=
  decSym (H (input.1, F.smul (input.1, F.decSk input, F.decEph input)), F.decBody input)

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
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encMsg :=
  let hd := ComputableInPolyTime.fst F.encDesc (encPair encNat (encPair encBits encBits))
  let hr := ComputableInPolyTime.snd F.encDesc (encPair encNat (encPair encBits encBits))
  hdecSym.comp'
    ((hH.comp'
      (hd.prod (F.computableInPolyTime_smul.comp' (hd.prod (hr.fst'.prod hr.snd'.fst'))))).prod
      hr.snd'.snd')

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
  if valid n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
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
  simp only [pmf_norm, hashedElGamalCPAGame, hashedElGamalCipherCPAGame,
    hashedElGamalCipherCPAGameOn, ↓reduceIte]

/-- **Game 1** for general-cipher Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of
Theorem 11.5, p. 450): replace the Diffie–Hellman shared element `(α * β) • g` with an independent
uniform group element `γ • g`. -/
noncomputable def hashedElGamalCipherRandomDDHGameOn {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  if valid n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let γ ← PMF.uniformOfFintype (ZMod (F.order d))
    let k := H (d, F.encode d (γ • F.generator d))
    let c ← ProbComp.eval (encryptSym n k m)
    let ct := encPair encBits encBits (F.encode d (β • F.generator d), c)
    ProbComp.eval (adversary.guess n choice.2 ct)
  else
    pure false

/-- Unrestricted Game 1 for general-cipher Hashed ElGamal. -/
noncomputable abbrev hashedElGamalCipherRandomDDHGame {Msg : Type} (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) : Game :=
  F.hashedElGamalCipherRandomDDHGameOn (fun _ _ _ _ => true) setup H encryptSym adversary bit n

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
  if valid n pk (Encryption.ChoiceOut.msg₀ choice) (Encryption.ChoiceOut.msg₁ choice) then
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
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
  simp only [pmf_norm, hashedElGamalCipherCPAGame, hashedElGamalCipherCPAGameOn,
    Encryption.AdversaryOf.restrict, ↓reduceIte, List.headD_cons, List.tail_cons]
  congr 1 with d : 1
  congr 1 with α : 1
  congr 1 with choice : 1
  cases valid n (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))
      choice.1.1 choice.1.2 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]

/-- Running the unrestricted `hashedElGamalCipherRandomDDHGame` on `adversary.restrict valid` has
the same output distribution as running `hashedElGamalCipherRandomDDHGameOn valid` on
`adversary`. -/
theorem hashedElGamalCipherRandomDDHGame_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.hashedElGamalCipherRandomDDHGame setup H encryptSym (adversary.restrict valid) bit n =
      F.hashedElGamalCipherRandomDDHGameOn valid setup H encryptSym adversary bit n := by
  simp only [pmf_norm, hashedElGamalCipherRandomDDHGame, hashedElGamalCipherRandomDDHGameOn,
    Encryption.AdversaryOf.restrict, ↓reduceIte, List.headD_cons, List.tail_cons]
  congr 1 with d : 1
  congr 1 with α : 1
  congr 1 with choice : 1
  cases valid n (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))
      choice.1.1 choice.1.2 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]

/-- Running the unrestricted `hashedElGamalCipherUniformKeyGame` on `adversary.restrict valid` has
the same output distribution as running `hashedElGamalCipherUniformKeyGameOn valid` on
`adversary`. -/
theorem hashedElGamalCipherUniformKeyGame_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (setup : ℕ → PMF F.Desc)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym (adversary.restrict valid) bit n =
      F.hashedElGamalCipherUniformKeyGameOn valid setup keyLen encryptSym adversary bit n := by
  simp only [pmf_norm, hashedElGamalCipherUniformKeyGame, hashedElGamalCipherUniformKeyGameOn,
    Encryption.AdversaryOf.restrict, ↓reduceIte, List.headD_cons, List.tail_cons]
  congr 1 with d : 1
  congr 1 with α : 1
  congr 1 with choice : 1
  cases valid n (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))
      choice.1.1 choice.1.2 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.bind_const]

/-- Per-bit KDF distinguisher constructed from a general-cipher Hashed ElGamal IND-CPA adversary
([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5, pp. 450–451): given `(d, u, v, k)`, pass
`pk = (d, encode u)` to `adversary.choose`, encrypt the selected message `m` under `k` via
`c ← encryptSym n k m`, and return `adversary.guess` on `(encode v, c)`. -/
def hashedElGamalCipherToKDFDistinguisher {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) : F.KDFDistinguisher :=
  fun n d u v key => do
    let pk := encPair F.encDesc encBits (d, F.encode d u)
    let choice ← adversary.choose n pk
    let m := if bit then Encryption.ChoiceOut.msg₁ choice else Encryption.ChoiceOut.msg₀ choice
    let c ← encryptSym n key m
    let ct := encPair encBits encBits (F.encode d v, c)
    adversary.guess n choice.2 ct

/-- Per-bit DDH distinguisher constructed from a general-cipher Hashed ElGamal IND-CPA adversary
([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5, p. 450):
`hashedElGamalCipherToKDFDistinguisher` run with the key `H (d, encode w)` derived from the
candidate shared element `w`. -/
abbrev hashedElGamalCipherToDDHDistinguisher {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) : F.DDHDistinguisher :=
  F.kdfToDDHDistinguisher H (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit)

/-- In the real DDH game, `hashedElGamalCipherToDDHDistinguisher` simulates
`hashedElGamalCipherCPAGame` exactly. -/
@[simp] theorem ddhRealGame_hashedElGamalCipherToDDHDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.hashedElGamalCipherToDDHDistinguisher H encryptSym adversary bit) n =
      F.hashedElGamalCipherCPAGame setup H encryptSym adversary bit n := by
  simp only [ddhRealGame, eval_ddhRealExperiment, kdfToDDHDistinguisher,
    hashedElGamalCipherToKDFDistinguisher, hashedElGamalCipherCPAGame,
    hashedElGamalCipherCPAGameOn, ↓reduceIte, ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  pmf_swap

/-- In the real KDF game, `hashedElGamalCipherToKDFDistinguisher` simulates Game 1
(`hashedElGamalCipherRandomDDHGame`) exactly. By `ddhRandomGame_kdfToDDHDistinguisher`, this is
also the random DDH game for `hashedElGamalCipherToDDHDistinguisher`. -/
@[simp] theorem kdfRealGame_hashedElGamalCipherToKDFDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.kdfRealGame setup H (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit) n =
      F.hashedElGamalCipherRandomDDHGame setup H encryptSym adversary bit n := by
  simp only [kdfRealGame, hashedElGamalCipherToKDFDistinguisher, hashedElGamalCipherRandomDDHGame,
    hashedElGamalCipherRandomDDHGameOn, ↓reduceIte, ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  pmf_swap

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
    hashedElGamalCipherUniformKeyGameOn, ↓reduceIte, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  pmf_swap

/-- `hashedElGamalCipherToKDFDistinguisher` is uniform strict PPT whenever `encryptSym` and
`adversary` are. The DDH reduction `hashedElGamalCipherToDDHDistinguisher` is then uniform strict
PPT by `isPPT_kdfToDDHDistinguisher`. -/
theorem isPPT_hashedElGamalCipherToKDFDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : Encryption.AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    (F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit).IsPPT := by
  have hm : ComputableInPolyTime
      (fun p : F.KDFInput × Encryption.ChoiceOut Msg => if bit then p.2.1.2 else p.2.1.1)
      (encPair F.encKDFInput (Encryption.encChoiceOut encMsg)) encMsg :=
    .ite' (encC := encBool) (.const bit) (by fun_prop) (by fun_prop)
  simp only [KDFDistinguisher.IsPPT, hashedElGamalCipherToKDFDistinguisher]
  exact (hA.choose.on.preprocess
      (prepare := fun x : F.KDFInput =>
        (x.secParam, encPair F.encDesc encBits (x.groupParameters, F.encode _ x.leftPublic)))
      (.prod (by fun_prop) (.encoding_comp (by fun_prop)))).bind_with
    ((hencryptSym.preprocess
        (prepare := fun p : F.KDFInput × Encryption.ChoiceOut Msg =>
          (p.1.secParam, p.1.key, if bit then p.2.1.2 else p.2.1.1))
        (.prod (by fun_prop) (.prod (by fun_prop) hm))).bind_with
      (hA.guess.preprocess
        (prepare := fun q : (F.KDFInput × Encryption.ChoiceOut Msg) × List Bool =>
          (q.1.1.secParam, q.1.2.2, encPair encBits encBits (F.encode _ q.1.1.rightPublic, q.2)))
        (.prod (by fun_prop) (.prod (by fun_prop) (.encoding_comp (.prod (by fun_prop)
          (by fun_prop)))))))

/-- Single hidden-bit KDF distinguisher $\mathcal{B}_{\mathrm{kdf}}$ ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, Equation `(11.18)`, pp. 450–451): sample a uniform challenge
bit `bit ← ProbComp.uniform Bool`, run `hashedElGamalCipherToKDFDistinguisher` on `bit`, and output
`guess ^^ bit`. -/
noncomputable def hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) : F.KDFDistinguisher :=
  fun n d u v key => do
    let bit ← ProbComp.uniform Bool
    let guess ← F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary bit n d u v key
    return (guess ^^ bit)

/-- Single hidden-bit DDH distinguisher $\mathcal{B}_{\mathrm{ddh}}$ ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, Figure 11.4 and Equation `(11.17)`, p. 450):
`hashedElGamalCipherToKDFHiddenBitDistinguisher` run with the key `H (d, encode w)` derived from the
candidate shared element `w`. It samples a uniform challenge bit, runs
`hashedElGamalCipherToDDHDistinguisher` on it, and outputs `guess ^^ bit`. -/
noncomputable abbrev hashedElGamalCipherToDDHHiddenBitDistinguisher {Msg : Type}
    (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) : F.DDHDistinguisher :=
  F.kdfToDDHDistinguisher H (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary)

/-- `hashedElGamalCipherToKDFHiddenBitDistinguisher` is uniform strict PPT whenever `encryptSym` and
`adversary` are. The DDH reduction `hashedElGamalCipherToDDHHiddenBitDistinguisher` is then
uniform strict PPT by `isPPT_kdfToDDHDistinguisher`. -/
theorem isPPT_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    {encMsg : Msg ↪ List Bool} {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : Encryption.AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary).IsPPT := by
  unfold KDFDistinguisher.IsPPT
  let E0 := F.encKDFInput
  let E1 := encPair E0 encBool
  let hp1 := ComputableInPolyTime.fst E0 encBool
  let hp2 := ComputableInPolyTime.snd E0 encBool
  let hq1 := ComputableInPolyTime.fst E1 encBool
  let hq2 := ComputableInPolyTime.snd E1 encBool
  have hFalse := F.isPPT_hashedElGamalCipherToKDFDistinguisher hencryptSym hA false
  have hTrue := F.isPPT_hashedElGamalCipherToKDFDistinguisher hencryptSym hA true
  have hStep : IsPPTOn E1 encBool
      (fun p : F.KDFInput × Bool =>
        F.hashedElGamalCipherToKDFDistinguisher encryptSym adversary p.2 p.1.secParam
          p.1.groupParameters p.1.leftPublic p.1.rightPublic p.1.key) :=
    (IsPPTOn.cond' hp2 (hTrue.preprocess hp1) (hFalse.preprocess hp1)).congr
      (fun ⟨_, bit⟩ => by cases bit <;> rfl)
  exact (isPPTOn_uniform_bool E0).bind_with
    (hStep.bind_with
      ((ComputableInPolyTime.bool_xor.comp' (hq2.prod (hp2.comp' hq1))).isPPTOn))

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
        (F.ddhRandomGame setup
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
        (F.ddhRandomGame setup
          (F.hashedElGamalCipherToDDHDistinguisher H encryptSym
            (adversary.restrict valid) true) n) := by
  let A' := adversary.restrict valid
  rw [← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary false n,
    ← F.hashedElGamalCipherCPAGame_restrict valid setup H encryptSym adversary true n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary false n,
    ← F.hashedElGamalCipherUniformKeyGame_restrict valid setup keyLen encryptSym adversary true n]
  simp only [ddhRealGame_hashedElGamalCipherToDDHDistinguisher,
    ddhRandomGame_kdfToDDHDistinguisher,
    kdfRealGame_hashedElGamalCipherToKDFDistinguisher,
    kdfIdealGame_hashedElGamalCipherToKDFDistinguisher]
  game_trans
    [F.hashedElGamalCipherRandomDDHGame setup H encryptSym A' false n,
     F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' false n,
     F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym A' true n,
     F.hashedElGamalCipherRandomDDHGame setup H encryptSym A' true n]
    using [le_rfl, le_rfl, le_rfl, le_rfl, le_rfl]

private theorem ddhRealGame_hashedElGamalCipherToDDHHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.ddhRealGame setup
        (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherCPAGame setup H encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [pmf_norm, ← ddhRealGame_hashedElGamalCipherToDDHDistinguisher, ddhRealGame,
    eval_ddhRealExperiment, kdfToDDHDistinguisher,
    hashedElGamalCipherToKDFHiddenBitDistinguisher, ProbComp.eval_uniform]
  pmf_swap

private theorem kdfRealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.kdfRealGame setup H
        (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherRandomDDHGame setup H encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [pmf_norm, ← kdfRealGame_hashedElGamalCipherToKDFDistinguisher, kdfRealGame,
    hashedElGamalCipherToKDFHiddenBitDistinguisher, ProbComp.eval_uniform]
  pmf_swap

private theorem kdfIdealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher {Msg : Type}
    (setup : ℕ → PMF F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ) :
    F.kdfIdealGame setup keyLen
        (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym adversary) n =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (F.hashedElGamalCipherUniformKeyGame setup keyLen encryptSym adversary bit n).map
          (fun guess => guess ^^ bit) := by
  simp only [pmf_norm, ← kdfIdealGame_hashedElGamalCipherToKDFDistinguisher, kdfIdealGame,
    hashedElGamalCipherToKDFHiddenBitDistinguisher, ProbComp.eval_uniform]
  pmf_swap

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
        (F.ddhRandomGame setup
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
    F.ddhRandomGame_kdfToDDHDistinguisher,
    F.kdfRealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher,
    F.kdfIdealGame_hashedElGamalCipherToKDFHiddenBitDistinguisher]
  have h1 := advantage_le_two_mul_uniform_bool_xor
    (fun bit => F.hashedElGamalCipherCPAGame setup H encryptSym A' bit n)
    (fun bit => F.hashedElGamalCipherRandomDDHGame setup H encryptSym A' bit n)
  have h2 := advantage_le_two_mul_uniform_bool_xor
    (fun bit => F.hashedElGamalCipherRandomDDHGame setup H encryptSym A' bit n)
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
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
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
  have hkdfPPT := F.isPPT_hashedElGamalCipherToKDFHiddenBitDistinguisher hencryptSym hA'
  have hddh := hDDH _ (F.isPPT_kdfToDDHDistinguisher hH hkdfPPT)
  have hkdf := hKDF _ hkdfPPT
  negligible using
    F.advantage_hashedElGamalCipherCPAGameOn_le_two_mul valid setup H keyLen encryptSym adversary

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
  let EChoice := encPair (encPair encMsg encMsg) encBits
  let E4 := encPair E3 EChoice
  have hn0 : ComputableInPolyTime (fun p : ℕ × List Bool => p.1) E0 encUnary :=
    ComputableInPolyTime.fst encUnary encBits
  have hp1 := ComputableInPolyTime.fst E0 F.encDesc
  have hd1 : ComputableInPolyTime (fun p : (ℕ × List Bool) × F.Desc => p.2) E1 F.encDesc :=
    ComputableInPolyTime.snd E0 F.encDesc
  have hn1 : ComputableInPolyTime (fun p : (ℕ × List Bool) × F.Desc => p.1.1) E1 encUnary :=
    hp1.fst'
  have hp2 := ComputableInPolyTime.fst E1 encNat
  have hn2 : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × F.Desc) × ℕ => p.1.1.1) E2 encUnary := hp2.fst'.fst'
  have hd2 : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × F.Desc) × ℕ => p.1.2) E2 F.encDesc := hp2.snd'
  have hp3 := ComputableInPolyTime.fst E2 encNat
  have hd3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ => p.1.1.2) E3 F.encDesc := hp3.fst'.snd'
  have ha3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ => p.1.2) E3 encNat := hp3.snd'
  have hu3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ =>
        F.encodeElGamalPublicKey (p.1.1.2, p.1.2)) E3 encBits :=
    F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd3.prod ha3)
  have hpk3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ =>
        encPair F.encDesc encBits (p.1.1.2, F.encodeElGamalPublicKey (p.1.1.2, p.1.2)))
      E3 encBits :=
    (hd3.prod hu3).encoding_comp
  have hn3 : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ => p.1.1.1.1) E3 encUnary :=
    hp3.fst'.fst'.fst'
  have hchoose3 : IsPPTOn E3 EChoice
      (fun p : (((ℕ × List Bool) × F.Desc) × ℕ) × ℕ =>
        adversary.choose p.1.1.1.1
          (encPair F.encDesc encBits (p.1.1.2, F.encodeElGamalPublicKey (p.1.1.2, p.1.2)))) :=
    hA.choose.on.preprocess (hn3.prod hpk3)
  have hp4 := ComputableInPolyTime.fst E3 EChoice
  have hq4 := ComputableInPolyTime.snd E3 EChoice
  have hd4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool => p.1.1.1.2)
      E4 F.encDesc := hp4.fst'.fst'.snd'
  have hb4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool => p.1.2)
      E4 encNat := hp4.snd'
  have hv4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool =>
        F.encodeElGamalPublicKey (p.1.1.1.2, p.1.2)) E4 encBits :=
    F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd4.prod hb4)
  have hst4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool =>
        encPair encBits encBits (F.encodeElGamalPublicKey (p.1.1.1.2, p.1.2), p.2.2))
      E4 encBits :=
    (hv4.prod hq4.snd').encoding_comp
  have hret4 : ComputableInPolyTime
      (fun p : ((((ℕ × List Bool) × F.Desc) × ℕ) × ℕ) × (Msg × Msg) × List Bool =>
        (p.2.1, encPair encBits encBits (F.encodeElGamalPublicKey (p.1.1.1.2, p.1.2), p.2.2)))
      E4 EChoice :=
    hq4.fst'.prod hst4
  let EG := encPair encUnary (encPair encBits encBits)
  have hqG := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  have hstG : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => dropFrame p.2.1)
      EG encBits :=
    ComputableInPolyTime.dropFrame.comp' hqG.fst'
  have hvG : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => unframe p.2.1)
      EG encBits :=
    ComputableInPolyTime.unframe.comp' hqG.fst'
  have hctG : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => encPair encBits encBits (unframe p.2.1, p.2.2))
      EG encBits :=
    (hvG.prod hqG.snd').encoding_comp
  have hargG : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        (p.1, dropFrame p.2.1, encPair encBits encBits (unframe p.2.1, p.2.2)))
      EG EG :=
    (ComputableInPolyTime.fst encUnary (encPair encBits encBits)).prod (hstG.prod hctG)
  refine ⟨?_, hA.guess.preprocess hargG⟩
  unfold Probability.IsPPT hashedElGamalCipherToDEMAdversary
  exact (hsetup.preprocess hn0).bind_with
    ((F.isPPTOn_sampleExp hn1 hd1).bind_with
      ((F.isPPTOn_sampleExp hn2 hd2).bind_with
        (hchoose3.bind_with hret4.isPPTOn)))

/-- For each bit `bit : Bool` and any key-length function `keyLen : ℕ → ℕ`, the Game 2 distribution
`hashedElGamalCipherUniformKeyGameOn` over `fun m => ProbComp.eval (setupProb m)` is within
`2 / 2 ^ n` in `Game.advantage` of the standalone one-time symmetric experiment
`Encryption.demKeyGameOn` on the wrapper adversary
`hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)`
(two approximate exponent draws via `sampleExp`, each within `1 / 2 ^ n` of uniform). -/
theorem advantage_hashedElGamalCipherUniformKeyGameOn_demKeyGameOn_le {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary bit n)
      (ProbComp.eval
        (Encryption.demKeyGameOn validSym keyLen encryptSym
          (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) bit n)) ≤
      2 / 2 ^ n := by
  let k (d : F.Desc) (α β : ZMod (F.order d)) : Game :=
    let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
    (ProbComp.eval (adversary.choose n pk)).bind fun choice =>
      if valid n pk choice.1.1 choice.1.2 then
        (Cslib.BitString.uniformList (keyLen n)).bind fun key =>
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
    simp only [hashedElGamalCipherUniformKeyGameOn, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, k]
    pmf_swap with d α choice
    split_ifs <;> simp only [PMF.bind_const]
  have hdem :
      ProbComp.eval
        (Encryption.demKeyGameOn validSym keyLen encryptSym
          (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) bit n) =
      (ProbComp.eval (setupProb n)).bind fun d =>
        (ProbComp.eval (F.sampleExp n d)).bind fun a =>
          (ProbComp.eval (F.sampleExp n d)).bind fun b =>
            k d (a : ZMod (F.order d)) (b : ZMod (F.order d)) := by
    simp only [pmf_norm, Encryption.demKeyGameOn, hashedElGamalCipherToDEMAdversary,
      Encryption.AdversaryOf.restrict, Cslib.BitString.eval_sampleList, apply_ite ProbComp.eval,
      encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append, List.headD_cons,
      List.tail_cons, encodeElGamalPublicKey_eq_encode, k]
    pmf_swap with d a b choice
    by_cases hv :
        valid n (encPair F.encDesc encBits (d, F.encode d ((a : ZMod (F.order d)) • F.generator d)))
          choice.1.1 choice.1.2 = true
    · have hvs := hvalid_imp d (F.encode d ((a : ZMod (F.order d)) • F.generator d))
        choice.1.1 choice.1.2 hv
      simp only [encPair_apply, encBits_apply] at hv
      simp only [hv, hvs, ↓reduceIte]
    · simp only [Bool.not_eq_true, encPair_apply, encBits_apply] at hv
      by_cases hvs : validSym n [] choice.1.1 choice.1.2 = true <;>
        simp only [hv, hvs, Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
  rw [hgame2, hdem]
  peel_binds d
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExp_pair_le n d (k d)

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
  rw [← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ bit hkeyLen]
  exact F.advantage_hashedElGamalCipherUniformKeyGameOn_demKeyGameOn_le
    valid validSym setupProb keyLen encryptSym adversary bit n hvalid_imp

/-- **Quantitative bridge from Game 2 (`hashedElGamalCipherUniformKeyGameOn`) to standalone
symmetric-cipher security at arbitrary key length (`Encryption.demKeyGameOn`)**: for any
`keyLen : ℕ → ℕ`, the Game 2 advantage is bounded by the `Encryption.demKeyGameOn` advantage of
`hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)` plus `4 / 2 ^ n`. -/
theorem advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hvalid_imp : ∀ d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true) :
    Game.advantage
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary false n)
      (F.hashedElGamalCipherUniformKeyGameOn valid (fun m => ProbComp.eval (setupProb m))
        keyLen encryptSym adversary true n) ≤
      Encryption.advantage (Encryption.demKeyGameOn validSym keyLen encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))) n +
      4 / 2 ^ n := by
  have hf := F.advantage_hashedElGamalCipherUniformKeyGameOn_demKeyGameOn_le
    valid validSym setupProb keyLen encryptSym adversary false n hvalid_imp
  have ht := F.advantage_hashedElGamalCipherUniformKeyGameOn_demKeyGameOn_le
    valid validSym setupProb keyLen encryptSym adversary true n hvalid_imp
  rw [Encryption.advantage]
  game_trans
    [ProbComp.eval
       (Encryption.demKeyGameOn validSym keyLen encryptSym
         (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) false n),
     ProbComp.eval
       (Encryption.demKeyGameOn validSym keyLen encryptSym
         (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid)) true n)]
    using [hf, le_rfl, ht]

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
      Encryption.advantage (Encryption.demGameOn validSym encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))) n +
      4 / 2 ^ n := by
  rw [Encryption.advantage,
    ← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ false hkeyLen,
    ← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ true hkeyLen]
  exact F.advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn
    valid validSym setupProb keyLen encryptSym adversary n hvalid_imp

/-- **Native approximate-sampling version of Equation `(11.14)` for Theorem 11.5 via DDH,
`SecureKDF`, and standalone symmetric-cipher security at arbitrary key length
(`Encryption.demKeyGameOn`)** ([BonehShoup2023], Section 11.5.2, Theorem 11.5, Equation `(11.14)`,
p. 449): combining the exact PMF-level Equation `(11.14)` bound
`advantage_hashedElGamalCipherCPAGameOn_le_two_mul` with the `sampleExp` Game 2 bridge
`advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn` adds `4 / 2 ^ n` for the two
approximate exponent draws per branch:
$$\mathsf{SSadv}[\mathcal{A}, \mathcal{E}_{\mathrm{EG}}] \le
  2 \cdot \mathsf{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] +
  2 \cdot \mathsf{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
  \mathsf{SSadv}[\mathcal{B}_s, \mathcal{E}_s] + \frac{4}{2^n}.$$ -/
theorem advantage_hashedElGamalCipherCPAGameOn_le_demKeyGameOn {Msg : Type}
    (valid validSym : ℕ → List Bool → Msg → Msg → Bool)
    (setupProb : ℕ → ProbComp F.Desc) (H : F.Desc × List Bool → List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
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
        (F.ddhRandomGame (fun m => ProbComp.eval (setupProb m))
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n) +
      2 * Game.advantage
        (F.kdfRealGame (fun m => ProbComp.eval (setupProb m)) H
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n)
        (F.kdfIdealGame (fun m => ProbComp.eval (setupProb m)) keyLen
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n) +
      Encryption.advantage (Encryption.demKeyGameOn validSym keyLen encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))) n +
      4 / 2 ^ n := by
  have h1 := F.advantage_hashedElGamalCipherCPAGameOn_le_two_mul
    valid (fun m => ProbComp.eval (setupProb m)) H keyLen encryptSym adversary n
  have h2 := F.advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn
    valid validSym setupProb keyLen encryptSym adversary n hvalid_imp
  exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by ring)

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
        (F.ddhRandomGame (fun m => ProbComp.eval (setupProb m))
          (F.hashedElGamalCipherToDDHHiddenBitDistinguisher H encryptSym
            (adversary.restrict valid)) n) +
      2 * Game.advantage
        (F.kdfRealGame (fun m => ProbComp.eval (setupProb m)) H
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n)
        (F.kdfIdealGame (fun m => ProbComp.eval (setupProb m)) keyLen
          (F.hashedElGamalCipherToKDFHiddenBitDistinguisher encryptSym
            (adversary.restrict valid)) n) +
      Encryption.advantage (Encryption.demGameOn validSym encryptSym
        (F.hashedElGamalCipherToDEMAdversary setupProb (adversary.restrict valid))) n +
      4 / 2 ^ n := by
  rw [Encryption.advantage,
    ← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ false hkeyLen,
    ← Encryption.demKeyGameOn_eq_demGameOn_of_eq validSym keyLen encryptSym _ true hkeyLen]
  exact F.advantage_hashedElGamalCipherCPAGameOn_le_demKeyGameOn
    valid validSym setupProb H keyLen encryptSym adversary n hvalid_imp

/-- One-time symmetric IND-CPA security at arbitrary key length (`Encryption.DEMOneTimeKeyINDCPAOn`)
implies negligibility of the Game 2 advantage (`hashedElGamalCipherUniformKeyGameOn`) whenever the
setup law is efficiently samplable (`setupProb : ℕ → ProbComp F.Desc`) and `valid` implies
`validSym`. -/
theorem negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeKeyINDCPAOn {Msg : Type}
    {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDEM : Encryption.DEMOneTimeKeyINDCPAOn validSym encMsg keyLen encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
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
  negligible using fun n =>
    F.advantage_hashedElGamalCipherUniformKeyGameOn_le_demKeyGameOn
      valid validSym setupProb keyLen encryptSym adversary n (hvalid_imp n)

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
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
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
          keyLen encryptSym adversary true n) :=
  F.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeKeyINDCPAOn
    (hDEM.demOneTimeKeyINDCPAOn hkeyLen) hsetup hvalid hvalid_imp hA

/-- **Boneh–Shoup Theorem 11.5 from DDH, `SecureKDF`, and `Encryption.DEMOneTimeKeyINDCPAOn` at
arbitrary key length** ([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451): for any
efficiently samplable setup `setupProb : ℕ → ProbComp F.Desc`
(`setup n = ProbComp.eval (setupProb n)`), key-length function `keyLen : ℕ → ℕ`, and admissibility
predicate `valid` implying `validSym`, if `F.DDH`, `F.SecureKDF`, and
`Encryption.DEMOneTimeKeyINDCPAOn validSym encMsg keyLen encryptSym` hold, then every uniform strict
PPT adversary has negligible advantage in `hashedElGamalCipherCPAGameOn valid`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeKeyINDCPAOn
    {F : PrimeOrderGroupFamily} {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {H : F.Desc × List Bool → List Bool} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hKDF : F.SecureKDF (fun n => ProbComp.eval (setupProb n)) H keyLen)
    (hDEM : Encryption.DEMOneTimeKeyINDCPAOn validSym encMsg keyLen encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
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
    (F.negligible_hashedElGamalCipherUniformKeyGameOn_of_demOneTimeKeyINDCPAOn
      hDEM hsetup hvalid hvalid_imp hA)

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
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.hashedElGamalCipherCPAGameOn valid (fun n => ProbComp.eval (setupProb n))
          H encryptSym adversary false n)
        (F.hashedElGamalCipherCPAGameOn valid (fun n => ProbComp.eval (setupProb n))
          H encryptSym adversary true n) :=
  hDDH.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeKeyINDCPAOn
    hKDF (hDEM.demOneTimeKeyINDCPAOn hkeyLen) hsetup hvalid hvalid_imp hH hencryptSym hA

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
  simp only [pmf_norm, seededSetupProb, seededSetup, Cslib.BitString.eval_sampleList]

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
      E2 F.withSeed.encDesc :=
    (ComputableInPolyTime.fst E1 encBits).snd'.prod (ComputableInPolyTime.snd E1 encBits)
  unfold seededSetupProb
  exact hsetup.bind_with (hsample.bind_with hret.isPPTOn)

/-- **General-cipher Hashed ElGamal IND-CPA security with `linearHashKDF` at arbitrary key length
`outLen : ℕ → ℕ` from `DDH` and `Encryption.DEMOneTimeKeyINDCPAOn`** ([BonehShoup2023],
Section 8.10.4, Theorem 8.11, p. 334, and Section 11.5.2, Theorem 11.5, pp. 449–451): combining
`DDH.withSeed`, `secureKDF_linearHashKDF`, `isPPTOn_seededSetupProb`, and
`DDH.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeKeyINDCPAOn` yields IND-CPA security of
general-cipher Hashed ElGamal instantiated with `linearHashKDF` at any polynomial-time key length
`outLen` under `F.DDH` and `Encryption.DEMOneTimeKeyINDCPAOn`, with no `SecureKDF` hypothesis.
In its place the theorem requires `LinearHashKDFConditions` for the strict PPT setup sampler
`setupProb` with output length `outLen`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_linearHashKDF_of_demOneTimeKeyINDCPAOn
    {F : PrimeOrderGroupFamily} {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen bound : F.Desc → ℕ} {outLen qMin : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hDEM : Encryption.DEMOneTimeKeyINDCPAOn validSym encMsg outLen encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hKDF : F.LinearHashKDFConditions (fun n => ProbComp.eval (setupProb n)) keyLen bound outLen
      qMin)
    (hout_poly : ComputableInPolyTime outLen encUnary encUnary)
    (hkey_poly : ComputableInPolyTime keyLen F.encDesc encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.withSeed.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) :
    Negligible fun n =>
      Game.advantage
        (F.withSeed.hashedElGamalCipherCPAGameOn valid
          (F.seededSetup (fun m => ProbComp.eval (setupProb m))
            (F.linearHashSeedLen outLen bound))
          (F.linearHashKDF keyLen bound) encryptSym adversary false n)
        (F.withSeed.hashedElGamalCipherCPAGameOn valid
          (F.seededSetup (fun m => ProbComp.eval (setupProb m))
            (F.linearHashSeedLen outLen bound))
          (F.linearHashKDF keyLen bound) encryptSym adversary true n) := by
  have hseed_poly := F.computableInPolyTime_linearHashSeedLen hout_poly hbound_poly
  have hsetup_seeded := F.isPPTOn_seededSetupProb hsetup hseed_poly
  have hDDH_seeded :
      F.withSeed.DDH (fun n => ProbComp.eval (F.seededSetupProb setupProb
        (F.linearHashSeedLen outLen bound) n)) := by
    simp only [F.eval_seededSetupProb]
    exact hDDH.withSeed hseed_poly
  have hKDF_seeded :
      F.withSeed.SecureKDF (fun n => ProbComp.eval (F.seededSetupProb setupProb
        (F.linearHashSeedLen outLen bound) n))
        (F.linearHashKDF keyLen bound) outLen := by
    simp only [F.eval_seededSetupProb]
    exact F.secureKDF_linearHashKDF hKDF
  simpa only [F.eval_seededSetupProb] using
    hDDH_seeded.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeKeyINDCPAOn
      hKDF_seeded hDEM hsetup_seeded hvalid hvalid_imp
      (F.computableInPolyTime_linearHashKDF hkey_poly hbound_poly) hencryptSym hA

/-- **General-cipher Hashed ElGamal IND-CPA security with `linearHashKDF` from `DDH` and
`Encryption.DEMOneTimeINDCPAOn`** ([BonehShoup2023], Section 8.10.4, Theorem 8.11, p. 334, and
Section 11.5.2, Theorem 11.5, pp. 449–451): combining `DDH.withSeed`, `secureKDF_linearHashKDF`,
`isPPTOn_seededSetupProb`, and `DDH.negligible_hashedElGamalCipherCPAGameOn_of_demOneTimeINDCPAOn`
yields IND-CPA security of general-cipher Hashed ElGamal instantiated with `linearHashKDF` under
`F.DDH` and `Encryption.DEMOneTimeINDCPAOn`, with no `SecureKDF` hypothesis. In its place the
theorem requires `LinearHashKDFConditions` for the strict PPT setup sampler `setupProb` with output
length `n`. -/
theorem DDH.negligible_hashedElGamalCipherCPAGameOn_linearHashKDF {F : PrimeOrderGroupFamily}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid validSym : ℕ → List Bool → Msg → Msg → Bool}
    {setupProb : ℕ → ProbComp F.Desc} {keyLen bound : F.Desc → ℕ} {qMin : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => ProbComp.eval (setupProb n)))
    (hDEM : Encryption.DEMOneTimeINDCPAOn validSym encMsg encryptSym)
    (hsetup : IsPPTOn encUnary F.encDesc setupProb)
    (hKDF : F.LinearHashKDFConditions (fun n => ProbComp.eval (setupProb n)) keyLen bound
      (fun n => n) qMin)
    (hkey_poly : ComputableInPolyTime keyLen F.encDesc encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hvalid_imp : ∀ n d u m₀ m₁,
      valid n (encPair F.withSeed.encDesc encBits (d, u)) m₀ m₁ = true →
        validSym n [] m₀ m₁ = true)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m))
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
          (F.linearHashKDF keyLen bound) encryptSym adversary true n) :=
  hDDH.negligible_hashedElGamalCipherCPAGameOn_linearHashKDF_of_demOneTimeKeyINDCPAOn
    hDEM hsetup hKDF ComputableInPolyTime.id' hkey_poly hbound_poly
    hvalid hvalid_imp hencryptSym hA

end Cslib.Crypto.PrimeOrderGroupFamily
