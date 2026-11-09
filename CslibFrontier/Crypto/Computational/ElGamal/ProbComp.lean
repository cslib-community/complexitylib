/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ElGamal
public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.FourHop
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance

/-!
# Strict-PPT ElGamal Key Generation, KEM Encapsulation, and `Encryption.INDCPAOn` Bridges

This module defines uniform strict-PPT (`IsPPTOn`) key generation, encapsulation, decapsulation,
and encryption for multiplicative ElGamal and Hashed ElGamal ([BonehShoup2023], Section 11.5,
pp. 445–446, Remark 11.1, Section 11.5.2, Theorem 11.5, pp. 449–451, Exercise 11.5(a), p. 459, and
Exercise 11.9, pp. 460–461) using `ProbComp.sampleModNat`, and connects the PMF-level ElGamal games
in `CslibFrontier/Crypto/Computational/ElGamal.lean` directly to `Encryption.KEMINDCPA`,
`Encryption.INDCPAOf`, `Encryption.INDCPAOn`, and `Encryption.INDCPA`.

* **Paraphrase of [BonehShoup2023], Section 11.5 (p. 445) and Remark 11.1 (p. 446):** key
  generation samples $\alpha \leftarrow \mathbb{Z}_q$ and outputs $(pk = \alpha \cdot g, sk =
  \alpha)$; in the $\mathcal{E}'_{\mathrm{EG}}$ variant of Remark 11.1, encapsulation/encryption
  samples $\beta \leftarrow \mathbb{Z}_q$, sets $v = \beta \cdot g$ and $w = \beta \cdot u$,
  derives the symmetric key $k = H(w)$, and encrypts $m$ under $k$; decapsulation/decryption
  computes $w = \alpha \cdot v$, recovers $k = H(w)$, and decrypts $c$ under $k$.
* **Paraphrase of [BonehShoup2023], Exercise 11.5(a) (p. 459) and Exercise 11.9 (pp. 460–461):**
  multiplicative ElGamal encrypts a group element $m \in G$ as $(\beta \cdot g, \beta \cdot u + m)$
  and is IND-CPA secure under DDH; Hashed ElGamal acts as an IND-CPA secure KEM under DDH and
  `SecureKDF`, and composing it with any one-time semantically secure DEM yields an IND-CPA secure
  public-key encryption scheme. The KDF output key space is uniform `keyLen n`-bit words;
  `n` remains the security parameter controlling the modular-sampling error `4 / 2 ^ n`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalKeyGenProb`: uniform strict-PPT ElGamal key
  generation.
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalEncapsProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecaps`: uniform strict-PPT Hashed ElGamal KEM
  encapsulation and deterministic polynomial-time decapsulation.
* `Cslib.Crypto.PrimeOrderGroupFamily.kemToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kemToKDFDistinguisher`: DDH and KDF reductions from a KEM
  distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalEncryptProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecryptDet`: uniform strict-PPT multiplicative ElGamal
  encryption and deterministic polynomial-time decryption.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecaps_hashedElGamalEncapsProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecryptDet_elGamalEncryptProb`: support-level
  decapsulation and decryption correctness.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_kemGame_hashedElGamalEncapsProb_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.kemINDCPA_hashedElGamalEncapsProb`: quantitative KEM
  advantage bound and `Encryption.KEMINDCPA` security of Hashed ElGamal under `DDH` and
  `SecureKDF`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcpaOf_hybrid_hashedElGamal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcpaOn_hybrid_hashedElGamal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.wordINDCPA_hybrid_hashedElGamal`: Theorem 11.5 via
  `Encryption.INDCPAOf`, `Encryption.INDCPAOn`, and `Encryption.WordINDCPA` for any one-time
  semantically secure symmetric cipher (`Encryption.DEMOneTimeINDCPAOf` /
  `Encryption.DEMOneTimeINDCPAOn` / `Encryption.DEMOneTimeWordINDCPA`).
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcpaOn_elGamalEncryptProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcpa_elGamalBitEncryptProb`: multiplicative and bit
  ElGamal satisfy `Encryption.INDCPAOn` and `Encryption.INDCPA` under `DDH`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5 (pp. 445–446, Remark 11.1), Section 11.5.2
  (pp. 448–451, Theorem 11.5), Exercise 11.5(a) (p. 459), and Exercise 11.9 (pp. 460–461).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Encryption Game
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

private theorem dropFrame_encPair_encBits {α : Type} (e : α ↪ List Bool) (a : α)
    (s : List Bool) : dropFrame (encPair e encBits (a, s)) = s := by
  simp only [encPair_apply, dropFrame_frame_append, encBits_apply]

private theorem unframe_encPair_encBits (p : List Bool × List Bool) :
    unframe (encPair encBits encBits p) = p.1 := by
  simp only [encPair_apply, unframe_frame_append, encBits_apply]

private theorem dropFrame_encPair_encBits_pair (p : List Bool × List Bool) :
    dropFrame (encPair encBits encBits p) = p.2 := by
  simp only [encPair_apply, dropFrame_frame_append, encBits_apply]

/-- Probabilistic polynomial-time ElGamal key generation for a group description family
`d : ℕ → F.Desc` ([BonehShoup2023], Section 11.5, p. 445, and Exercise 11.5, p. 459): sample
`a ← sampleExp n (d n)` and output
`(encPair F.encDesc encBits (d n, encode (a • g)), encNat a)`. -/
noncomputable def elGamalKeyGenProb (d : ℕ → F.Desc) (n : ℕ) :
    ProbComp (List Bool × List Bool) := do
  let a ← F.sampleExp n (d n)
  return (encPair F.encDesc encBits (d n, F.encodeElGamalPublicKey (d n, a)), encNat a)

/-- `elGamalKeyGenProb` is uniformly strict PPT whenever `d` is computable in polynomial time. -/
theorem isPPTOn_elGamalKeyGenProb {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn encUnary (encPair encBits encBits) (F.elGamalKeyGenProb d) := by
  unfold elGamalKeyGenProb
  let hd1 := hd.comp' (ComputableInPolyTime.fst encUnary encNat)
  let ha := ComputableInPolyTime.snd encUnary encNat
  have hbody := ((hd1.prod
    (F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd1.prod ha))).encoding_comp.prod
    ha.encoding_comp).isPPTOn
  exact (F.isPPTOn_sampleExp .id' hd).bind_with hbody

/-- Probabilistic polynomial-time Hashed ElGamal KEM encapsulation for a group description family
`d : ℕ → F.Desc` ([BonehShoup2023], Section 11.5, p. 445, Remark 11.1, p. 446, and Exercise 11.9,
pp. 460–461): sample `b ← sampleExp n (d n)`, unpack `u = dropFrame pk`, and output
`(H (d n, encode (b • u)), encode (b • g))`. -/
noncomputable def hashedElGamalEncapsProb (H : F.Desc × List Bool → List Bool)
    (d : ℕ → F.Desc) (n : ℕ) (pk : List Bool) : ProbComp (List Bool × List Bool) := do
  let b ← F.sampleExp n (d n)
  let u := dropFrame pk
  return (H (d n, F.smul (d n, b, u)),
    F.smul (d n, b, F.encode (d n) (F.generator (d n))))

/-- `hashedElGamalEncapsProb` is uniformly strict PPT whenever `H` and `d` are computable in
polynomial time. -/
theorem isPPTOn_hashedElGamalEncapsProb {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => F.hashedElGamalEncapsProb H d p.1 p.2) := by
  unfold hashedElGamalEncapsProb
  let E0 := encPair encUnary encBits
  let hp := ComputableInPolyTime.fst E0 encNat; let hd1 := hd.comp' hp.fst'
  let hb := ComputableInPolyTime.snd E0 encNat
  let hu := ComputableInPolyTime.dropFrame.comp' hp.snd'
  have hbody := ((hH.comp'
    (hd1.prod (F.computableInPolyTime_smul.comp' (hd1.prod (hb.prod hu))))).prod
    (F.computableInPolyTime_smul.comp'
      (hd1.prod (hb.prod (F.computableInPolyTime_generator.comp' hd1))))).isPPTOn
  exact (F.isPPTOn_sampleExp (ComputableInPolyTime.fst encUnary encBits)
    (hd.comp' (ComputableInPolyTime.fst encUnary encBits))).bind_with hbody

/-- Deterministic polynomial-time Hashed ElGamal KEM decapsulation ([BonehShoup2023], Section 11.5,
p. 445, Remark 11.1, p. 446): given secret key `sk = encNat a` and KEM ciphertext
`ctKem = encode (b • g)`, recover `H (d n, encode (a • v))`. -/
def hashedElGamalDecaps (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (n : ℕ) (sk ctKem : List Bool) : List Bool :=
  H (d n, F.smul (d n, ofBits sk, ctKem))

/-- `hashedElGamalDecaps` is computable in polynomial time whenever `H` and `d` are. -/
theorem computableInPolyTime_hashedElGamalDecaps {H : F.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => F.hashedElGamalDecaps H d n sk ct)
      (encKeyedInput encBits) encBits := by
  let hd1 := hd.comp' (ComputableInPolyTime.fst encUnary (encPair encBits encBits))
  let hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  have h := hH.comp' (hd1.prod (F.computableInPolyTime_smul.comp'
    (hd1.prod ((ComputableInPolyTime.bitsToNat.comp' hrest.fst').prod hrest.snd'))))
  exact h

/-- **Hashed ElGamal KEM decapsulation correctness**: for any `n : ℕ`, any `(pk, sk)` in the
support of `elGamalKeyGenProb d n`, and any `(k, ctKem)` in the support of
`hashedElGamalEncapsProb H d n pk`, `hashedElGamalDecaps H d n sk ctKem = k`. -/
theorem hashedElGamalDecaps_hashedElGamalEncapsProb (H : F.Desc × List Bool → List Bool)
    (d : ℕ → F.Desc) (n : ℕ) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (F.elGamalKeyGenProb d n)).support)
    {encapsulated : List Bool × List Bool}
    (hencaps : encapsulated ∈ (ProbComp.eval (F.hashedElGamalEncapsProb H d n keys.1)).support) :
    F.hashedElGamalDecaps H d n keys.2 encapsulated.2 = encapsulated.1 := by
  simp only [elGamalKeyGenProb, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hkeys
  rcases hkeys with ⟨a, _, rfl⟩
  simp only [hashedElGamalEncapsProb, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hencaps
  rcases hencaps with ⟨b, _, rfl⟩
  have hbits : ofBits (encNat a) = a := Nat.foldr_bit_bits a
  simp only [hashedElGamalDecaps, hbits, dropFrame_encPair_encBits,
    encodeElGamalPublicKey_eq_encode, F.smul_encode, smul_smul, mul_comm (a : ZMod (F.order (d n)))]

/-- DDH distinguisher constructed from a `KEMAdversary` (`Distinguisher`) for
`(elGamalKeyGenProb d, hashedElGamalEncapsProb H d)`. -/
def kemToDDHDistinguisher (H : F.Desc × List Bool → List Bool)
    (distinguisher : Distinguisher) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  let pk := encPair F.encDesc encBits (input.1, F.ddhPk input)
  distinguisher n
    (encPair encBits (encPair encBits encBits)
      (pk, (H (input.1, F.ddhShared input), F.ddhEph input)))

/-- KDF distinguisher constructed from a `KEMAdversary` (`Distinguisher`) for
`(elGamalKeyGenProb d, hashedElGamalEncapsProb H d)`. -/
def kemToKDFDistinguisher (distinguisher : Distinguisher) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  let pk := encPair F.encDesc encBits (input.1, F.ddhPk input)
  distinguisher n
    (encPair encBits (encPair encBits encBits) (pk, (F.ddhShared input, F.ddhEph input)))

/-- `ddhIdealGame` for `kemToDDHDistinguisher` is identical to `kdfRealGame` for
`kemToKDFDistinguisher`. -/
theorem ddhIdealGame_kemToDDHDistinguisher_eq_kdfRealGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (distinguisher : Distinguisher) (n : ℕ) :
    F.ddhIdealGame setup (F.kemToDDHDistinguisher H distinguisher) n =
      F.kdfRealGame setup H (F.kemToKDFDistinguisher distinguisher) n :=
  rfl

/-- `kemToDDHDistinguisher` is uniform strict PPT whenever `H` is polynomial time and
`distinguisher` is uniform strict PPT. -/
theorem isPPTOn_kemToDDHDistinguisher {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {distinguisher : Distinguisher} (hD : IsPPT encBool distinguisher) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.kemToDDHDistinguisher H distinguisher input.1 input.2) := by
  let E1 := encPair F.encDesc (encPair encBits (encPair encBits encBits))
  let h1 := ComputableInPolyTime.snd encUnary E1
  let h2 := h1.snd'
  let h3 := h2.snd'
  have hprep := (ComputableInPolyTime.fst encUnary E1).prod
    (((h1.fst'.prod h2.fst').encoding_comp.prod
      ((hH.comp' (h1.fst'.prod h3.snd')).prod h3.fst')).encoding_comp)
  exact hD.on.preprocess hprep

/-- `kemToKDFDistinguisher` is uniform strict PPT whenever `distinguisher` is: it is
`kemToDDHDistinguisher` with the identity key derivation `H (d, w) = w`. -/
theorem isPPTOn_kemToKDFDistinguisher {distinguisher : Distinguisher}
    (hD : IsPPT encBool distinguisher) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.kemToKDFDistinguisher distinguisher input.1 input.2) :=
  F.isPPTOn_kemToDDHDistinguisher (H := fun p => p.2) (ComputableInPolyTime.snd F.encDesc encBits)
    hD

private theorem advantage_eval_kemRealGame_ddhRealGame_le
    (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (distinguisher : Distinguisher) (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (kemRealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n))
      (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n) ≤
      2 / 2 ^ n := by
  let k (α β : ZMod (F.order (d n))) : Game :=
    ProbComp.eval (distinguisher n
      (encPair encBits (encPair encBits encBits)
        (encPair F.encDesc encBits (d n, F.encode (d n) (α • F.generator (d n))),
          (H (d n, F.encode (d n) ((α * β) • F.generator (d n))),
            F.encode (d n) (β • F.generator (d n))))))
  have hreal :
      ProbComp.eval
        (kemRealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n) =
      (ProbComp.eval (F.sampleExp n (d n))).bind fun a =>
        (ProbComp.eval (F.sampleExp n (d n))).bind fun b =>
          k (a : ZMod (F.order (d n))) (b : ZMod (F.order (d n))) := by
    simp only [kemRealGame, kemRealGameWith,
    elGamalKeyGenProb, hashedElGamalEncapsProb, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, dropFrame_encPair_encBits,
      encodeElGamalPublicKey_eq_encode, F.smul_encode, smul_smul,
      mul_comm _ (_ : ZMod (F.order (d n))), k]
  have hddh :
      F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n =
      (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun β => k α β := by
    simp only [ddhRealGame, kemToDDHDistinguisher, PMF.monad_bind_eq_bind, PMF.pure_bind, k]
  rw [hreal, hddh]
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun α =>
      (ProbComp.eval (F.sampleExp n (d n))).bind fun b =>
        k α (b : ZMod (F.order (d n)))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n (d n) (fun α =>
    (ProbComp.eval (F.sampleExp n (d n))).bind fun b => k α (b : ZMod (F.order (d n))))
  have h2 := advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order (d n)))) _ _
    (fun α => F.advantage_bind_sampleExp_le n (d n) (k α))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n := add_le_add h1 h2
    _ = 2 / 2 ^ n := by ring

private theorem advantage_kdfIdealGame_eval_kemIdealGame_le (keyLen : ℕ → ℕ)
    (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (distinguisher : Distinguisher) (n : ℕ) :
    Game.advantage
      (F.kdfIdealGame (fun m => PMF.pure (d m)) keyLen
        (F.kemToKDFDistinguisher distinguisher) n)
      (ProbComp.eval
        (kemIdealGame keyLen (F.elGamalKeyGenProb d)
        (F.hashedElGamalEncapsProb H d) distinguisher n)) ≤
      2 / 2 ^ n := by
  let k (α β : ZMod (F.order (d n))) : Game :=
    (Cslib.BitString.uniformList (keyLen n)).bind fun pad =>
      ProbComp.eval (distinguisher n
        (encPair encBits (encPair encBits encBits)
          (encPair F.encDesc encBits (d n, F.encode (d n) (α • F.generator (d n))),
            (pad, F.encode (d n) (β • F.generator (d n))))))
  have hideal :
      ProbComp.eval
        (kemIdealGame keyLen (F.elGamalKeyGenProb d)
        (F.hashedElGamalEncapsProb H d) distinguisher n) =
      (ProbComp.eval (F.sampleExp n (d n))).bind fun a =>
        (ProbComp.eval (F.sampleExp n (d n))).bind fun b =>
          k (a : ZMod (F.order (d n))) (b : ZMod (F.order (d n))) := by
    simp only [kemIdealGame, kemIdealGameWith, kemRealGameWith,
    elGamalKeyGenProb, hashedElGamalEncapsProb, ProbComp.eval_bind,
      ProbComp.eval_pure, Cslib.BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind,
      encodeElGamalPublicKey_eq_encode, F.smul_encode, k]
  have hkdf :
      F.kdfIdealGame (fun m => PMF.pure (d m)) keyLen
        (F.kemToKDFDistinguisher distinguisher) n =
      (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun β => k α β := by
    simp only [kdfIdealGame, kemToKDFDistinguisher, PMF.monad_bind_eq_bind, PMF.pure_bind, k]
  rw [Game.advantage_comm, hideal, hkdf]
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun α =>
      (ProbComp.eval (F.sampleExp n (d n))).bind fun b =>
        k α (b : ZMod (F.order (d n)))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n (d n) (fun α =>
    (ProbComp.eval (F.sampleExp n (d n))).bind fun b => k α (b : ZMod (F.order (d n))))
  have h2 := advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order (d n)))) _ _
    (fun α => F.advantage_bind_sampleExp_le n (d n) (k α))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n := add_le_add h1 h2
    _ = 2 / 2 ^ n := by ring

/-- **Quantitative KEM IND-CPA bound for Hashed ElGamal**: the KEM distinguishing advantage of
`distinguisher` against `(elGamalKeyGenProb d, hashedElGamalEncapsProb H d)` is bounded by the DDH
advantage of `kemToDDHDistinguisher H distinguisher` plus the KDF advantage of
`kemToKDFDistinguisher distinguisher` plus `4 / 2 ^ n`. -/
theorem advantage_kemGame_hashedElGamalEncapsProb_le (keyLen : ℕ → ℕ)
    (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (distinguisher : Distinguisher) (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (kemRealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n))
      (ProbComp.eval
        (kemIdealGame keyLen (F.elGamalKeyGenProb d)
        (F.hashedElGamalEncapsProb H d) distinguisher n)) ≤
      Game.advantage
        (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
        (F.ddhIdealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n) +
      Game.advantage
        (F.kdfRealGame (fun m => PMF.pure (d m)) H (F.kemToKDFDistinguisher distinguisher) n)
        (F.kdfIdealGame (fun m => PMF.pure (d m)) keyLen
          (F.kemToKDFDistinguisher distinguisher) n) +
      4 / 2 ^ n := by
  have h0 := F.advantage_eval_kemRealGame_ddhRealGame_le H d distinguisher n
  have h3 := F.advantage_kdfIdealGame_eval_kemIdealGame_le keyLen H d distinguisher n
  have htri1 := Game.advantage_triangle
    (ProbComp.eval
      (kemRealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n))
    (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
    (ProbComp.eval
      (kemIdealGame keyLen (F.elGamalKeyGenProb d)
        (F.hashedElGamalEncapsProb H d) distinguisher n))
  have htri2 := Game.advantage_triangle
    (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
    (F.ddhIdealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
    (ProbComp.eval
      (kemIdealGame keyLen (F.elGamalKeyGenProb d)
        (F.hashedElGamalEncapsProb H d) distinguisher n))
  conv at htri2 => rhs; arg 2; arg 1; rw [F.ddhIdealGame_kemToDDHDistinguisher_eq_kdfRealGame]
  have htri3 := Game.advantage_triangle
    (F.kdfRealGame (fun m => PMF.pure (d m)) H (F.kemToKDFDistinguisher distinguisher) n)
    (F.kdfIdealGame (fun m => PMF.pure (d m)) keyLen
      (F.kemToKDFDistinguisher distinguisher) n)
    (ProbComp.eval
      (kemIdealGame keyLen (F.elGamalKeyGenProb d)
        (F.hashedElGamalEncapsProb H d) distinguisher n))
  exact (htri1.trans (add_le_add h0 (htri2.trans (add_le_add le_rfl
    (htri3.trans (add_le_add le_rfl h3)))))).trans_eq (by ring)

/-- **Hashed ElGamal KEM is `Encryption.KEMINDCPA`-secure under DDH and `SecureKDF`**
([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451, and Exercise 11.9, pp. 460–461): for
any group description family `d : ℕ → F.Desc`, if `F.DDH (fun n => PMF.pure (d n))` and
`F.SecureKDF (fun n => PMF.pure (d n)) H keyLen` hold and `H` is computable in polynomial
time, then `(elGamalKeyGenProb d, hashedElGamalEncapsProb H d)` satisfies
`Encryption.KEMINDCPA keyLen`. -/
theorem DDH.kemINDCPA_hashedElGamalEncapsProb {F : PrimeOrderGroupFamily} {keyLen : ℕ → ℕ}
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hKDF : F.SecureKDF (fun n => PMF.pure (d n)) H keyLen)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    KEMINDCPA keyLen (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) := by
  intro distinguisher hD
  have hddh := hDDH _ (F.isPPTOn_kemToDDHDistinguisher hH hD)
  have hkdf := hKDF _ (F.isPPTOn_kemToKDFDistinguisher hD)
  have h4 : Negligible fun n => (4 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 4
  refine negligible_of_le ((hddh.add hkdf).add h4) fun n => ?_
  dsimp only [Pi.add_apply]
  exact F.advantage_kemGame_hashedElGamalEncapsProb_le keyLen H d distinguisher n

/-- **Theorem 11.5 via `Encryption.INDCPAOf`** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
pp. 449–451): combining `DDH.kemINDCPA_hashedElGamalEncapsProb` with `KEMINDCPA.hybrid_indcpa`,
Hashed ElGamal coupled with any uniform strict-PPT one-time semantically secure symmetric cipher
`encryptSym` (`DEMOneTimeKeyINDCPAOf encMsg keyLen encryptSym`) satisfies `Encryption.INDCPAOf`. -/
theorem DDH.indcpaOf_hybrid_hashedElGamal {F : PrimeOrderGroupFamily} {keyLen : ℕ → ℕ}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hKDF : F.SecureKDF (fun n => PMF.pure (d n)) H keyLen)
    (hdem : DEMOneTimeKeyINDCPAOf encMsg keyLen encryptSym)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m)) :
    INDCPAOf encMsg (F.elGamalKeyGenProb d)
      (hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym) :=
  (hDDH.kemINDCPA_hashedElGamalEncapsProb hKDF hH).hybrid_indcpa hdem
    (F.isPPTOn_elGamalKeyGenProb hd) (F.isPPTOn_hashedElGamalEncapsProb hH hd) hencryptSym

/-- **Theorem 11.5 via `Encryption.INDCPAOn`** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
pp. 449–451): combining `DDH.kemINDCPA_hashedElGamalEncapsProb` with `KEMINDCPA.hybrid_indcpaOn`,
for any polynomial-time admissibility predicate `valid` that ignores the public key (such as
the equal-length predicate `fun _ _ m₀ m₁ => m₀.length == m₁.length`), Hashed ElGamal coupled with
any one-time semantically secure symmetric cipher `encryptSym`
(`DEMOneTimeKeyINDCPAOn valid encMsg keyLen encryptSym`) satisfies `Encryption.INDCPAOn`. -/
theorem DDH.indcpaOn_hybrid_hashedElGamal {F : PrimeOrderGroupFamily} {keyLen : ℕ → ℕ}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hKDF : F.SecureKDF (fun n => PMF.pure (d n)) H keyLen)
    (hdem : DEMOneTimeKeyINDCPAOn valid encMsg keyLen encryptSym)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hpk : ∀ n pk m₀ m₁, valid n pk m₀ m₁ = valid n [] m₀ m₁)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hencryptSym : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m)) :
    INDCPAOn valid encMsg (F.elGamalKeyGenProb d)
      (hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym) :=
  (hDDH.kemINDCPA_hashedElGamalEncapsProb hKDF hH).hybrid_indcpaOn hdem hvalid hpk
    (F.isPPTOn_elGamalKeyGenProb hd) (F.isPPTOn_hashedElGamalEncapsProb hH hd) hencryptSym

/-- **Theorem 11.5 via `Encryption.WordINDCPA`** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
pp. 449–451): combining `DDH.indcpaOn_hybrid_hashedElGamal` with Attack Game 11.1's equal-length
rule (`fun _ _ m₀ m₁ => m₀.length == m₁.length`), Hashed ElGamal coupled with any equal-length
one-time semantically secure word cipher `encryptSym`
(`DEMOneTimeKeyWordINDCPA keyLen encryptSym`) satisfies
`Encryption.WordINDCPA`. -/
theorem DDH.wordINDCPA_hybrid_hashedElGamal {F : PrimeOrderGroupFamily} {keyLen : ℕ → ℕ}
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    {encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hKDF : F.SecureKDF (fun n => PMF.pure (d n)) H keyLen)
    (hdem : DEMOneTimeKeyWordINDCPA keyLen encryptSym)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hencryptSym : IsPPTOn (encKeyedInput encBits) encBits
      (fun ⟨n, k, m⟩ => encryptSym n k m)) :
    WordINDCPA (F.elGamalKeyGenProb d)
      (hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym) :=
  let hm := (ComputableInPolyTime.snd encUnary (encPair encBits (encPair encBits encBits))).snd'
  hDDH.indcpaOn_hybrid_hashedElGamal hKDF hdem
    (hm.fst'.length_bits_comp.beq hm.snd'.length_bits_comp)
    (fun _ _ _ _ => rfl) hH hd hencryptSym

/-- Probabilistic polynomial-time multiplicative ElGamal encryption for a group description family
`d : ℕ → F.Desc` and message encoder `encodeMsg : F.Desc → Msg → List Bool`
([BonehShoup2023], Exercise 11.5, p. 459): sample `b ← sampleExp n (d n)`, unpack
`u = dropFrame pk`, and output
`encPair encBits encBits (encodeElGamalEncrypt (d n, u, encodeMsg (d n) m, b))`. -/
noncomputable def elGamalEncryptProb {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (d : ℕ → F.Desc) (n : ℕ) (pk : List Bool) (m : Msg) : ProbComp (List Bool) := do
  let b ← F.sampleExp n (d n)
  let u := dropFrame pk
  return encPair encBits encBits (F.encodeElGamalEncrypt (d n, u, encodeMsg (d n) m, b))

/-- `elGamalEncryptProb` is uniformly strict PPT whenever `encodeMsg` and `d` are computable in
polynomial time. -/
theorem isPPTOn_elGamalEncryptProb {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encodeMsg : F.Desc → Msg → List Bool} {d : ℕ → F.Desc}
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => F.elGamalEncryptProb encodeMsg d n pk m) := by
  unfold elGamalEncryptProb
  let E0 := encPair encUnary (encPair encBits encMsg)
  let hp1 := ComputableInPolyTime.fst E0 encNat
  let hd1 := hd.comp' hp1.fst'
  let hp12 := hp1.snd'
  let hb := ComputableInPolyTime.snd E0 encNat
  have hbody := (F.computableInPolyTime_encodeElGamalEncrypt.comp'
    (hd1.prod ((ComputableInPolyTime.dropFrame.comp' hp12.fst').prod
      ((hencMsg.comp' (hd1.prod hp12.snd')).prod hb)))).encoding_comp.isPPTOn
  exact (F.isPPTOn_sampleExp (ComputableInPolyTime.fst encUnary (encPair encBits encMsg))
    (hd.comp' (ComputableInPolyTime.fst encUnary (encPair encBits encMsg)))).bind_with hbody

/-- Deterministic polynomial-time multiplicative ElGamal decryption on words: given secret key
`sk = encNat a` and ciphertext `ct = encPair encBits encBits (v, e)`, compute
`decodeElGamal (d n, ofBits sk, unframe ct, dropFrame ct)`. -/
def elGamalDecryptDet (d : ℕ → F.Desc) (n : ℕ) (sk ct : List Bool) : List Bool :=
  F.decodeElGamal (d n, ofBits sk, unframe ct, dropFrame ct)

/-- `elGamalDecryptDet` is computable in polynomial time whenever `d` is. -/
theorem computableInPolyTime_elGamalDecryptDet {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => F.elGamalDecryptDet d n sk ct)
      (encKeyedInput encBits) encBits :=
  let hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  let hct := hrest.snd'
  F.computableInPolyTime_decodeElGamal.comp'
    ((hd.comp' (ComputableInPolyTime.fst encUnary (encPair encBits encBits))).prod
      ((ComputableInPolyTime.bitsToNat.comp' hrest.fst').prod
        ((ComputableInPolyTime.unframe.comp' hct).prod
          (ComputableInPolyTime.dropFrame.comp' hct))))

/-- **Multiplicative ElGamal decryption correctness on `ProbComp` outputs**: for any `(pk, sk)` in
the support of `elGamalKeyGenProb d n`, any `m : F.Carrier (d n)`, and any `ct` in the support of
`elGamalEncryptProb (fun d x => x) d n pk (F.encode (d n) m)`,
`elGamalDecryptDet d n sk ct = F.encode (d n) m`. -/
theorem elGamalDecryptDet_elGamalEncryptProb (d : ℕ → F.Desc) (n : ℕ)
    {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (F.elGamalKeyGenProb d n)).support)
    (m : F.Carrier (d n)) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval
      (F.elGamalEncryptProb (fun _ x => x) d n keys.1 (F.encode (d n) m))).support) :
    F.elGamalDecryptDet d n keys.2 ct = F.encode (d n) m := by
  simp only [elGamalKeyGenProb, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hkeys
  rcases hkeys with ⟨a, _, rfl⟩
  simp only [elGamalEncryptProb, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hct
  rcases hct with ⟨b, _, rfl⟩
  have hbits : ofBits (encNat a) = a := Nat.foldr_bit_bits a
  simp only [elGamalDecryptDet, hbits, unframe_encPair_encBits, dropFrame_encPair_encBits_pair,
    dropFrame_encPair_encBits, F.decodeElGamal_encodeElGamalEncrypt]

/-- The native `Encryption.gameOn` experiment for
`(elGamalKeyGenProb d, elGamalEncryptProb encodeMsg d)` is within statistical distance `2 / 2 ^ n`
of the ideal exact-uniform PMF game
`elGamalMsgCPAGameOn valid encodeMsg (fun n => PMF.pure (d n))`. -/
theorem advantage_gameOn_elGamalMsgCPAGameOn_le {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encodeMsg : F.Desc → Msg → List Bool) (d : ℕ → F.Desc)
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (gameOn valid (F.elGamalKeyGenProb d) (F.elGamalEncryptProb encodeMsg d) adversary bit n))
      (F.elGamalMsgCPAGameOn valid encodeMsg (fun m => PMF.pure (d m)) adversary bit n) ≤
      2 / 2 ^ n := by
  let innerB (α : ZMod (F.order (d n))) (choice : (Msg × Msg) × List Bool)
      (β : ZMod (F.order (d n))) : Game :=
    let m := if bit then choice.1.2 else choice.1.1
    let ct := encPair encBits encBits
      (F.encode (d n) (β • F.generator (d n)),
        F.add (d n, F.encode (d n) ((α * β) • F.generator (d n)), encodeMsg (d n) m))
    ProbComp.eval (adversary.guess n choice.2 ct)
  let innerA (useExactB : Bool) (α : ZMod (F.order (d n))) : Game :=
    let pk := encPair F.encDesc encBits (d n, F.encode (d n) (α • F.generator (d n)))
    (ProbComp.eval (adversary.choose n pk)).bind fun choice =>
      if valid n pk choice.1.1 choice.1.2 then
        if useExactB then
          (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind (innerB α choice)
        else
          (ProbComp.eval (F.sampleExp n (d n))).bind fun b =>
            innerB α choice (b : ZMod (F.order (d n)))
      else
        PMF.pure false
  have hgame0 :
      ProbComp.eval
        (gameOn valid (F.elGamalKeyGenProb d) (F.elGamalEncryptProb encodeMsg d) adversary bit n) =
      (ProbComp.eval (F.sampleExp n (d n))).bind fun a =>
        innerA false (a : ZMod (F.order (d n))) := by
    simp only [gameOn, elGamalKeyGenProb, elGamalEncryptProb, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, apply_ite ProbComp.eval,
      encodeElGamalPublicKey_eq_encode, innerA, innerB]
    refine congrArg _ (funext fun a => congrArg _ (funext fun choice => ?_))
    by_cases hv : valid n
        (encPair F.encDesc encBits
          (d n, F.encode (d n) ((a : ZMod (F.order (d n))) • F.generator (d n))))
        choice.1.1 choice.1.2 = true
    · simp only [hv, ↓reduceIte, Bool.false_eq_true, dropFrame_encPair_encBits,
        encodeElGamalEncrypt, F.smul_encode, smul_smul, mul_comm _ (a : ZMod (F.order (d n)))]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
  have hgame1 :
      F.elGamalMsgCPAGameOn valid encodeMsg (fun m => PMF.pure (d m)) adversary bit n =
      (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind (innerA true) := by
    simp only [elGamalMsgCPAGameOn, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
      innerA, innerB, ↓reduceIte]
  rw [hgame0, hgame1]
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order (d n)))).bind (innerA false)) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n (d n) (innerA false)
  have h2 : Game.advantage
      ((PMF.uniformOfFintype (ZMod (F.order (d n)))).bind (innerA false))
      ((PMF.uniformOfFintype (ZMod (F.order (d n)))).bind (innerA true)) ≤ 1 / 2 ^ n := by
    refine advantage_bind_le_nnreal _ _ _ fun α => ?_
    dsimp only [innerA]
    refine advantage_bind_le_nnreal _ _ _ fun choice => ?_
    by_cases hv : valid n (encPair F.encDesc encBits (d n, F.encode (d n) (α • F.generator (d n))))
        choice.1.1 choice.1.2 = true
    · simp only [hv, ↓reduceIte, Bool.false_eq_true]
      exact F.advantage_bind_sampleExp_le n (d n) (innerB α choice)
    · simp only [hv, Bool.false_eq_true, ↓reduceIte, Game.advantage_self, zero_le]
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n := add_le_add h1 h2
    _ = 2 / 2 ^ n := by ring

/-- **Multiplicative ElGamal satisfies `Encryption.INDCPAOn` under DDH** ([BonehShoup2023],
Exercise 11.5(a), p. 459): for any polynomial-time group description family `d : ℕ → F.Desc`,
polynomial-time message encoder `encodeMsg`, and polynomial-time admissibility predicate `valid`
admitting only group elements (`AdmitsGroupElements encodeMsg valid`),
`(elGamalKeyGenProb d, elGamalEncryptProb encodeMsg d)` satisfies `Encryption.INDCPAOn valid encMsg`
whenever `F.DDH (fun n => PMF.pure (d n))` holds. -/
theorem DDH.indcpaOn_elGamalEncryptProb {F : PrimeOrderGroupFamily}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encodeMsg : F.Desc → Msg → List Bool} {d : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hsound : F.AdmitsGroupElements encodeMsg valid)
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits) :
    INDCPAOn valid encMsg (F.elGamalKeyGenProb d) (F.elGamalEncryptProb encodeMsg d) := by
  intro adversary hA
  have hmid := hDDH.negligible_elGamalMsgCPAGameOn hvalid hsound hencMsg hA
  have h2 : Negligible fun n => (2 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 2
  refine negligible_of_le ((h2.add hmid).add h2) fun n => ?_
  dsimp only [Pi.add_apply]
  exact Game.advantage_four_hop_le
    (F.advantage_gameOn_elGamalMsgCPAGameOn_le valid encodeMsg d adversary false n)
    (F.advantage_gameOn_elGamalMsgCPAGameOn_le valid encodeMsg d adversary true n)

/-- **Bit ElGamal satisfies `Encryption.INDCPA` under DDH** ([BonehShoup2023], Exercise 11.5(a),
p. 459): specialization of `DDH.indcpaOn_elGamalEncryptProb` to `encodeBit`. -/
theorem DDH.indcpa_elGamalBitEncryptProb {F : PrimeOrderGroupFamily} {d : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (d n))) :
    INDCPA (F.elGamalKeyGenProb d) (F.elGamalEncryptProb F.encodeBit d) :=
  hDDH.indcpaOn_elGamalEncryptProb
    (ComputableInPolyTime.const true)
    F.admitsGroupElements_encodeBit F.computableInPolyTime_encodeBit

end Cslib.Crypto.PrimeOrderGroupFamily
