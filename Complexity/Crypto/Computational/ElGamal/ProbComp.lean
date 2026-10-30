/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.ElGamal
public import Complexity.Crypto.Computational.Encryption.Hybrid
public import Complexity.Languages.Probabilistic.UniformNat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Crypto.Game.Statistical
import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Negligible.Dyadic
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Event
import Complexity.Probability.StatisticalDistance
import Complexity.Tactic.PPT

/-!
# Strict-PPT ElGamal Key Generation, KEM Encapsulation, and `Encryption.INDCPAOn` Bridges

This module defines uniform strict-PPT (`IsPPTOn`) key generation, encapsulation, decapsulation,
and encryption for multiplicative ElGamal and Hashed ElGamal ([BonehShoup2023], Section 11.5,
pp. 445–446, Remark 11.1, Section 11.5.2, Theorem 11.5, pp. 449–451, Exercise 11.5(a), p. 459, and
Exercise 11.9, pp. 460–461) using `ProbComp.sampleModNat`, and connects the PMF-level ElGamal games
in `Complexity/Crypto/Computational/ElGamal.lean` directly to `Encryption.KEMINDCPA`,
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
  public-key encryption scheme.

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
  simp [encPair_apply]

private theorem unframe_encPair_encBits (p : List Bool × List Bool) :
    unframe (encPair encBits encBits p) = p.1 := by
  simp [encPair_apply]

private theorem dropFrame_encPair_encBits_pair (p : List Bool × List Bool) :
    dropFrame (encPair encBits encBits p) = p.2 := by
  simp [encPair_apply]

/-- Probabilistic polynomial-time ElGamal key generation for a group description family
`d : ℕ → F.Desc` ([BonehShoup2023], Section 11.5, p. 445, and Exercise 11.5, p. 459): sample
`a ← sampleExp n (d n)` and output
`(encPair F.encDesc encBits (d n, encode (a • g)), encNat a)`. -/
noncomputable def elGamalKeyGenProb (d : ℕ → F.Desc) (n : ℕ) :
    ProbComp (List Bool × List Bool) :=
  F.sampleExp n (d n) >>= fun a =>
    pure (encPair F.encDesc encBits (d n, F.encodeElGamalPublicKey (d n, a)), encNat a)

/-- `elGamalKeyGenProb` is uniformly strict PPT whenever `d` is computable in polynomial time. -/
theorem isPPTOn_elGamalKeyGenProb {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn encUnary (encPair encBits encBits) (F.elGamalKeyGenProb d) := by
  let E := encPair encUnary encNat
  have hd1 : ComputableInPolyTime (fun p : ℕ × ℕ => d p.1) E F.encDesc :=
    hd.comp (ComputableInPolyTime.fst _ _)
  have ha : ComputableInPolyTime (fun p : ℕ × ℕ => p.2) E encNat :=
    ComputableInPolyTime.snd _ _
  have hu : ComputableInPolyTime
      (fun p : ℕ × ℕ => F.encodeElGamalPublicKey (d p.1, p.2)) E encBits :=
    F.computableInPolyTime_encodeElGamalPublicKey.comp (hd1.prod ha)
  have hpk : ComputableInPolyTime
      (fun p : ℕ × ℕ => encPair F.encDesc encBits (d p.1, F.encodeElGamalPublicKey (d p.1, p.2)))
      E encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp (hd1.prod hu)
  have hsk : ComputableInPolyTime (fun p : ℕ × ℕ => encNat p.2) E encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp ha
  unfold elGamalKeyGenProb
  exact (F.isPPTOn_sampleExp ComputableInPolyTime.id' hd).bind_with
    (hpk.prod hsk).isPPTOn

/-- Probabilistic polynomial-time Hashed ElGamal KEM encapsulation for a group description family
`d : ℕ → F.Desc` ([BonehShoup2023], Section 11.5, p. 445, Remark 11.1, p. 446, and Exercise 11.9,
pp. 460–461): sample `b ← sampleExp n (d n)`, unpack `u = dropFrame pk`, and output
`(H (d n, encode (b • u)), encode (b • g))`. -/
noncomputable def hashedElGamalEncapsProb (H : F.Desc × List Bool → List Bool)
    (d : ℕ → F.Desc) (n : ℕ) (pk : List Bool) : ProbComp (List Bool × List Bool) :=
  F.sampleExp n (d n) >>= fun b =>
    let u := dropFrame pk
    pure (H (d n, F.smul (d n, b, u)),
      F.smul (d n, b, F.encode (d n) (F.generator (d n))))

/-- `hashedElGamalEncapsProb` is uniformly strict PPT whenever `H` and `d` are computable in
polynomial time. -/
theorem isPPTOn_hashedElGamalEncapsProb {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => F.hashedElGamalEncapsProb H d p.1 p.2) := by
  let E := encPair (encPair encUnary encBits) encNat
  have hd1 : ComputableInPolyTime (fun p : (ℕ × List Bool) × ℕ => d p.1.1) E F.encDesc :=
    hd.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
  have hb : ComputableInPolyTime (fun p : (ℕ × List Bool) × ℕ => p.2) E encNat :=
    ComputableInPolyTime.snd _ _
  have hu : ComputableInPolyTime (fun p : (ℕ × List Bool) × ℕ => dropFrame p.1.2) E encBits :=
    ComputableInPolyTime.dropFrame.comp
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
  have hgen : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ℕ => F.encode (d p.1.1) (F.generator (d p.1.1))) E encBits :=
    F.computableInPolyTime_generator.comp hd1
  have hw : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ℕ => F.smul (d p.1.1, p.2, dropFrame p.1.2)) E encBits :=
    F.computableInPolyTime_smul.comp (hd1.prod (hb.prod hu))
  have hk : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ℕ => H (d p.1.1, F.smul (d p.1.1, p.2, dropFrame p.1.2)))
      E encBits :=
    hH.comp (hd1.prod hw)
  have hv : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ℕ =>
        F.smul (d p.1.1, p.2, F.encode (d p.1.1) (F.generator (d p.1.1)))) E encBits :=
    F.computableInPolyTime_smul.comp (hd1.prod (hb.prod hgen))
  unfold hashedElGamalEncapsProb
  exact (F.isPPTOn_sampleExp (ComputableInPolyTime.fst _ _)
    (hd.comp (ComputableInPolyTime.fst _ _))).bind_with (hk.prod hv).isPPTOn

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
      (fun p : ℕ × List Bool × List Bool => F.hashedElGamalDecaps H d p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  let E := encPair encUnary (encPair encBits encBits)
  have hd1 : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => d p.1) E F.encDesc :=
    hd.comp (ComputableInPolyTime.fst _ _)
  have ha : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => ofBits p.2.1) E encNat :=
    ComputableInPolyTime.bitsToNat.comp
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  have hct : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => p.2.2) E encBits :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)
  have hw : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => F.smul (d p.1, ofBits p.2.1, p.2.2)) E encBits :=
    F.computableInPolyTime_smul.comp (hd1.prod (ha.prod hct))
  unfold hashedElGamalDecaps
  exact hH.comp (hd1.prod hw)

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
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  distinguisher n
    (encPair encBits (encPair encBits encBits) (pk, (H (input.1, input.2.2.2), input.2.2.1)))

/-- KDF distinguisher constructed from a `KEMAdversary` (`Distinguisher`) for
`(elGamalKeyGenProb d, hashedElGamalEncapsProb H d)`. -/
def kemToKDFDistinguisher (distinguisher : Distinguisher) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  distinguisher n
    (encPair encBits (encPair encBits encBits) (pk, (input.2.2.2, input.2.2.1)))

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
  let E0 := encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  have hk : ComputableInPolyTime
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        H (input.2.1, input.2.2.2.2)) E0 encBits :=
    hH.comp (by fun_prop)
  exact hD.on.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1,
        encPair encBits (encPair encBits encBits)
          (encPair F.encDesc encBits (input.2.1, input.2.2.1),
            (H (input.2.1, input.2.2.2.2), input.2.2.2.1))))
    (by fun_prop)

/-- `kemToKDFDistinguisher` is uniform strict PPT whenever `distinguisher` is. -/
theorem isPPTOn_kemToKDFDistinguisher {distinguisher : Distinguisher}
    (hD : IsPPT encBool distinguisher) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.kemToKDFDistinguisher distinguisher input.1 input.2) :=
  hD.on.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1,
        encPair encBits (encPair encBits encBits)
          (encPair F.encDesc encBits (input.2.1, input.2.2.1),
            (input.2.2.2.2, input.2.2.2.1))))
    (by fun_prop)

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
    simp only [kemRealGame, elGamalKeyGenProb, hashedElGamalEncapsProb, ProbComp.eval_bind,
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

private theorem advantage_kdfIdealGame_eval_kemIdealGame_le
    (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (distinguisher : Distinguisher) (n : ℕ) :
    Game.advantage
      (F.kdfIdealGame (fun m => PMF.pure (d m)) (fun m => m)
        (F.kemToKDFDistinguisher distinguisher) n)
      (ProbComp.eval
        (kemIdealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n)) ≤
      2 / 2 ^ n := by
  let k (α β : ZMod (F.order (d n))) : Game :=
    (Cslib.BitString.uniformList n).bind fun pad =>
      ProbComp.eval (distinguisher n
        (encPair encBits (encPair encBits encBits)
          (encPair F.encDesc encBits (d n, F.encode (d n) (α • F.generator (d n))),
            (pad, F.encode (d n) (β • F.generator (d n))))))
  have hideal :
      ProbComp.eval
        (kemIdealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n) =
      (ProbComp.eval (F.sampleExp n (d n))).bind fun a =>
        (ProbComp.eval (F.sampleExp n (d n))).bind fun b =>
          k (a : ZMod (F.order (d n))) (b : ZMod (F.order (d n))) := by
    simp only [kemIdealGame, elGamalKeyGenProb, hashedElGamalEncapsProb, ProbComp.eval_bind,
      ProbComp.eval_pure, Cslib.BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind,
      encodeElGamalPublicKey_eq_encode, F.smul_encode, k]
  have hkdf :
      F.kdfIdealGame (fun m => PMF.pure (d m)) (fun m => m)
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
theorem advantage_kemGame_hashedElGamalEncapsProb_le
    (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (distinguisher : Distinguisher) (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (kemRealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n))
      (ProbComp.eval
        (kemIdealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n)) ≤
      Game.advantage
        (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
        (F.ddhIdealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n) +
      Game.advantage
        (F.kdfRealGame (fun m => PMF.pure (d m)) H (F.kemToKDFDistinguisher distinguisher) n)
        (F.kdfIdealGame (fun m => PMF.pure (d m)) (fun m => m)
          (F.kemToKDFDistinguisher distinguisher) n) +
      4 / 2 ^ n := by
  have h0 := F.advantage_eval_kemRealGame_ddhRealGame_le H d distinguisher n
  have h3 := F.advantage_kdfIdealGame_eval_kemIdealGame_le H d distinguisher n
  have htri1 := Game.advantage_triangle
    (ProbComp.eval
      (kemRealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n))
    (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
    (ProbComp.eval
      (kemIdealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n))
  have htri2 := Game.advantage_triangle
    (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
    (F.ddhIdealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
    (ProbComp.eval
      (kemIdealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n))
  have htri3 := Game.advantage_triangle
    (F.kdfRealGame (fun m => PMF.pure (d m)) H (F.kemToKDFDistinguisher distinguisher) n)
    (F.kdfIdealGame (fun m => PMF.pure (d m)) (fun m => m)
      (F.kemToKDFDistinguisher distinguisher) n)
    (ProbComp.eval
      (kemIdealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n))
  have htri2' :
      Game.advantage
        (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
        (ProbComp.eval
          (kemIdealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) distinguisher n)) ≤
      Game.advantage
        (F.ddhRealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n)
        (F.ddhIdealGame (fun m => PMF.pure (d m)) (F.kemToDDHDistinguisher H distinguisher) n) +
      Game.advantage
        (F.kdfRealGame (fun m => PMF.pure (d m)) H (F.kemToKDFDistinguisher distinguisher) n)
        (ProbComp.eval
          (kemIdealGame (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d)
            distinguisher n)) := by
    simpa only [← F.ddhIdealGame_kemToDDHDistinguisher_eq_kdfRealGame] using htri2
  exact (htri1.trans (add_le_add h0 (htri2'.trans (add_le_add le_rfl
    (htri3.trans (add_le_add le_rfl h3)))))).trans_eq (by ring)

/-- **Hashed ElGamal KEM is `Encryption.KEMINDCPA`-secure under DDH and `SecureKDF`**
([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 449–451, and Exercise 11.9, pp. 460–461): for
any group description family `d : ℕ → F.Desc`, if `F.DDH (fun n => PMF.pure (d n))` and
`F.SecureKDF (fun n => PMF.pure (d n)) H (fun n => n)` hold and `H` is computable in polynomial
time, then `(elGamalKeyGenProb d, hashedElGamalEncapsProb H d)` satisfies `Encryption.KEMINDCPA`. -/
theorem DDH.kemINDCPA_hashedElGamalEncapsProb {F : PrimeOrderGroupFamily}
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hKDF : F.SecureKDF (fun n => PMF.pure (d n)) H (fun n => n))
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    KEMINDCPA (F.elGamalKeyGenProb d) (F.hashedElGamalEncapsProb H d) := by
  intro distinguisher hD
  have hddh := hDDH _ (F.isPPTOn_kemToDDHDistinguisher hH hD)
  have hkdf := hKDF _ (F.isPPTOn_kemToKDFDistinguisher hD)
  have h4 : Negligible fun n => (4 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 4
  exact negligible_of_le ((hddh.add hkdf).add h4)
    (F.advantage_kemGame_hashedElGamalEncapsProb_le H d distinguisher)

/-- **Theorem 11.5 via `Encryption.INDCPAOf`** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
pp. 449–451): combining `DDH.kemINDCPA_hashedElGamalEncapsProb` with `KEMINDCPA.hybrid_indcpa`,
Hashed ElGamal coupled with any uniform strict-PPT one-time semantically secure symmetric cipher
`encryptSym` (`DEMOneTimeINDCPAOf encMsg encryptSym`) satisfies `Encryption.INDCPAOf`. -/
theorem DDH.indcpaOf_hybrid_hashedElGamal {F : PrimeOrderGroupFamily}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hKDF : F.SecureKDF (fun n => PMF.pure (d n)) H (fun n => n))
    (hdem : DEMOneTimeINDCPAOf encMsg encryptSym)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2)) :
    INDCPAOf encMsg (F.elGamalKeyGenProb d)
      (hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym) :=
  (hDDH.kemINDCPA_hashedElGamalEncapsProb hKDF hH).hybrid_indcpa hdem
    (F.isPPTOn_elGamalKeyGenProb hd) (F.isPPTOn_hashedElGamalEncapsProb hH hd) hencryptSym

/-- **Theorem 11.5 via `Encryption.INDCPAOn`** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
pp. 449–451): combining `DDH.kemINDCPA_hashedElGamalEncapsProb` with `KEMINDCPA.hybrid_indcpaOn`,
for any polynomial-time admissibility predicate `valid` that ignores the public key (such as
the equal-length predicate `fun _ _ m₀ m₁ => m₀.length == m₁.length`), Hashed ElGamal coupled with
any one-time semantically secure symmetric cipher `encryptSym`
(`DEMOneTimeINDCPAOn valid encMsg encryptSym`) satisfies `Encryption.INDCPAOn`. -/
theorem DDH.indcpaOn_hybrid_hashedElGamal {F : PrimeOrderGroupFamily}
    {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hKDF : F.SecureKDF (fun n => PMF.pure (d n)) H (fun n => n))
    (hdem : DEMOneTimeINDCPAOn valid encMsg encryptSym)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hpk : ∀ n pk m₀ m₁, valid n pk m₀ m₁ = valid n [] m₀ m₁)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2)) :
    INDCPAOn valid encMsg (F.elGamalKeyGenProb d)
      (hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym) :=
  (hDDH.kemINDCPA_hashedElGamalEncapsProb hKDF hH).hybrid_indcpaOn hdem hvalid hpk
    (F.isPPTOn_elGamalKeyGenProb hd) (F.isPPTOn_hashedElGamalEncapsProb hH hd) hencryptSym

/-- **Theorem 11.5 via `Encryption.WordINDCPA`** ([BonehShoup2023], Section 11.5.2, Theorem 11.5,
pp. 449–451): combining `DDH.indcpaOn_hybrid_hashedElGamal` with Attack Game 11.1's equal-length
rule (`fun _ _ m₀ m₁ => m₀.length == m₁.length`), Hashed ElGamal coupled with any equal-length
one-time semantically secure word cipher `encryptSym` (`DEMOneTimeWordINDCPA encryptSym`) satisfies
`Encryption.WordINDCPA`. -/
theorem DDH.wordINDCPA_hybrid_hashedElGamal {F : PrimeOrderGroupFamily}
    {H : F.Desc × List Bool → List Bool} {d : ℕ → F.Desc}
    {encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hKDF : F.SecureKDF (fun n => PMF.pure (d n)) H (fun n => n))
    (hdem : DEMOneTimeWordINDCPA encryptSym)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2)) :
    WordINDCPA (F.elGamalKeyGenProb d)
      (hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym) := by
  let E := encPair encUnary (encPair encBits (encPair encBits encBits))
  have hl0 : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => p.2.2.1.length) E encUnary :=
    (ComputableInPolyTime.encoding_length encBits).comp
      ((ComputableInPolyTime.fst _ _).comp
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)))
  have hl1 : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => p.2.2.2.length) E encUnary :=
    (ComputableInPolyTime.encoding_length encBits).comp
      ((ComputableInPolyTime.snd _ _).comp
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)))
  have hbeq : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 == p.2)
      (encPair encUnary encUnary) encBool := by fun_prop
  exact hDDH.indcpaOn_hybrid_hashedElGamal hKDF hdem
    (hbeq.comp (hl0.prod hl1)) (fun _ _ _ _ => rfl) hH hd hencryptSym

/-- Probabilistic polynomial-time multiplicative ElGamal encryption for a group description family
`d : ℕ → F.Desc` and message encoder `encodeMsg : F.Desc → Msg → List Bool`
([BonehShoup2023], Exercise 11.5, p. 459): sample `b ← sampleExp n (d n)`, unpack
`u = dropFrame pk`, and output
`encPair encBits encBits (encodeElGamalEncrypt (d n, u, encodeMsg (d n) m, b))`. -/
noncomputable def elGamalEncryptProb {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (d : ℕ → F.Desc) (n : ℕ) (pk : List Bool) (m : Msg) : ProbComp (List Bool) :=
  F.sampleExp n (d n) >>= fun b =>
    let u := dropFrame pk
    pure (encPair encBits encBits (F.encodeElGamalEncrypt (d n, u, encodeMsg (d n) m, b)))

/-- `elGamalEncryptProb` is uniformly strict PPT whenever `encodeMsg` and `d` are computable in
polynomial time. -/
theorem isPPTOn_elGamalEncryptProb {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encodeMsg : F.Desc → Msg → List Bool} {d : ℕ → F.Desc}
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => F.elGamalEncryptProb encodeMsg d p.1 p.2.1 p.2.2) := by
  let E := encPair (encPair encUnary (encPair encBits encMsg)) encNat
  have hp1 : ComputableInPolyTime (fun p : (ℕ × List Bool × Msg) × ℕ => p.1)
      E (encPair encUnary (encPair encBits encMsg)) :=
    ComputableInPolyTime.fst _ _
  have hd1 : ComputableInPolyTime (fun p : (ℕ × List Bool × Msg) × ℕ => d p.1.1) E F.encDesc :=
    hd.comp ((ComputableInPolyTime.fst _ _).comp hp1)
  have hp12 : ComputableInPolyTime (fun p : (ℕ × List Bool × Msg) × ℕ => p.1.2)
      E (encPair encBits encMsg) :=
    (ComputableInPolyTime.snd _ _).comp hp1
  have hu : ComputableInPolyTime
      (fun p : (ℕ × List Bool × Msg) × ℕ => dropFrame p.1.2.1) E encBits :=
    ComputableInPolyTime.dropFrame.comp ((ComputableInPolyTime.fst _ _).comp hp12)
  have hm : ComputableInPolyTime (fun p : (ℕ × List Bool × Msg) × ℕ => p.1.2.2) E encMsg :=
    (ComputableInPolyTime.snd _ _).comp hp12
  have hem : ComputableInPolyTime
      (fun p : (ℕ × List Bool × Msg) × ℕ => encodeMsg (d p.1.1) p.1.2.2) E encBits :=
    hencMsg.comp (hd1.prod hm)
  have hb : ComputableInPolyTime (fun p : (ℕ × List Bool × Msg) × ℕ => p.2) E encNat :=
    ComputableInPolyTime.snd _ _
  have hraw : ComputableInPolyTime
      (fun p : (ℕ × List Bool × Msg) × ℕ =>
        F.encodeElGamalEncrypt (d p.1.1, dropFrame p.1.2.1, encodeMsg (d p.1.1) p.1.2.2, p.2))
      E (encPair encBits encBits) :=
    F.computableInPolyTime_encodeElGamalEncrypt.comp (hd1.prod (hu.prod (hem.prod hb)))
  have henc : ComputableInPolyTime
      (fun p : (ℕ × List Bool × Msg) × ℕ =>
        encPair encBits encBits
          (F.encodeElGamalEncrypt (d p.1.1, dropFrame p.1.2.1, encodeMsg (d p.1.1) p.1.2.2, p.2)))
      E encBits :=
    (ComputableInPolyTime.of_eq fun _ => rfl).comp hraw
  unfold elGamalEncryptProb
  exact (F.isPPTOn_sampleExp (ComputableInPolyTime.fst _ _)
    (hd.comp (ComputableInPolyTime.fst _ _))).bind_with henc.isPPTOn

/-- Deterministic polynomial-time multiplicative ElGamal decryption on words: given secret key
`sk = encNat a` and ciphertext `ct = encPair encBits encBits (v, e)`, compute
`decodeElGamal (d n, ofBits sk, unframe ct, dropFrame ct)`. -/
def elGamalDecryptDet (d : ℕ → F.Desc) (n : ℕ) (sk ct : List Bool) : List Bool :=
  F.decodeElGamal (d n, ofBits sk, unframe ct, dropFrame ct)

/-- `elGamalDecryptDet` is computable in polynomial time whenever `d` is. -/
theorem computableInPolyTime_elGamalDecryptDet {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => F.elGamalDecryptDet d p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  let E := encPair encUnary (encPair encBits encBits)
  have hd1 : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => d p.1) E F.encDesc :=
    hd.comp (ComputableInPolyTime.fst _ _)
  have ha : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => ofBits p.2.1) E encNat :=
    ComputableInPolyTime.bitsToNat.comp
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  have hct : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) E encBits :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)
  have hv : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => unframe p.2.2) E encBits :=
    ComputableInPolyTime.unframe.comp hct
  have he : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => dropFrame p.2.2) E encBits :=
    ComputableInPolyTime.dropFrame.comp hct
  unfold elGamalDecryptDet
  exact F.computableInPolyTime_decodeElGamal.comp (hd1.prod (ha.prod (hv.prod he)))

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
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hsound : F.AdmitsGroupElements encodeMsg valid)
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits) :
    INDCPAOn valid encMsg (F.elGamalKeyGenProb d) (F.elGamalEncryptProb encodeMsg d) := by
  intro adversary hA
  have hmid := hDDH.negligible_elGamalMsgCPAGameOn hvalid hsound hencMsg hA
  have h2 : Negligible fun n => (2 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 2
  refine negligible_of_le ((h2.add hmid).add h2) fun n => ?_
  have h0 := F.advantage_gameOn_elGamalMsgCPAGameOn_le valid encodeMsg d adversary false n
  have h1 := F.advantage_gameOn_elGamalMsgCPAGameOn_le valid encodeMsg d adversary true n
  rw [Game.advantage_comm] at h1
  have htri1 := Game.advantage_triangle
    (ProbComp.eval
      (gameOn valid (F.elGamalKeyGenProb d) (F.elGamalEncryptProb encodeMsg d) adversary false n))
    (F.elGamalMsgCPAGameOn valid encodeMsg (fun m => PMF.pure (d m)) adversary false n)
    (ProbComp.eval
      (gameOn valid (F.elGamalKeyGenProb d) (F.elGamalEncryptProb encodeMsg d) adversary true n))
  have htri2 := Game.advantage_triangle
    (F.elGamalMsgCPAGameOn valid encodeMsg (fun m => PMF.pure (d m)) adversary false n)
    (F.elGamalMsgCPAGameOn valid encodeMsg (fun m => PMF.pure (d m)) adversary true n)
    (ProbComp.eval
      (gameOn valid (F.elGamalKeyGenProb d) (F.elGamalEncryptProb encodeMsg d) adversary true n))
  exact (htri1.trans (add_le_add le_rfl htri2)).trans
    (by rw [add_assoc]; exact add_le_add h0 (add_le_add le_rfl h1))

/-- **Bit ElGamal satisfies `Encryption.INDCPA` under DDH** ([BonehShoup2023], Exercise 11.5(a),
p. 459): specialization of `DDH.indcpaOn_elGamalEncryptProb` to `encodeBit`. -/
theorem DDH.indcpa_elGamalBitEncryptProb {F : PrimeOrderGroupFamily} {d : ℕ → F.Desc}
    (hDDH : F.DDH (fun n => PMF.pure (d n))) :
    INDCPA (F.elGamalKeyGenProb d) (F.elGamalEncryptProb F.encodeBit d) :=
  hDDH.indcpaOn_elGamalEncryptProb
    (ComputableInPolyTime.const true)
    F.admitsGroupElements_encodeBit F.computableInPolyTime_encodeBit

end Cslib.Crypto.PrimeOrderGroupFamily
