/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Computational.Encryption.PolyTime
public import Complexity.Foundations.Data.BitString.List.Operations
public import Complexity.Languages.Probabilistic.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Probability.BitString.List
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# KEM–DEM hybrid public-key encryption

A Key Encapsulation Mechanism (KEM) samples a public/secret key pair `(pk, sk) ← keyGen n` and
encapsulates a symmetric key `(k, ctKem) ← encaps n pk` ([BonehShoup2023], Exercise 11.9). Its
chosen-plaintext / semantic security (`KEMINDCPA`, Exercise 11.9) asks that replacing the
encapsulated key `k` with an independent uniform `n`-bit key `BitString.sampleList n` is
computationally indistinguishable to every uniform strict PPT distinguisher receiving
`(pk, (k, ctKem))`.

A Data Encapsulation Mechanism (DEM) over message space `Msg` encrypts a single challenge message
under a fresh uniform `n`-bit key ([BonehShoup2023], Section 2.2, Attack Game 2.1, p. 16, and
Definition 2.2). As for public-key encryption (`Encryption.gameOn`), the experiment `demGameOn`
takes a challenge-pair admissibility predicate `valid`, and an inadmissible pair makes it output
`false` in both experiments. `demGame` and `DEMOneTimeINDCPAOf` are the always-true case,
`DEMOneTimeINDCPA` specializes to single-bit messages, and `DEMOneTimeWordINDCPA` imposes Attack
Game 2.1's equal-length rule on bit words.

Combining `encaps` with `encryptSym` produces the hybrid public-key encryption scheme
`hybridEncrypt encaps encryptSym` (`hybridDecrypt decaps decryptSym`, Exercise 11.9(a)). By
Boneh and Shoup's Exercise 11.9(b), if the KEM is IND-CPA secure and the DEM is one-time IND-CPA
secure, then `hybridEncrypt encaps encryptSym` is IND-CPA secure: `KEMINDCPA.hybrid_indcpa` for
unrestricted challenge pairs, and `KEMINDCPA.hybrid_indcpaOn` under an admissibility predicate that
ignores the public key, such as the equal-length rule. We formalize both the single hidden-bit KEM
distinguisher bound of Exercise 11.9(b) (`advantage_hybridGame_le_two_mul`) and its
two-distinguisher triangle-inequality variant (`advantage_hybridGame_le`), together with
non-vacuous single-bit and `n`-bit word one-time pad DEM instantiations (`otpEncrypt`,
`otpDecrypt`, `demOneTimeINDCPA_otpEncrypt`, `KEMINDCPA.hybrid_otpEncrypt_indcpa`,
`otpWordEncrypt`, `otpWordDecrypt`, `demOneTimeINDCPA_otpWordEncrypt`,
`demOneTimeWordINDCPA_otpWordEncrypt`, `KEMINDCPA.hybrid_otpWordEncrypt_indcpa`).

Relative to [Boneh and Shoup, Exercise 11.9][BonehShoup2023], this development has the following
representation conventions:
* Plaintext messages are parameterized by `Msg : Type` (with message encoding
  `encMsg : Msg ↪ List Bool` for PPT admissibility), matching `Encryption.gameOn` and
  `Encryption.INDCPAOn` in `Complexity/Crypto/Computational/Encryption/Basic.lean`.
* The DEM adversary receives the empty public key `[]`, and `demGameOn valid` evaluates `valid` at
  it. `KEMINDCPA.hybrid_indcpaOn` therefore asks that `valid` ignore the public key.
* Both the ideal KEM key distribution and the one-time DEM key distribution at security parameter
  `n` are fixed to uniform `n`-bit strings (`BitString.sampleList n`). Because `encaps` returns
  arbitrary bit lists and `KEMINDCPA` requires only negligible distinguishing advantage, finitely
  many or negligibly probable length deviations remain compatible with `KEMINDCPA`, whereas
  non-negligible length deviations are detectable (as in `not_kemINDCPA_leaking`).
* Decapsulation `decaps` and hybrid decryption `hybridDecrypt` are total deterministic functions
  without a separate `reject` symbol; `hybridDecrypt_hybridEncrypt` states exact recovery on
  supported ciphertexts when `decaps` and `decryptSym` are correct on supported outputs.
* In `kemRealGame` and `kemIdealGame`, the KEM distinguisher receives the public key `pk`
  explicitly alongside `(k, ctKem)` (encoded as `(pk, (k, ctKem))`). Although the prose of
  Exercise 11.9 writes that the challenger sends `(k_b, c_kem)`, the public key `pk` is public in a
  public-key KEM experiment and is required by the reduction distinguisher to run
  `adversary.choose n pk`.

## Main definitions

* `Cslib.Crypto.Encryption.kemRealGame`, `Cslib.Crypto.Encryption.kemIdealGame`,
  `Cslib.Crypto.Encryption.KEMINDCPA`: real and ideal KEM IND-CPA experiments and security.
* `Cslib.Crypto.Encryption.demGameOn`, `Cslib.Crypto.Encryption.demGame`,
  `Cslib.Crypto.Encryption.DEMOneTimeINDCPAOn`, `Cslib.Crypto.Encryption.DEMOneTimeINDCPAOf`,
  `Cslib.Crypto.Encryption.DEMOneTimeINDCPA`,
  `Cslib.Crypto.Encryption.DEMOneTimeWordINDCPA`: one-time symmetric encryption experiments and
  security, with and without an admissibility predicate.
* `Cslib.Crypto.Encryption.hybridEncrypt`, `Cslib.Crypto.Encryption.hybridDecrypt`: KEM–DEM
  hybrid encryption and deterministic decryption.
* `Cslib.Crypto.Encryption.hybridIdealGame`: intermediate game replacing the encapsulated key
  with an independent uniform `n`-bit key.
* `Cslib.Crypto.Encryption.hybridToKEMDistinguisher`,
  `Cslib.Crypto.Encryption.hybridToKEMHiddenBitDistinguisher`,
  `Cslib.Crypto.Encryption.hybridToDEMAdversary`: the certified uniform reductions.
* `Cslib.Crypto.Encryption.otpEncrypt`, `Cslib.Crypto.Encryption.otpDecrypt`,
  `Cslib.Crypto.Encryption.otpWordEncrypt`, `Cslib.Crypto.Encryption.otpWordDecrypt`: one-time pad
  single-bit and `n`-bit word DEMs.

## Main results

* `Cslib.Crypto.Encryption.isPPTOn_kemRealGame`,
  `Cslib.Crypto.Encryption.isPPTOn_kemIdealGame`,
  `Cslib.Crypto.Encryption.isPPTOn_demGameOn`,
  `Cslib.Crypto.Encryption.isPPTOn_demGame`,
  `Cslib.Crypto.Encryption.isPPTOn_hybridEncrypt`,
  `Cslib.Crypto.Encryption.computableInPolyTime_hybridDecrypt`: polynomial-time certificates.
* `Cslib.Crypto.Encryption.hybridDecrypt_encPair`,
  `Cslib.Crypto.Encryption.hybridDecrypt_hybridEncrypt`: exact decryption correctness
  (Exercise 11.9(a)).
* `Cslib.Crypto.Encryption.advantage_hybridGame_le_two_mul`,
  `Cslib.Crypto.Encryption.advantage_hybridGame_le`: quantitative Boneh–Shoup Exercise 11.9(b)
  reduction and its two-distinguisher variant.
* `Cslib.Crypto.Encryption.eval_demGame_restrict`,
  `Cslib.Crypto.Encryption.DEMOneTimeINDCPAOf.demOneTimeINDCPAOn`: unrestricted one-time security
  implies one-time security under every polynomial-time admissibility predicate.
* `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_indcpa`,
  `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_indcpaOn`: asymptotic Boneh–Shoup Exercise 11.9(b),
  without and with an admissibility predicate.
* `Cslib.Crypto.Encryption.demOneTimeINDCPA_otpEncrypt`,
  `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_otpEncrypt_indcpa`,
  `Cslib.Crypto.Encryption.demOneTimeINDCPA_otpWordEncrypt`,
  `Cslib.Crypto.Encryption.demOneTimeWordINDCPA_otpWordEncrypt`,
  `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_otpWordEncrypt_indcpa`: unconditional one-time pad DEM
  security and the KEM-to-PKE corollaries.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 2.2 (Attack Game 2.1 and Definition 2.2, p. 16) and
  Exercise 11.9 (pp. 460–461).
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Key Encapsulation Mechanisms -/

/-- The real KEM IND-CPA experiment ([BonehShoup2023], Exercise 11.9, Experiment `0`):
sample `(pk, sk) ← keyGen n` and `(k, ctKem) ← encaps n pk`, and pass the encoded triple
`(pk, (k, ctKem))` to `distinguisher n`. -/
def kemRealGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (distinguisher : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let encapsulated ← encaps n keys.1
  distinguisher n (encPair encBits (encPair encBits encBits) (keys.1, encapsulated))

/-- The ideal KEM IND-CPA experiment ([BonehShoup2023], Exercise 11.9, Experiment `1`):
sample `(pk, sk) ← keyGen n`, `(k, ctKem) ← encaps n pk`, and an independent uniform `n`-bit key
`kIdeal ← BitString.sampleList n`, and pass `(pk, (kIdeal, ctKem))` to `distinguisher n`. -/
noncomputable def kemIdealGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (distinguisher : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let encapsulated ← encaps n keys.1
  let kIdeal ← BitString.sampleList n
  distinguisher n
    (encPair encBits (encPair encBits encBits) (keys.1, (kIdeal, encapsulated.2)))

/-- The real KEM IND-CPA experiment is uniform strict PPT when key generation, encapsulation, and
the distinguisher have native certificates. -/
@[fun_prop]
theorem isPPTOn_kemRealGame {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    {distinguisher : Distinguisher} (hdist : IsPPT encBool distinguisher)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    IsPPTOn input encBool (fun a => kemRealGame keyGen encaps distinguisher (n a)) := by
  have hn' := hn.tidy
  let E1 := encPair input (encPair encBits encBits)
  let E2 := encPair E1 (encPair encBits encBits)
  have h1 : ComputableTidilyInPolyTime
      (fun p : α × List Bool × List Bool => (n p.1, p.2.1))
      E1 (encPair encUnary encBits) := by
    dsimp only [E1]; fun_prop
  have h2 : ComputableTidilyInPolyTime
      (fun p : (α × List Bool × List Bool) × List Bool × List Bool =>
        encPair encBits (encPair encBits encBits) (p.1.2.1, p.2))
      E2 encBits := by
    dsimp only [E2, E1]
    exact (ComputableTidilyInPolyTime.encode (encPair encBits (encPair encBits encBits))).comp
      (by fun_prop)
  have h3 : IsPPTOn E2 encBool
      (fun p => distinguisher (n p.1.1)
        (encPair encBits (encPair encBits encBits) (p.1.2.1, p.2))) := by
    dsimp only [E2, E1]
    exact hdist.preprocess (by fun_prop) h2
  unfold kemRealGame
  exact (hkeyGen.preprocess hn).bind_with
    ((hencaps.preprocess h1.computableInPolyTime).bind_with h3)

/-- The ideal KEM IND-CPA experiment is uniform strict PPT when key generation, encapsulation, and
the distinguisher have native certificates. -/
@[fun_prop]
theorem isPPTOn_kemIdealGame {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    {distinguisher : Distinguisher} (hdist : IsPPT encBool distinguisher)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    IsPPTOn input encBool (fun a => kemIdealGame keyGen encaps distinguisher (n a)) := by
  have hn' := hn.tidy
  let E1 := encPair input (encPair encBits encBits)
  let E2 := encPair E1 (encPair encBits encBits)
  let E3 := encPair E2 encBits
  have h1 : ComputableTidilyInPolyTime
      (fun p : α × List Bool × List Bool => (n p.1, p.2.1))
      E1 (encPair encUnary encBits) := by
    dsimp only [E1]; fun_prop
  have h2 : IsPPTOn E2 encBits
      (fun p : (α × List Bool × List Bool) × List Bool × List Bool =>
        BitString.sampleList (n p.1.1)) := by
    dsimp only [E2, E1]
    exact ComputableInPolyTime.sampleList (by fun_prop)
  have h3 : ComputableTidilyInPolyTime
      (fun p : ((α × List Bool × List Bool) × List Bool × List Bool) × List Bool =>
        encPair encBits (encPair encBits encBits) (p.1.1.2.1, (p.2, p.1.2.2)))
      E3 encBits := by
    dsimp only [E3, E2, E1]
    exact (ComputableTidilyInPolyTime.encode (encPair encBits (encPair encBits encBits))).comp
      (by fun_prop)
  have h4 : IsPPTOn E3 encBool
      (fun p => distinguisher (n p.1.1.1)
        (encPair encBits (encPair encBits encBits) (p.1.1.2.1, (p.2, p.1.2.2)))) := by
    dsimp only [E3, E2, E1]
    exact hdist.preprocess (by fun_prop) h3
  unfold kemIdealGame
  exact (hkeyGen.preprocess hn).bind_with
    ((hencaps.preprocess h1.computableInPolyTime).bind_with (h2.bind_with h4))

/-- IND-CPA / semantic security for a Key Encapsulation Mechanism ([BonehShoup2023],
Exercise 11.9): every uniform strict PPT distinguisher has negligible advantage between
`kemRealGame` and `kemIdealGame`. -/
def KEMINDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)) : Prop :=
  Game.Indistinguishable
    (fun D n => ProbComp.eval (kemRealGame keyGen encaps D n))
    (fun D n => ProbComp.eval (kemIdealGame keyGen encaps D n))
    (IsPPT encBool)

/-! ### One-Time Symmetric Encryption (DEM) -/

/-- The one-time symmetric chosen-plaintext experiment over message space `Msg` with challenge-pair
admissibility predicate `valid` ([BonehShoup2023], Section 2.2, Attack Game 2.1, p. 16): sample a
uniform `n`-bit key `k ← BitString.sampleList n` and invoke `adversary.choose n []`; the adversary
receives the empty public key `[]`, and `valid` is evaluated at it. If the chosen pair is valid,
encrypt the selected message under `encryptSym n k` and pass the saved state and challenge
ciphertext to `adversary.guess n`; otherwise return `false`, in both experiments. -/
noncomputable def demGameOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let choice ← adversary.choose n []
  if valid n [] choice.1.1 choice.1.2 then
    let ciphertext ← encryptSym n k (if bit then choice.1.2 else choice.1.1)
    adversary.guess n choice.2 ciphertext
  else
    return false

/-- The unrestricted one-time symmetric experiment: `demGameOn` with every challenge pair
admissible. -/
noncomputable abbrev demGame {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  demGameOn (fun _ _ _ _ => true) encryptSym adversary bit n

/-- Running the unrestricted `demGame` on `adversary.restrict valid` has the same output
distribution as running `demGameOn valid` on `adversary`. -/
theorem eval_demGame_restrict {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (demGame encryptSym (adversary.restrict valid) bit n) =
      ProbComp.eval (demGameOn valid encryptSym adversary bit n) := by
  simp only [demGame, demGameOn, AdversaryOf.restrict, ↓reduceIte, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, apply_ite ProbComp.eval]
  congr 1; funext k
  congr 1; funext choice
  cases valid n [] choice.1.1 choice.1.2 <;>
    simp [PMF.bind_const]

/-- The one-time symmetric experiment `demGameOn valid` has a strict polynomial clock when `valid`
is computable in polynomial time and symmetric encryption and both adversary stages have native
certificates. -/
@[fun_prop]
theorem isPPTOn_demGameOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => demGameOn valid encryptSym adversary (bit a) (n a)) := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  have hsample : IsPPTOn input encBits (fun a => BitString.sampleList (n a)) :=
    ComputableInPolyTime.sampleList hn
  unfold demGameOn
  ppt

/-- The unrestricted one-time symmetric experiment has a strict polynomial clock when symmetric
encryption and both adversary stages have native certificates. -/
@[fun_prop]
theorem isPPTOn_demGame {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => demGame encryptSym adversary (bit a) (n a)) :=
  isPPTOn_demGameOn (ComputableTidilyInPolyTime.const true).computableInPolyTime hencrypt
    hadversary hn hbit

/-- One-time symmetric IND-CPA / semantic security over message encoding `encMsg` with
challenge-pair admissibility predicate `valid` ([BonehShoup2023], Section 2.2, Attack Game 2.1,
p. 16, and Definition 2.2): every uniform strict PPT `Encryption.AdversaryOf Msg` has negligible
distinguishing advantage between `demGameOn valid encryptSym adversary false` and
`demGameOn valid encryptSym adversary true`. -/
def DEMOneTimeINDCPAOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (demGameOn valid encryptSym adversary false n))
    (fun adversary n => ProbComp.eval (demGameOn valid encryptSym adversary true n))
    (AdversaryOf.IsPPT encMsg)

/-- One-time symmetric IND-CPA with every challenge pair admissible. For `List Bool` messages this
is stronger than the textbook notion, which `DEMOneTimeWordINDCPA` states. -/
abbrev DEMOneTimeINDCPAOf {Msg : Type} (encMsg : Msg ↪ List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  DEMOneTimeINDCPAOn (fun _ _ _ _ => true) encMsg encryptSym

/-- Unrestricted one-time symmetric IND-CPA implies one-time symmetric IND-CPA under every
polynomial-time admissibility predicate. -/
theorem DEMOneTimeINDCPAOf.demOneTimeINDCPAOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : DEMOneTimeINDCPAOf encMsg encryptSym)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool) :
    DEMOneTimeINDCPAOn valid encMsg encryptSym := by
  intro adversary hadversary
  simpa only [eval_demGame_restrict] using
    h (adversary.restrict valid) (hadversary.restrict hvalid)

/-- One-time symmetric IND-CPA / semantic security for single-bit encryption. -/
abbrev DEMOneTimeINDCPA (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)) : Prop :=
  DEMOneTimeINDCPAOf encBool encryptSym

/-- One-time symmetric IND-CPA / semantic security for bit-word encryption under Attack Game 2.1's
equal-length rule ([BonehShoup2023], Section 2.2, p. 16): challenge pairs with
`m₀.length ≠ m₁.length` are inadmissible. -/
abbrev DEMOneTimeWordINDCPA
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)) : Prop :=
  DEMOneTimeINDCPAOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits encryptSym

/-! ### Hybrid Encryption Construction and Correctness -/

/-- KEM–DEM hybrid encryption ([BonehShoup2023], Exercise 11.9): encapsulate a symmetric key
`(k, ctKem) ← encaps n pk`, encrypt the plaintext message under `k` via
`ctDem ← encryptSym n k msg`, and encode `(ctKem, ctDem)` using `encPair encBits encBits`. -/
def hybridEncrypt {Msg : Type} (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (n : ℕ) (pk : List Bool) (msg : Msg) : ProbComp (List Bool) := do
  let encapsulated ← encaps n pk
  let ctDem ← encryptSym n encapsulated.1 msg
  return encPair encBits encBits (encapsulated.2, ctDem)

/-- Deterministic KEM–DEM hybrid decryption ([BonehShoup2023], Exercise 11.9):
decode the hybrid ciphertext `ct` into `ctKem = unframe ct` and `ctDem = dropFrame ct`,
decapsulate `k = decaps n sk ctKem`, and return `decryptSym n k ctDem`. -/
def hybridDecrypt {Msg : Type} (decaps : ℕ → List Bool → List Bool → List Bool)
    (decryptSym : ℕ → List Bool → List Bool → Msg)
    (n : ℕ) (sk ct : List Bool) : Msg :=
  decryptSym n (decaps n sk (unframe ct)) (dropFrame ct)

/-- Hybrid encryption is uniform strict PPT when encapsulation and symmetric encryption are. -/
@[fun_prop]
theorem isPPTOn_hybridEncrypt {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => hybridEncrypt encaps encryptSym p.1 p.2.1 p.2.2) := by
  let E0 := encPair encUnary (encPair encBits encMsg)
  let E1 := encPair E0 (encPair encBits encBits)
  let E2 := encPair E1 encBits
  have h1 : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × Msg => (p.1, p.2.1))
      E0 (encPair encUnary encBits) := by
    dsimp only [E0]; fun_prop
  have h2 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool × Msg) × List Bool × List Bool => (p.1.1, p.2.1, p.1.2.2))
      E1 (encPair encUnary (encPair encBits encMsg)) := by
    dsimp only [E1, E0]; fun_prop
  have h3 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool × Msg) × List Bool × List Bool) × List Bool =>
        encPair encBits encBits (p.1.2.2, p.2))
      E2 encBits := by
    dsimp only [E2, E1, E0]
    exact (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp (by fun_prop)
  unfold hybridEncrypt
  exact (hencaps.preprocess h1.computableInPolyTime).bind_with
    ((hencryptSym.preprocess h2.computableInPolyTime).bind_with h3.isPPTOn)

/-- Hybrid decryption is computable in polynomial time when decapsulation and symmetric decryption
are computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_hybridDecrypt {Msg : Type} {encMsg : Msg ↪ List Bool}
    {decaps : ℕ → List Bool → List Bool → List Bool}
    {decryptSym : ℕ → List Bool → List Bool → Msg}
    (hdecaps : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decaps p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hdecryptSym : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decryptSym p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encMsg) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => hybridDecrypt decaps decryptSym p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encMsg := by
  let E0 := encPair encUnary (encPair encBits encBits)
  have hctKem : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool => unframe p.2.2) E0 encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [E0]; fun_prop)
  have hctDem : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool => dropFrame p.2.2) E0 encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [E0]; fun_prop)
  have hk : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool => decaps p.1 p.2.1 (unframe p.2.2)) E0 encBits :=
    hdecaps.tidy.comp (ComputableTidilyInPolyTime.prod (by dsimp only [E0]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [E0]; fun_prop) hctKem))
  unfold hybridDecrypt
  exact .of_tidy (hdecryptSym.tidy.comp
    (ComputableTidilyInPolyTime.prod (by dsimp only [E0]; fun_prop) (hk.prod hctDem)))

/-- Hybrid decryption on an encoded ciphertext pair `(ctKem, ctDem)` decapsulates `ctKem` and
decrypts `ctDem` under the resulting key. -/
theorem hybridDecrypt_encPair {Msg : Type} (decaps : ℕ → List Bool → List Bool → List Bool)
    (decryptSym : ℕ → List Bool → List Bool → Msg)
    (n : ℕ) (sk ctKem ctDem : List Bool) :
    hybridDecrypt decaps decryptSym n sk (encPair encBits encBits (ctKem, ctDem)) =
      decryptSym n (decaps n sk ctKem) ctDem := by
  simp [hybridDecrypt, encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append]

/-- **Hybrid decryption correctness**: if `decaps n sk` recovers the encapsulated key `k` on every
supported output `(k, ctKem)` of `encaps n pk`, and `decryptSym n k` recovers `msg` on every
supported output of `encryptSym n k msg`, then `hybridDecrypt` recovers `msg` on every supported
ciphertext of `hybridEncrypt`. -/
theorem hybridDecrypt_hybridEncrypt {Msg : Type}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decryptSym : ℕ → List Bool → List Bool → Msg}
    {n : ℕ} {pk sk ct : List Bool} {msg : Msg}
    (hkem : ∀ k ctKem, (k, ctKem) ∈ (ProbComp.eval (encaps n pk)).support →
      decaps n sk ctKem = k)
    (hdem : ∀ k ctDem, (∃ ctKem, (k, ctKem) ∈ (ProbComp.eval (encaps n pk)).support) →
      ctDem ∈ (ProbComp.eval (encryptSym n k msg)).support →
      decryptSym n k ctDem = msg)
    (hct : ct ∈ (ProbComp.eval (hybridEncrypt encaps encryptSym n pk msg)).support) :
    hybridDecrypt decaps decryptSym n sk ct = msg := by
  simp only [hybridEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  rcases hct with ⟨⟨k, ctKem⟩, hkc, ctDem, hdemSupp, rfl⟩
  rw [hybridDecrypt_encPair, hkem k ctKem hkc]
  exact hdem k ctDem ⟨ctKem, hkc⟩ hdemSupp

/-! ### Boneh–Shoup Exercise 11.9(b) Reductions and Asymptotic Security -/

/-- The intermediate hybrid game $G_1$ for the standard hybrid argument of
[BonehShoup2023], Exercise 11.9(b): identical to
`Encryption.game keyGen (hybridEncrypt encaps encryptSym)` except that the symmetric key passed to
`encryptSym` is an independent uniform `n`-bit key `kIdeal ← BitString.sampleList n` rather than
`encapsulated.1`. -/
noncomputable def hybridIdealGame {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← adversary.choose n keys.1
  let encapsulated ← encaps n keys.1
  let kIdeal ← BitString.sampleList n
  let ctDem ← encryptSym n kIdeal (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 (encPair encBits encBits (encapsulated.2, ctDem))

/-- Direct per-bit KEM distinguisher $D_{\mathrm{kem}, b}$ constructed from an
`Encryption.AdversaryOf Msg` and DEM encryption `encryptSym` (for the two-distinguisher variant of
[BonehShoup2023], Exercise 11.9(b)): given an encoded KEM challenge `(pk, (k, ctKem))`, run
`adversary.choose n pk`, encrypt the `bit`-selected message under `k`, and run `adversary.guess` on
`(ctKem, ctDem)`. -/
def hybridToKEMDistinguisher {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) : Distinguisher := fun n challenge => do
  let pk := unframe challenge
  let rest := dropFrame challenge
  let k := unframe rest
  let ctKem := dropFrame rest
  let choice ← adversary.choose n pk
  let ctDem ← encryptSym n k (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 (encPair encBits encBits (ctKem, ctDem))

/-- Single hidden-bit KEM distinguisher $\mathcal{B}_{\mathrm{kem}}$ for
[BonehShoup2023], Exercise 11.9(b): given an encoded KEM challenge `(pk, (k, ctKem))`, run
`adversary.choose n pk`, sample a fair challenge bit `bit ← ProbComp.uniform Bool`, encrypt the
selected message under `k`, run `adversary.guess`, and return `guess ^^ bit`. -/
noncomputable def hybridToKEMHiddenBitDistinguisher {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) : Distinguisher := fun n challenge => do
  let pk := unframe challenge
  let rest := dropFrame challenge
  let k := unframe rest
  let ctKem := dropFrame rest
  let choice ← adversary.choose n pk
  let bit ← ProbComp.uniform Bool
  let ctDem ← encryptSym n k (if bit then choice.1.2 else choice.1.1)
  let guess ← adversary.guess n choice.2 (encPair encBits encBits (ctKem, ctDem))
  return guess ^^ bit

/-- Two-stage DEM adversary $\mathcal{B}_{\mathrm{s}}$ constructed from `keyGen`, `encaps`, and a
hybrid `Encryption.AdversaryOf Msg` for [BonehShoup2023], Exercise 11.9(b): stage 1 samples
`(pk, sk) ← keyGen n` and `(k, ctKem) ← encaps n pk`, runs `adversary.choose n pk`, and saves
`encPair encBits encBits (ctKem, choice.2)`; stage 2 combines `ctKem` with the DEM challenge
ciphertext `ctDem` and runs `adversary.guess`. -/
def hybridToDEMAdversary {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (adversary : AdversaryOf Msg) : AdversaryOf Msg where
  choose n _ := do
    let keys ← keyGen n
    let choice ← adversary.choose n keys.1
    let encapsulated ← encaps n keys.1
    return (choice.1, encPair encBits encBits (encapsulated.2, choice.2))
  guess n state ctDem :=
    adversary.guess n (dropFrame state) (encPair encBits encBits (unframe state, ctDem))

/-- `hybridToKEMDistinguisher` is uniform strict PPT whenever symmetric encryption and the hybrid
adversary are. -/
theorem isPPT_hybridToKEMDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    (hadversary : AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    IsPPT encBool (hybridToKEMDistinguisher encryptSym adversary bit) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 (encPair (encPair encMsg encMsg) encBits)
  let E2 := encPair E1 encBits
  have hpk : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => unframe p.2) E0 encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [E0]; fun_prop)
  have h1 : IsPPTOn E0 (encPair (encPair encMsg encMsg) encBits)
      (fun p => adversary.choose p.1 (unframe p.2)) := by
    dsimp only [E0]
    exact hadversary.choose.preprocess (by fun_prop) hpk
  have hk2 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × (Msg × Msg) × List Bool => unframe (dropFrame p.1.2))
      E1 encBits :=
    ComputableTidilyInPolyTime.unframe.comp
      (ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [E1, E0]; fun_prop))
  have h2 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × (Msg × Msg) × List Bool =>
        (p.1.1, unframe (dropFrame p.1.2), if bit then p.2.1.2 else p.2.1.1))
      E1 (encPair encUnary (encPair encBits encMsg)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [E1, E0]; fun_prop)
      (hk2.prod (by dsimp only [E1, E0]; cases bit <;> fun_prop))
  have hctKem3 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (Msg × Msg) × List Bool) × List Bool =>
        dropFrame (dropFrame p.1.1.2)) E2 encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp
      (ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [E2, E1, E0]; fun_prop))
  have hct3 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (Msg × Msg) × List Bool) × List Bool =>
        encPair encBits encBits (dropFrame (dropFrame p.1.1.2), p.2))
      E2 encBits :=
    (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp
      (hctKem3.prod (by dsimp only [E2]; fun_prop))
  have h3 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (Msg × Msg) × List Bool) × List Bool =>
        (p.1.1.1, p.1.2.2, encPair encBits encBits (dropFrame (dropFrame p.1.1.2), p.2)))
      E2 (encPair encUnary (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [E2, E1, E0]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [E2, E1, E0]; fun_prop) hct3)
  unfold IsPPT hybridToKEMDistinguisher
  exact h1.bind_with
    ((hencryptSym.preprocess h2.computableInPolyTime).bind_with
      (hadversary.guess.preprocess h3.computableInPolyTime))

/-- `hybridToKEMHiddenBitDistinguisher` is uniform strict PPT whenever symmetric encryption and the
hybrid adversary are. -/
theorem isPPT_hybridToKEMHiddenBitDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    (hadversary : AdversaryOf.IsPPT encMsg adversary) :
    IsPPT encBool (hybridToKEMHiddenBitDistinguisher encryptSym adversary) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 (encPair (encPair encMsg encMsg) encBits)
  let E2 := encPair E1 encBool
  let E3 := encPair E2 encBits
  let E4 := encPair E3 encBool
  have hpk : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => unframe p.2) E0 encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [E0]; fun_prop)
  have h1 : IsPPTOn E0 (encPair (encPair encMsg encMsg) encBits)
      (fun p => adversary.choose p.1 (unframe p.2)) := by
    dsimp only [E0]; exact hadversary.choose.preprocess (by fun_prop) hpk
  have hk2 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (Msg × Msg) × List Bool) × Bool =>
        unframe (dropFrame p.1.1.2)) E2 encBits :=
    ComputableTidilyInPolyTime.unframe.comp
      (ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [E2, E1, E0]; fun_prop))
  have h2 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (Msg × Msg) × List Bool) × Bool =>
        (p.1.1.1, unframe (dropFrame p.1.1.2), if p.2 then p.1.2.1.2 else p.1.2.1.1))
      E2 (encPair encUnary (encPair encBits encMsg)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [E2, E1, E0]; fun_prop)
      (hk2.prod (by dsimp only [E2, E1, E0]; fun_prop))
  have hctKem3 : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List Bool) × (Msg × Msg) × List Bool) × Bool) × List Bool =>
        dropFrame (dropFrame p.1.1.1.2)) E3 encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp
      (ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [E3, E2, E1, E0]; fun_prop))
  have hct3 : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List Bool) × (Msg × Msg) × List Bool) × Bool) × List Bool =>
        encPair encBits encBits (dropFrame (dropFrame p.1.1.1.2), p.2))
      E3 encBits :=
    (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp
      (hctKem3.prod (by dsimp only [E3]; fun_prop))
  have h3 : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List Bool) × (Msg × Msg) × List Bool) × Bool) × List Bool =>
        (p.1.1.1.1, p.1.1.2.2, encPair encBits encBits (dropFrame (dropFrame p.1.1.1.2), p.2)))
      E3 (encPair encUnary (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [E3, E2, E1, E0]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [E3, E2, E1, E0]; fun_prop) hct3)
  have h4 : ComputableTidilyInPolyTime
      (fun p : ((((ℕ × List Bool) × (Msg × Msg) × List Bool) × Bool) × List Bool) × Bool =>
        p.2 ^^ p.1.1.2)
      E4 encBool := by
    dsimp only [E4, E3, E2, E1, E0]; fun_prop
  unfold IsPPT hybridToKEMHiddenBitDistinguisher
  exact h1.bind_with
    ((isPPTOn_uniform_bool E1).bind_with
      ((hencryptSym.preprocess h2.computableInPolyTime).bind_with
        ((hadversary.guess.preprocess h3.computableInPolyTime).bind_with h4.isPPTOn)))

/-- `hybridToDEMAdversary` is an admissible uniform strict PPT `Encryption.AdversaryOf Msg` whenever
key generation, encapsulation, and the hybrid adversary are. -/
theorem isPPT_hybridToDEMAdversary {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {adversary : AdversaryOf Msg}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hadversary : AdversaryOf.IsPPT encMsg adversary) :
    AdversaryOf.IsPPT encMsg (hybridToDEMAdversary keyGen encaps adversary) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 (encPair encBits encBits)
  let E2 := encPair E1 (encPair (encPair encMsg encMsg) encBits)
  let E3 := encPair E2 (encPair encBits encBits)
  have h1 : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => p.1) E0 encUnary := by
    dsimp only [E0]; fun_prop
  have h2 : IsPPTOn E1 (encPair (encPair encMsg encMsg) encBits)
      (fun p => adversary.choose p.1.1 p.2.1) := by
    dsimp only [E1, E0]; exact hadversary.choose.preprocess (by fun_prop) (by fun_prop)
  have h3 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool × List Bool) × (Msg × Msg) × List Bool =>
        (p.1.1.1, p.1.2.1))
      E2 (encPair encUnary encBits) := by
    dsimp only [E2, E1, E0]; fun_prop
  have hstate4 : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List Bool) × List Bool × List Bool) × (Msg × Msg) × List Bool) ×
          List Bool × List Bool =>
        encPair encBits encBits (p.2.2, p.1.2.2))
      E3 encBits :=
    (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp
      (by dsimp only [E3, E2, E1, E0]; fun_prop)
  have h4 : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List Bool) × List Bool × List Bool) × (Msg × Msg) × List Bool) ×
          List Bool × List Bool =>
        (p.1.2.1, encPair encBits encBits (p.2.2, p.1.2.2)))
      E3 (encPair (encPair encMsg encMsg) encBits) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [E3, E2, E1, E0]; fun_prop) hstate4
  let EG := encPair encUnary (encPair encBits encBits)
  have hstate5 : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool => dropFrame p.2.1) EG encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [EG]; fun_prop)
  have hctKem5 : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool => unframe p.2.1) EG encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [EG]; fun_prop)
  have hct5 : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool => encPair encBits encBits (unframe p.2.1, p.2.2))
      EG encBits :=
    (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp
      (hctKem5.prod (by dsimp only [EG]; fun_prop))
  have h5 : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        (p.1, dropFrame p.2.1, encPair encBits encBits (unframe p.2.1, p.2.2)))
      EG EG :=
    ComputableTidilyInPolyTime.prod (by dsimp only [EG]; fun_prop) (hstate5.prod hct5)
  refine ⟨?_, hadversary.guess.preprocess h5.computableInPolyTime⟩
  unfold Probability.IsPPT hybridToDEMAdversary
  exact (hkeyGen.preprocess h1.computableInPolyTime).bind_with
    (h2.bind_with
      ((hencaps.preprocess h3.computableInPolyTime).bind_with h4.isPPTOn))

/-- In the real KEM experiment, `hybridToKEMDistinguisher` reproduces the actual hybrid encryption
experiment `Encryption.game keyGen (hybridEncrypt encaps encryptSym)`. -/
@[simp] theorem eval_kemRealGame_hybridToKEMDistinguisher {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (kemRealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary bit) n) =
      ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary bit n) := by
  simp only [kemRealGame, hybridToKEMDistinguisher, game, gameOn, ↓reduceIte, hybridEncrypt,
    encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1; funext keys
  rw [PMF.bind_comm]

/-- In the ideal KEM experiment, `hybridToKEMDistinguisher` reproduces the intermediate game
`hybridIdealGame`. -/
@[simp] theorem eval_kemIdealGame_hybridToKEMDistinguisher {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (kemIdealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary bit) n) =
      ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary bit n) := by
  simp only [kemIdealGame, hybridToKEMDistinguisher, hybridIdealGame, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind]
  congr 1; funext keys
  conv_lhs =>
    rhs; ext encapsulated
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- In the one-time symmetric DEM experiment, `hybridToDEMAdversary` reproduces the intermediate
game `hybridIdealGame`. -/
@[simp] theorem eval_demGame_hybridToDEMAdversary {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) bit n) =
      ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary bit n) := by
  simp only [demGame, demGameOn, ↓reduceIte, hybridToDEMAdversary, hybridIdealGame, encPair_apply,
    encBits_apply, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
    unframe_frame_append, dropFrame_frame_append]
  rw [PMF.bind_comm]
  congr 1; funext keys
  rw [PMF.bind_comm]
  congr 1; funext choice
  rw [PMF.bind_comm]

/-- In the real KEM experiment, `hybridToKEMHiddenBitDistinguisher` averages the two hybrid
chosen-message games, complementing the second. -/
theorem eval_kemRealGame_hybridToKEMHiddenBitDistinguisher {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (n : ℕ) :
    ProbComp.eval
      (kemRealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n) =
      (do
        let bit ← PMF.uniformOfFintype Bool
        (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary bit n)).map
          (fun guess => guess ^^ bit)) := by
  simp only [kemRealGame, hybridToKEMHiddenBitDistinguisher, game, gameOn, ↓reduceIte,
    hybridEncrypt, encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.bind_bind, PMF.pure_bind, PMF.map_bind]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext keys
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  rw [PMF.bind_comm]
  rfl

/-- In the ideal KEM experiment, `hybridToKEMHiddenBitDistinguisher` averages the two intermediate
games `hybridIdealGame`, complementing the second. -/
theorem eval_kemIdealGame_hybridToKEMHiddenBitDistinguisher {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (n : ℕ) :
    ProbComp.eval
      (kemIdealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n) =
      (do
        let bit ← PMF.uniformOfFintype Bool
        (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary bit n)).map
          (fun guess => guess ^^ bit)) := by
  simp only [kemIdealGame, hybridToKEMHiddenBitDistinguisher, hybridIdealGame, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext keys
  conv_lhs =>
    rhs; ext encapsulated
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext encapsulated
  rw [PMF.bind_comm]
  rfl

/-- Success probability of `hybridToKEMHiddenBitDistinguisher` in `kemRealGame` is one half plus
half the signed hybrid chosen-message gap. -/
theorem probability_kemRealGame_hybridToKEMHiddenBitDistinguisher {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (kemRealGame keyGen encaps
        (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n)) : ℝ) =
      (1 + (Game.succProbability (ProbComp.eval
        (game keyGen (hybridEncrypt encaps encryptSym) adversary false n)) : ℝ) -
        Game.succProbability (ProbComp.eval
          (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))) / 2 := by
  rw [eval_kemRealGame_hybridToKEMHiddenBitDistinguisher]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, PMF.monad_bind_eq_bind,
    PMF.bind_apply_toReal, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num [PMF.toReal_false_eq_one_sub]
  ring

/-- Success probability of `hybridToKEMHiddenBitDistinguisher` in `kemIdealGame` is one half plus
half the signed `hybridIdealGame` gap. -/
theorem probability_kemIdealGame_hybridToKEMHiddenBitDistinguisher {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (kemIdealGame keyGen encaps
        (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n)) : ℝ) =
      (1 + (Game.succProbability (ProbComp.eval
        (hybridIdealGame keyGen encaps encryptSym adversary false n)) : ℝ) -
        Game.succProbability (ProbComp.eval
          (hybridIdealGame keyGen encaps encryptSym adversary true n))) / 2 := by
  rw [eval_kemIdealGame_hybridToKEMHiddenBitDistinguisher]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, PMF.monad_bind_eq_bind,
    PMF.bind_apply_toReal, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num [PMF.toReal_false_eq_one_sub]
  ring

/-- **Quantitative KEM–DEM reduction via two per-bit KEM distinguishers** (two-distinguisher
variant of [BonehShoup2023], Exercise 11.9(b)): the hybrid IND-CPA advantage is bounded by the sum
of the KEM advantages of `hybridToKEMDistinguisher encryptSym adversary false` and
`hybridToKEMDistinguisher encryptSym adversary true`, plus the DEM advantage of
`hybridToDEMAdversary keyGen encaps adversary`. -/
theorem advantage_hybridGame_le {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary false n))
      (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n)) ≤
      Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary false) n))
        (ProbComp.eval
          (kemIdealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary false) n)) +
      Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary true) n))
        (ProbComp.eval
          (kemIdealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary true) n)) +
      Game.advantage
        (ProbComp.eval (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) false n))
        (ProbComp.eval
          (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) true n)) := by
  simp only [eval_kemRealGame_hybridToKEMDistinguisher, eval_kemIdealGame_hybridToKEMDistinguisher,
    eval_demGame_hybridToDEMAdversary]
  have h1 := Game.advantage_triangle
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary false n))
    (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary false n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))
  have h2 := Game.advantage_triangle
    (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary false n))
    (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary true n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))
  rw [Game.advantage_comm
    (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary true n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))] at h2
  exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by ac_rfl)

/-- **Quantitative KEM–DEM reduction via a single hidden-bit KEM distinguisher** ([BonehShoup2023],
Exercise 11.9(b)): the hybrid IND-CPA advantage is at most twice the KEM advantage of
`hybridToKEMHiddenBitDistinguisher encryptSym adversary`, plus the DEM advantage of
`hybridToDEMAdversary keyGen encaps adversary`. -/
theorem advantage_hybridGame_le_two_mul {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary false n))
      (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n)) ≤
      2 * Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n))
        (ProbComp.eval
          (kemIdealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n)) +
      Game.advantage
        (ProbComp.eval (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) false n))
        (ProbComp.eval
          (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) true n)) := by
  rw [eval_demGame_hybridToDEMAdversary, eval_demGame_hybridToDEMAdversary]
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Game.coe_advantage,
    probability_kemRealGame_hybridToKEMHiddenBitDistinguisher,
    probability_kemIdealGame_hybridToKEMHiddenBitDistinguisher]
  have h := abs_sub_le
    ((Game.succProbability (ProbComp.eval
      (game keyGen (hybridEncrypt encaps encryptSym) adversary false n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (game keyGen (hybridEncrypt encaps encryptSym) adversary true n)))
    ((Game.succProbability (ProbComp.eval
      (hybridIdealGame keyGen encaps encryptSym adversary false n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (hybridIdealGame keyGen encaps encryptSym adversary true n))) 0
  have hscale (a b c d : ℝ) :
      2 * |(1 + a - b) / 2 - (1 + c - d) / 2| = |(a - b) - (c - d)| := by
    calc
      _ = |2 * ((1 + a - b) / 2 - (1 + c - d) / 2)| := by rw [abs_mul]; norm_num
      _ = _ := by congr 1; ring
  simpa only [hscale, sub_zero] using h

/-- **IND-CPA security of KEM–DEM hybrid encryption** ([BonehShoup2023], Exercise 11.9(b)):
if `(keyGen, encaps)` is an IND-CPA secure KEM and `encryptSym` is a one-time IND-CPA secure DEM
over `encMsg` (with uniform strict PPT honest algorithms), then `hybridEncrypt encaps encryptSym`
is IND-CPA secure over `encMsg`. -/
theorem KEMINDCPA.hybrid_indcpa {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hkem : KEMINDCPA keyGen encaps)
    (hdem : DEMOneTimeINDCPAOf encMsg encryptSym)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2)) :
    INDCPAOf encMsg keyGen (hybridEncrypt encaps encryptSym) := by
  intro adversary hadversary
  have hkemFalse := hkem (hybridToKEMDistinguisher encryptSym adversary false)
    (isPPT_hybridToKEMDistinguisher hencryptSym hadversary false)
  have hkemTrue := hkem (hybridToKEMDistinguisher encryptSym adversary true)
    (isPPT_hybridToKEMDistinguisher hencryptSym hadversary true)
  have hdemAdv := hdem (hybridToDEMAdversary keyGen encaps adversary)
    (isPPT_hybridToDEMAdversary hkeyGen hencaps hadversary)
  exact negligible_of_le ((hkemFalse.add hkemTrue).add hdemAdv)
    (advantage_hybridGame_le keyGen encaps encryptSym adversary)

/-- When `valid` ignores the public key, running the unrestricted `demGame` on the DEM adversary
built from `adversary.restrict valid` has the same output distribution as running `demGameOn valid`
on it: an invalid pair already makes the restricted adversary's guess `false`. -/
theorem eval_demGame_hybridToDEMAdversary_restrict {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (hpk : ∀ n pk m₀ m₁, valid n pk m₀ m₁ = valid n [] m₀ m₁)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (demGame encryptSym (hybridToDEMAdversary keyGen encaps (adversary.restrict valid)) bit n) =
      ProbComp.eval (demGameOn valid encryptSym
        (hybridToDEMAdversary keyGen encaps (adversary.restrict valid)) bit n) := by
  simp only [demGame, demGameOn, hybridToDEMAdversary, AdversaryOf.restrict, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
    apply_ite ProbComp.eval, encPair_apply, encBits_apply, unframe_frame_append,
    dropFrame_frame_append]
  congr 1; funext k
  congr 1; funext keys
  congr 1; funext choice
  rw [hpk n keys.1]
  cases valid n [] choice.1.1 choice.1.2 <;>
    simp [PMF.bind_const]

/-- **IND-CPA security of KEM–DEM hybrid encryption under an admissibility predicate**
([BonehShoup2023], Exercise 11.9(b)), for a polynomial-time predicate `valid` that ignores the
public key, such as the equal-length rule: if `(keyGen, encaps)` is an IND-CPA secure KEM and
`encryptSym` satisfies `DEMOneTimeINDCPAOn valid encMsg`, then `hybridEncrypt encaps encryptSym`
satisfies `INDCPAOn valid encMsg`. -/
theorem KEMINDCPA.hybrid_indcpaOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hkem : KEMINDCPA keyGen encaps)
    (hdem : DEMOneTimeINDCPAOn valid encMsg encryptSym)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hpk : ∀ n pk m₀ m₁, valid n pk m₀ m₁ = valid n [] m₀ m₁)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2)) :
    INDCPAOn valid encMsg keyGen (hybridEncrypt encaps encryptSym) := by
  intro adversary hadversary
  have hA' := hadversary.restrict hvalid
  have hkemFalse := hkem (hybridToKEMDistinguisher encryptSym (adversary.restrict valid) false)
    (isPPT_hybridToKEMDistinguisher hencryptSym hA' false)
  have hkemTrue := hkem (hybridToKEMDistinguisher encryptSym (adversary.restrict valid) true)
    (isPPT_hybridToKEMDistinguisher hencryptSym hA' true)
  have hdemAdv := hdem (hybridToDEMAdversary keyGen encaps (adversary.restrict valid))
    (isPPT_hybridToDEMAdversary hkeyGen hencaps hA')
  refine negligible_of_le ((hkemFalse.add hkemTrue).add hdemAdv) fun n => ?_
  simpa only [eval_game_restrict, eval_demGame_hybridToDEMAdversary_restrict valid hpk,
    Pi.add_apply] using
    advantage_hybridGame_le keyGen encaps encryptSym (adversary.restrict valid) n

/-! ### Non-vacuous One-Time Pad DEMs -/

/-- One-time pad single-bit symmetric encryption: XOR the first key bit `k.headD false` with the
plaintext bit `bit`. -/
def otpEncrypt (_ : ℕ) (k : List Bool) (bit : Bool) : ProbComp (List Bool) :=
  pure [k.headD false ^^ bit]

/-- One-time pad single-bit symmetric decryption: XOR the first key bit `k.headD false` with the
first ciphertext bit `ct.headD false`. -/
def otpDecrypt (_ : ℕ) (k ct : List Bool) : Bool :=
  k.headD false ^^ ct.headD false

/-- One-time pad decryption inverts one-time pad encryption on every supported ciphertext. -/
theorem otpDecrypt_otpEncrypt (n : ℕ) (k : List Bool) (bit : Bool) :
    otpDecrypt n k [k.headD false ^^ bit] = bit := by
  unfold otpDecrypt
  cases k.headD false <;> cases bit <;> rfl

/-- One-time pad encryption is uniform strict PPT. -/
@[fun_prop]
theorem isPPTOn_otpEncrypt :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => otpEncrypt p.1 p.2.1 p.2.2) := by
  unfold otpEncrypt
  apply ComputableInPolyTime.isPPTOn
  fun_prop

/-- One-time pad decryption is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_otpDecrypt :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => otpDecrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  unfold otpDecrypt
  exact ComputableInPolyTime.of_tidy (by fun_prop)

/-- For `1 ≤ n`, a uniform `n`-bit key masks the challenge bit perfectly in `demGame otpEncrypt`,
so the `false` and `true` experiment distributions are identical. -/
theorem eval_demGame_otpEncrypt_false_eq_true {n : ℕ} (hn : 1 ≤ n) (adversary : Adversary) :
    ProbComp.eval (demGame otpEncrypt adversary false n) =
      ProbComp.eval (demGame otpEncrypt adversary true n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [demGame, demGameOn, otpEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, BitString.uniformList_succ, PMF.bind_bind, PMF.bind_map,
    Function.comp_def, PMF.pure_bind, List.headD_cons, Bool.false_eq_true, ↓reduceIte]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext tail
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  ext out
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_bool]
  cases choice.1.1 <;> cases choice.1.2 <;> simp [add_comm]

/-- For `1 ≤ n`, every adversary has exact advantage `0` in `demGame otpEncrypt`. -/
theorem advantage_demGame_otpEncrypt_eq_zero {n : ℕ} (hn : 1 ≤ n) (adversary : Adversary) :
    Game.advantage (ProbComp.eval (demGame otpEncrypt adversary false n))
      (ProbComp.eval (demGame otpEncrypt adversary true n)) = 0 := by
  rw [eval_demGame_otpEncrypt_false_eq_true hn adversary, Game.advantage_self]

/-- **The one-time pad is unconditionally one-time IND-CPA secure**
(`DEMOneTimeINDCPA otpEncrypt`). -/
theorem demOneTimeINDCPA_otpEncrypt : DEMOneTimeINDCPA otpEncrypt := by
  intro adversary _ c
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp [advantage_demGame_otpEncrypt_eq_zero hn adversary]

/-- **KEM-to-PKE corollary**: combining any IND-CPA secure KEM with the one-time pad DEM yields an
IND-CPA secure public-key bit-encryption scheme. -/
theorem KEMINDCPA.hybrid_otpEncrypt_indcpa
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkem : KEMINDCPA keyGen encaps)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2)) :
    INDCPA keyGen (hybridEncrypt encaps otpEncrypt) :=
  hkem.hybrid_indcpa demOneTimeINDCPA_otpEncrypt hkeyGen hencaps isPPTOn_otpEncrypt

/-- One-time pad `n`-bit word symmetric encryption: XOR the `n`-bit key `k` with the plaintext
word `m` at width `n` using `BitString.listXor n [k, m]`. -/
def otpWordEncrypt (n : ℕ) (k m : List Bool) : ProbComp (List Bool) :=
  pure (BitString.listXor n [k, m])

/-- One-time pad `n`-bit word symmetric decryption: XOR the `n`-bit key `k` with the ciphertext
word `ct` at width `n` using `BitString.listXor n [k, ct]`. -/
def otpWordDecrypt (n : ℕ) (k ct : List Bool) : List Bool :=
  BitString.listXor n [k, ct]

/-- One-time pad word decryption inverts one-time pad word encryption on every `n`-bit plaintext
word `m`. -/
theorem otpWordDecrypt_otpWordEncrypt {n : ℕ} (k : List Bool) {m : List Bool}
    (hm : m.length = n) :
    otpWordDecrypt n k (BitString.listXor n [k, m]) = m :=
  BitString.listXor_pair_self_left_of_length k hm

/-- One-time pad word encryption is uniform strict PPT. -/
@[fun_prop]
theorem isPPTOn_otpWordEncrypt :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => otpWordEncrypt p.1 p.2.1 p.2.2) := by
  unfold otpWordEncrypt
  ppt

/-- One-time pad word decryption is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_otpWordDecrypt :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => otpWordDecrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  unfold otpWordDecrypt
  exact ComputableInPolyTime.of_tidy (by fun_prop)

/-- A uniform `n`-bit key masks any challenge word perfectly in `demGame otpWordEncrypt`, so the
`false` and `true` experiment distributions are identical for every `n`. -/
theorem eval_demGame_otpWordEncrypt_false_eq_true (n : ℕ) (adversary : WordAdversary) :
    ProbComp.eval (demGame otpWordEncrypt adversary false n) =
      ProbComp.eval (demGame otpWordEncrypt adversary true n) := by
  have hpad (msg state : List Bool) :
      (do
        let k ← BitString.uniformList n
        ProbComp.eval (adversary.guess n state (BitString.listXor n [k, msg]))) =
      (do
        let ct ← BitString.uniformList n
        ProbComp.eval (adversary.guess n state ct)) := by
    have h := congrArg
      (fun law : PMF (List Bool) => law.bind (ProbComp.eval ∘ adversary.guess n state))
      (BitString.uniformList_map_listXor n msg)
    simpa only [PMF.bind_map, Function.comp_def, PMF.monad_bind_eq_bind] using h
  simp only [demGame, demGameOn, ↓reduceIte, otpWordEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.pure_bind, Bool.false_eq_true, ↓reduceIte]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  exact (hpad choice.1.1 choice.2).trans (hpad choice.1.2 choice.2).symm

/-- Every word adversary has exact advantage `0` in `demGame otpWordEncrypt`. -/
theorem advantage_demGame_otpWordEncrypt_eq_zero (n : ℕ) (adversary : WordAdversary) :
    Game.advantage (ProbComp.eval (demGame otpWordEncrypt adversary false n))
      (ProbComp.eval (demGame otpWordEncrypt adversary true n)) = 0 := by
  rw [eval_demGame_otpWordEncrypt_false_eq_true n adversary, Game.advantage_self]

/-- **The `n`-bit word one-time pad is unconditionally one-time IND-CPA secure**
(`DEMOneTimeINDCPAOf encBits otpWordEncrypt`). -/
theorem demOneTimeINDCPA_otpWordEncrypt : DEMOneTimeINDCPAOf encBits otpWordEncrypt := by
  intro adversary _ c
  refine tendsto_const_nhds.congr' ?_
  filter_upwards with n
  simp [advantage_demGame_otpWordEncrypt_eq_zero n adversary]

/-- **The `n`-bit word one-time pad satisfies equal-length word DEM security**
(`DEMOneTimeWordINDCPA otpWordEncrypt`). -/
theorem demOneTimeWordINDCPA_otpWordEncrypt : DEMOneTimeWordINDCPA otpWordEncrypt :=
  demOneTimeINDCPA_otpWordEncrypt.demOneTimeINDCPAOn (ComputableInPolyTime.of_tidy (by polytime))

/-- **KEM-to-word-PKE corollary**: combining any IND-CPA secure KEM with the `n`-bit word one-time
pad DEM yields a public-key word-encryption scheme satisfying `WordINDCPA`, through the
equal-length instance of `KEMINDCPA.hybrid_indcpaOn`. -/
theorem KEMINDCPA.hybrid_otpWordEncrypt_indcpa
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkem : KEMINDCPA keyGen encaps)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2)) :
    WordINDCPA keyGen (hybridEncrypt encaps otpWordEncrypt) :=
  hkem.hybrid_indcpaOn demOneTimeWordINDCPA_otpWordEncrypt
    (ComputableInPolyTime.of_tidy (by polytime)) (fun _ _ _ _ => rfl) hkeyGen hencaps
    isPPTOn_otpWordEncrypt

end Cslib.Crypto.Encryption
