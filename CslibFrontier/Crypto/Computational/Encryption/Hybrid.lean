/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Computational.Encryption.PolyTime
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PMFSwap

/-!
# KEM–DEM hybrid public-key encryption

A Key Encapsulation Mechanism (KEM) samples a public/secret key pair `(pk, sk) ← keyGen n` and
encapsulates a symmetric key `(k, ctKem) ← encaps n pk` ([BonehShoup2023], Exercise 11.9). Its
chosen-plaintext / semantic security (`KEMINDCPA`, Exercise 11.9) asks that replacing the
encapsulated key `k` with an independent uniform `keyLen n`-bit key is
computationally indistinguishable to every uniform strict PPT distinguisher receiving
`(pk, (k, ctKem))`.

A Data Encapsulation Mechanism (DEM) over message space `Msg` encrypts a single challenge message
under a fresh uniform `keyLen n`-bit key ([BonehShoup2023], Section 2.2, Attack Game 2.1, p. 16,
and Definition 2.2). As for public-key encryption (`Encryption.gameOn`), `demKeyGameOn` takes a
challenge-pair admissibility predicate `valid`, and an inadmissible pair makes it output `false`
in both experiments. `demKeyGame` and `DEMOneTimeKeyINDCPAOf` are the always-true case. The
normalized interfaces `demGameOn`, `demGame`, and `DEMOneTimeINDCPAOf` specialize to `keyLen n = n`;
`DEMOneTimeINDCPA` specializes further to single-bit messages, and `DEMOneTimeWordINDCPA` imposes
Attack Game 2.1's equal-length rule on bit words.

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
  `Encryption.INDCPAOn` in `CslibFrontier/Crypto/Computational/Encryption/Basic.lean`.
* The DEM adversary receives the empty public key `[]`; `demKeyGameOn valid` evaluates `valid`
  at it. `KEMINDCPA.hybrid_indcpaOn` therefore asks that `valid` ignore the public key.
* Both the ideal KEM key distribution and the one-time DEM key distribution at security parameter
  `n` are uniform `keyLen n`-bit strings (`BitString.sampleList (keyLen n)`). The schedule is
  a function of the security parameter; `fun n => n` recovers the normalized convention.
  A native unary polynomial-time certificate for `keyLen` certifies ideal sampling. The security
  reductions themselves do not sample ideal keys and need no such premise. Because `encaps` returns
  arbitrary bit lists and `KEMINDCPA` requires only negligible distinguishing advantage, finitely
  many or negligibly probable length deviations remain compatible with `KEMINDCPA`, whereas
  non-negligible length deviations are detectable (as in `not_kemINDCPA_leaking`).
* Decapsulation and symmetric decryption return `Option`, with `none` denoting rejection.
  `hybridDecrypt` first checks canonical ciphertext-pair framing and propagates either failure;
  accepted empty keys/messages remain distinct from rejection. `hybridDecrypt_hybridEncrypt`
  states exact recovery as `some msg` on supported ciphertexts under component correctness.
* In `kemRealGame` and `kemIdealGame`, the KEM distinguisher receives the public key `pk`
  explicitly alongside `(k, ctKem)` (encoded as `(pk, (k, ctKem))`). Although the prose of
  Exercise 11.9 writes that the challenger sends `(k_b, c_kem)`, the public key `pk` is public in a
  public-key KEM experiment and is required by the reduction distinguisher to run
  `adversary.choose n pk`.

## Main definitions

* `Cslib.Crypto.Encryption.kemRealGameWith`, `Cslib.Crypto.Encryption.kemIdealGameWith`:
  shared challenger continuations for the CPA and adaptive decapsulation experiments.
* `Cslib.Crypto.Encryption.kemRealGame`, `Cslib.Crypto.Encryption.kemIdealGame`,
  `Cslib.Crypto.Encryption.KEMINDCPA`: real and ideal KEM IND-CPA experiments and security.
* `Cslib.Crypto.Encryption.demGameOn`, `Cslib.Crypto.Encryption.demGame`,
  `Cslib.Crypto.Encryption.demKeyGameOn`, `Cslib.Crypto.Encryption.demKeyGame`,
  `Cslib.Crypto.Encryption.DEMOneTimeINDCPAOn`, `Cslib.Crypto.Encryption.DEMOneTimeINDCPAOf`,
  `Cslib.Crypto.Encryption.DEMOneTimeINDCPA`,
  `Cslib.Crypto.Encryption.DEMOneTimeWordINDCPA`,
  `Cslib.Crypto.Encryption.DEMOneTimeKeyINDCPAOn`, `Cslib.Crypto.Encryption.DEMOneTimeKeyINDCPAOf`,
  `Cslib.Crypto.Encryption.DEMOneTimeKeyINDCPA`,
  `Cslib.Crypto.Encryption.DEMOneTimeKeyWordINDCPA`: one-time symmetric encryption experiments and
  security at normalized (`n`-bit) and arbitrary (`keyLen n`-bit) key lengths, with and without an
  admissibility predicate.
* `Cslib.Crypto.Encryption.hybridEncrypt`, `Cslib.Crypto.Encryption.hybridDecrypt`: KEM–DEM
  hybrid encryption and deterministic decryption.
* `Cslib.Crypto.Encryption.hybridIdealGame`: intermediate game replacing the encapsulated key
  with an independent uniform `keyLen n`-bit key.
* `Cslib.Crypto.Encryption.hybridToKEMDistinguisher`,
  `Cslib.Crypto.Encryption.hybridToKEMHiddenBitDistinguisher`,
  `Cslib.Crypto.Encryption.hybridToDEMAdversary`: the certified uniform reductions.
* `Cslib.Crypto.Encryption.otpEncrypt`, `Cslib.Crypto.Encryption.otpDecrypt`,
  `Cslib.Crypto.Encryption.otpWordEncrypt`, `Cslib.Crypto.Encryption.otpWordDecrypt`,
  `Cslib.Crypto.Encryption.otpKeyWordEncrypt`, `Cslib.Crypto.Encryption.otpKeyWordDecrypt`:
  one-time pad single-bit, `n`-bit word, and `keyLen n`-bit word DEMs.

## Main results

* `Cslib.Crypto.Encryption.isPPTOn_kemRealGame`,
  `Cslib.Crypto.Encryption.isPPTOn_kemIdealGame`,
  `Cslib.Crypto.Encryption.isPPTOn_demGameOn`,
  `Cslib.Crypto.Encryption.isPPTOn_demGame`,
  `Cslib.Crypto.Encryption.isPPTOn_demKeyGameOn`,
  `Cslib.Crypto.Encryption.isPPTOn_demKeyGame`,
  `Cslib.Crypto.Encryption.isPPTOn_hybridEncrypt`,
  `Cslib.Crypto.Encryption.computableInPolyTime_hybridDecrypt`: polynomial-time certificates.
* `Cslib.Crypto.Encryption.hybridDecrypt_of_not_canonical`: malformed encodings are rejected.
* `Cslib.Crypto.Encryption.hybridDecrypt_encPair`,
  `Cslib.Crypto.Encryption.hybridDecrypt_hybridEncrypt`: exact decryption correctness
  (Exercise 11.9(a)).
* `Cslib.Crypto.Encryption.advantage_hybridGame_le_two_mul`,
  `Cslib.Crypto.Encryption.advantage_hybridGame_le`: quantitative Boneh–Shoup Exercise 11.9(b)
  reduction and its two-distinguisher variant.
* `Cslib.Crypto.Encryption.eval_demGame_restrict`,
  `Cslib.Crypto.Encryption.eval_demKeyGame_restrict`,
  `Cslib.Crypto.Encryption.DEMOneTimeINDCPAOf.demOneTimeINDCPAOn`,
  `Cslib.Crypto.Encryption.DEMOneTimeKeyINDCPAOf.demOneTimeKeyINDCPAOn`: unrestricted one-time
  security implies one-time security under every polynomial-time admissibility predicate.
* `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_indcpa`,
  `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_indcpaOn`: asymptotic Boneh–Shoup Exercise 11.9(b),
  without and with an admissibility predicate.
* `Cslib.Crypto.Encryption.demOneTimeINDCPA_otpEncrypt`,
  `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_otpEncrypt_indcpa`,
  `Cslib.Crypto.Encryption.demOneTimeINDCPA_otpWordEncrypt`,
  `Cslib.Crypto.Encryption.demOneTimeWordINDCPA_otpWordEncrypt`,
  `Cslib.Crypto.Encryption.demOneTimeKeyINDCPA_otpKeyWordEncrypt`,
  `Cslib.Crypto.Encryption.demOneTimeKeyWordINDCPA_otpKeyWordEncrypt`,
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

/-- The shared real KEM experiment: generate keys and encapsulate, then run the challenger
continuation with `(sk, pk, key, ciphertext)`. The secret key is internal challenger data, not an
adversary input. CPA and CCA experiments specialize the same sampling computation. -/
def kemRealGameWith (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (next : ℕ → List Bool → List Bool → List Bool → List Bool → ProbComp Bool)
    (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let encapsulated ← encaps n keys.1
  next n keys.2 keys.1 encapsulated.1 encapsulated.2

/-- The shared ideal KEM experiment replaces only the key shown to the continuation with an
independent uniform `keyLen n`-bit word. Key generation, encapsulation, and their order are those
of `kemRealGameWith`; the secret key and ciphertext remain unchanged. -/
noncomputable def kemIdealGameWith (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (next : ℕ → List Bool → List Bool → List Bool → List Bool → ProbComp Bool)
    (n : ℕ) : ProbComp Bool :=
  kemRealGameWith keyGen encaps (fun n sk pk _ ct => do
    let kIdeal ← BitString.sampleList (keyLen n)
    next n sk pk kIdeal ct) n

/-- The real KEM IND-CPA experiment ([BonehShoup2023], Exercise 11.9, Experiment `0`):
sample `(pk, sk) ← keyGen n` and `(k, ctKem) ← encaps n pk`, and pass the encoded triple
`(pk, (k, ctKem))` to `distinguisher n`. -/
def kemRealGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (distinguisher : Distinguisher) (n : ℕ) : ProbComp Bool :=
  kemRealGameWith keyGen encaps (fun n _ pk k ct =>
    distinguisher n (encPair encBits (encPair encBits encBits) (pk, (k, ct)))) n

/-- The ideal KEM IND-CPA experiment ([BonehShoup2023], Exercise 11.9, Experiment `1`):
sample `(pk, sk) ← keyGen n`, `(k, ctKem) ← encaps n pk`, and an independent uniform
`keyLen n`-bit key `kIdeal ← BitString.sampleList (keyLen n)`,
and pass `(pk, (kIdeal, ctKem))` to `distinguisher n`. -/
noncomputable def kemIdealGame (keyLen : ℕ → ℕ) (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (distinguisher : Distinguisher) (n : ℕ) : ProbComp Bool :=
  kemIdealGameWith keyLen keyGen encaps (fun n _ pk k ct =>
    distinguisher n (encPair encBits (encPair encBits encBits) (pk, (k, ct)))) n

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
  let E1 := encPair input (encPair encBits encBits)
  let hp1 := ComputableInPolyTime.fst input (encPair encBits encBits)
  let hp2 := ComputableInPolyTime.snd input (encPair encBits encBits)
  let hq1 := ComputableInPolyTime.fst E1 (encPair encBits encBits)
  let hq2 := ComputableInPolyTime.snd E1 (encPair encBits encBits)
  exact (hkeyGen.preprocess hn).bind_with
    ((hencaps.preprocess ((hn.comp' hp1).prod hp2.fst')).bind_with
      (hdist.on.preprocess
        ((hn.comp' (hp1.comp' hq1)).prod
          (((hp2.fst'.comp' hq1).prod hq2).encoding_comp))))

/-- The ideal KEM IND-CPA experiment is uniform strict PPT when key generation, encapsulation, and
the distinguisher have native certificates and `keyLen` is computable in polynomial time
in unary. -/
@[fun_prop]
theorem isPPTOn_kemIdealGame {keyLen : ℕ → ℕ}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    {distinguisher : Distinguisher} (hdist : IsPPT encBool distinguisher)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    IsPPTOn input encBool (fun a => kemIdealGame keyLen keyGen encaps distinguisher (n a)) := by
  let E1 := encPair input (encPair encBits encBits)
  let E2 := encPair E1 (encPair encBits encBits)
  let hp1 := ComputableInPolyTime.fst input (encPair encBits encBits)
  let hp2 := ComputableInPolyTime.snd input (encPair encBits encBits)
  let hq1 := ComputableInPolyTime.fst E1 (encPair encBits encBits)
  let hq2 := ComputableInPolyTime.snd E1 (encPair encBits encBits)
  let hr1 := ComputableInPolyTime.fst E2 encBits
  let hr2 := ComputableInPolyTime.snd E2 encBits
  have hn2 := hn.comp' (hp1.comp' hq1)
  exact (hkeyGen.preprocess hn).bind_with
    ((hencaps.preprocess ((hn.comp' hp1).prod hp2.fst')).bind_with
      ((hkeyLen.comp' hn2).sampleList.bind_with
        (hdist.on.preprocess
          ((hn2.comp' hr1).prod
            (((hp2.fst'.comp' (hq1.comp' hr1)).prod
              (hr2.prod (hq2.snd'.comp' hr1))).encoding_comp)))))

/-- IND-CPA / semantic security for a Key Encapsulation Mechanism ([BonehShoup2023],
Exercise 11.9): every uniform strict PPT distinguisher has negligible advantage between
`kemRealGame` and `kemIdealGame keyLen`. The key space is the uniform bit-word space of length
`keyLen n`; security does not bundle correctness or efficient honest sampling. -/
def KEMINDCPA (keyLen : ℕ → ℕ) (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)) : Prop :=
  Game.Indistinguishable
    (fun D n => ProbComp.eval (kemRealGame keyGen encaps D n))
    (fun D n => ProbComp.eval (kemIdealGame keyLen keyGen encaps D n))
    (IsPPT encBool)

/-! ### One-Time Symmetric Encryption (DEM) -/

/-- The one-time symmetric chosen-plaintext experiment over message space `Msg` with challenge-pair
admissibility predicate `valid` and key-length function `keyLen : ℕ → ℕ` ([BonehShoup2023],
Section 2.2, Attack Game 2.1, p. 16): sample a uniform `keyLen n`-bit key
`k ← BitString.sampleList (keyLen n)` and invoke `adversary.choose n []`; the adversary receives
the empty public key `[]`, and `valid` is evaluated at it. If the chosen pair is valid, encrypt the
selected message under `encryptSym n k` and pass the saved state and challenge ciphertext to
`adversary.guess n`; otherwise return `false`, in both experiments. -/
noncomputable def demKeyGameOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList (keyLen n)
  let choice ← adversary.choose n []
  if valid n [] (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let ciphertext ← encryptSym n k
      (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
    adversary.guess n choice.2 ciphertext
  else
    return false

/-- The unrestricted one-time symmetric experiment at key-length function `keyLen`: `demKeyGameOn`
with every challenge pair admissible. -/
noncomputable abbrev demKeyGame {Msg : Type} (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  demKeyGameOn (fun _ _ _ _ => true) keyLen encryptSym adversary bit n

/-- The normalized (`n`-bit key) one-time symmetric chosen-plaintext experiment over message space
`Msg` with challenge-pair admissibility predicate `valid` ([BonehShoup2023], Section 2.2, Attack
Game 2.1, p. 16): `demKeyGameOn` specialized to `keyLen n = n`. -/
noncomputable abbrev demGameOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  demKeyGameOn valid (fun m => m) encryptSym adversary bit n

/-- The unrestricted `n`-bit key one-time symmetric experiment: `demGameOn` with every challenge
pair admissible. -/
noncomputable abbrev demGame {Msg : Type}
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  demGameOn (fun _ _ _ _ => true) encryptSym adversary bit n

/-- At the normalized key length `keyLen n = n`, `demKeyGameOn` is definitionally `demGameOn`. -/
theorem demKeyGameOn_id {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    demKeyGameOn valid (fun m => m) encryptSym adversary bit n =
      demGameOn valid encryptSym adversary bit n :=
  rfl

/-- Whenever `keyLen n = n`, `demKeyGameOn` at security parameter `n` coincides with `demGameOn`. -/
theorem demKeyGameOn_eq_demGameOn_of_eq {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) {n : ℕ} (h : keyLen n = n) :
    demKeyGameOn valid keyLen encryptSym adversary bit n =
      demGameOn valid encryptSym adversary bit n := by
  simp only [demKeyGameOn, demGameOn, h]

/-- Running the unrestricted `demKeyGame` on `adversary.restrict valid` has the same output
distribution as running `demKeyGameOn valid` on `adversary`. -/
theorem eval_demKeyGame_restrict {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyLen : ℕ → ℕ) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (demKeyGame keyLen encryptSym (adversary.restrict valid) bit n) =
      ProbComp.eval (demKeyGameOn valid keyLen encryptSym adversary bit n) := by
  simp only [demKeyGame, demKeyGameOn, AdversaryOf.restrict, ↓reduceIte, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, apply_ite ProbComp.eval]
  congr 1 with k : 1
  congr 1 with choice : 1
  cases valid n [] choice.1.1 choice.1.2 <;>
    simp [PMF.bind_const]

/-- Running the unrestricted `demGame` on `adversary.restrict valid` has the same output
distribution as running `demGameOn valid` on `adversary`. -/
theorem eval_demGame_restrict {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (demGame encryptSym (adversary.restrict valid) bit n) =
      ProbComp.eval (demGameOn valid encryptSym adversary bit n) :=
  eval_demKeyGame_restrict valid (fun m => m) encryptSym adversary bit n

/-- The one-time symmetric experiment `demKeyGameOn valid keyLen` has a strict polynomial clock
when `valid` and `keyLen` are computable in polynomial time and symmetric encryption and both
adversary stages have native certificates. -/
@[fun_prop]
theorem isPPTOn_demKeyGameOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {keyLen : ℕ → ℕ}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool
      (fun a => demKeyGameOn valid keyLen encryptSym adversary (bit a) (n a)) := by
  let E1 := encPair input encBits
  let EChoice := encPair (encPair encMsg encMsg) encBits
  let E2 := encPair E1 EChoice
  let hp1 := ComputableInPolyTime.fst input encBits
  let hp2 := ComputableInPolyTime.snd input encBits
  let hq1 := ComputableInPolyTime.fst E1 EChoice
  let hq2 := ComputableInPolyTime.snd E1 EChoice
  let hr1 := ComputableInPolyTime.fst E2 encBits
  let hr2 := ComputableInPolyTime.snd E2 encBits
  have ha2 := hp1.comp' hq1
  have hn2 := hn.comp' ha2
  exact (hkeyLen.comp' hn).sampleList.bind_with
    ((hadversary.choose.on.preprocess ((hn.comp' hp1).prod (.const []))).bind_with
      (IsPPTOn.cond'
        (hvalid.comp' (hn2.prod ((ComputableInPolyTime.const []).prod hq2.fst')))
        ((hencrypt.preprocess
          (hn2.prod
            ((hp2.comp' hq1).prod
              ((hbit.comp' ha2).ite hq2.fst'.snd' hq2.fst'.fst')))).bind_with
          (hadversary.guess.preprocess
            ((hn2.comp' hr1).prod ((hq2.snd'.comp' hr1).prod hr2))))
        (ComputableInPolyTime.const false).isPPTOn))

/-- The unrestricted one-time symmetric experiment `demKeyGame keyLen` has a strict polynomial
clock when `keyLen` is computable in polynomial time and symmetric encryption and both adversary
stages have native certificates. -/
@[fun_prop]
theorem isPPTOn_demKeyGame {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyLen : ℕ → ℕ} (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => demKeyGame keyLen encryptSym adversary (bit a) (n a)) :=
  isPPTOn_demKeyGameOn (ComputableInPolyTime.const true) hkeyLen hencrypt hadversary hn hbit

/-- The normalized (`n`-bit key) one-time symmetric experiment `demGameOn valid` has a strict
polynomial clock when `valid` is computable in polynomial time and symmetric encryption and both
adversary stages have native certificates. -/
@[fun_prop]
theorem isPPTOn_demGameOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun ⟨n, k, msg⟩ => encryptSym n k msg))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => demGameOn valid encryptSym adversary (bit a) (n a)) :=
  isPPTOn_demKeyGameOn hvalid ComputableInPolyTime.id' hencrypt hadversary hn hbit

/-- The unrestricted `n`-bit key one-time symmetric experiment has a strict polynomial clock when
symmetric encryption and both adversary stages have native certificates. -/
@[fun_prop]
theorem isPPTOn_demGame {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun ⟨n, k, msg⟩ => encryptSym n k msg))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => demGame encryptSym adversary (bit a) (n a)) :=
  isPPTOn_demKeyGame ComputableInPolyTime.id' hencrypt hadversary hn hbit

/-- One-time symmetric IND-CPA / semantic security over message encoding `encMsg` with
challenge-pair admissibility predicate `valid` and key-length function `keyLen : ℕ → ℕ`
([BonehShoup2023], Section 2.2, Attack Game 2.1, p. 16, and Definition 2.2): every uniform strict
PPT `Encryption.AdversaryOf Msg` has negligible distinguishing advantage between
`demKeyGameOn valid keyLen encryptSym adversary false` and
`demKeyGameOn valid keyLen encryptSym adversary true`. -/
def DEMOneTimeKeyINDCPAOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (demKeyGameOn valid keyLen encryptSym adversary false n))
    (fun adversary n => ProbComp.eval (demKeyGameOn valid keyLen encryptSym adversary true n))
    (AdversaryOf.IsPPT encMsg)

/-- One-time symmetric IND-CPA at key-length function `keyLen` with every challenge pair
admissible. -/
abbrev DEMOneTimeKeyINDCPAOf {Msg : Type} (encMsg : Msg ↪ List Bool) (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  DEMOneTimeKeyINDCPAOn (fun _ _ _ _ => true) encMsg keyLen encryptSym

/-- Unrestricted one-time symmetric IND-CPA at key length `keyLen` implies one-time symmetric
IND-CPA under every polynomial-time admissibility predicate. -/
theorem DEMOneTimeKeyINDCPAOf.demOneTimeKeyINDCPAOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : DEMOneTimeKeyINDCPAOf encMsg keyLen encryptSym)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool) :
    DEMOneTimeKeyINDCPAOn valid encMsg keyLen encryptSym := by
  intro adversary hadversary
  simpa only [eval_demKeyGame_restrict] using
    h (adversary.restrict valid) (hadversary.restrict hvalid)

/-- One-time symmetric IND-CPA / semantic security for single-bit encryption at key length
`keyLen`. -/
abbrev DEMOneTimeKeyINDCPA (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)) : Prop :=
  DEMOneTimeKeyINDCPAOf encBool keyLen encryptSym

/-- One-time symmetric IND-CPA / semantic security for bit-word encryption at key length `keyLen`
under Attack Game 2.1's equal-length rule ([BonehShoup2023], Section 2.2, p. 16). -/
abbrev DEMOneTimeKeyWordINDCPA (keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)) : Prop :=
  DEMOneTimeKeyINDCPAOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits keyLen encryptSym

/-- Normalized (`n`-bit key) one-time symmetric IND-CPA / semantic security over message encoding
`encMsg` with challenge-pair admissibility predicate `valid` ([BonehShoup2023], Section 2.2, Attack
Game 2.1, p. 16, and Definition 2.2): `DEMOneTimeKeyINDCPAOn` specialized to `keyLen n = n`. -/
abbrev DEMOneTimeINDCPAOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  DEMOneTimeKeyINDCPAOn valid encMsg (fun n => n) encryptSym

/-- Normalized (`n`-bit key) one-time symmetric IND-CPA with every challenge pair admissible. For
`List Bool` messages this is stronger than the textbook notion, which `DEMOneTimeWordINDCPA`
states. -/
abbrev DEMOneTimeINDCPAOf {Msg : Type} (encMsg : Msg ↪ List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  DEMOneTimeINDCPAOn (fun _ _ _ _ => true) encMsg encryptSym

/-- Unrestricted `n`-bit key one-time symmetric IND-CPA implies one-time symmetric IND-CPA under
every polynomial-time admissibility predicate. -/
theorem DEMOneTimeINDCPAOf.demOneTimeINDCPAOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : DEMOneTimeINDCPAOf encMsg encryptSym)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool) :
    DEMOneTimeINDCPAOn valid encMsg encryptSym :=
  DEMOneTimeKeyINDCPAOf.demOneTimeKeyINDCPAOn h hvalid

/-- Normalized (`n`-bit key) one-time symmetric IND-CPA / semantic security for single-bit
encryption. -/
abbrev DEMOneTimeINDCPA (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)) : Prop :=
  DEMOneTimeINDCPAOf encBool encryptSym

/-- Normalized (`n`-bit key) one-time symmetric IND-CPA / semantic security for bit-word encryption
under Attack Game 2.1's equal-length rule ([BonehShoup2023], Section 2.2, p. 16): challenge pairs
with `m₀.length ≠ m₁.length` are inadmissible. -/
abbrev DEMOneTimeWordINDCPA
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)) : Prop :=
  DEMOneTimeINDCPAOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits encryptSym

/-- At the normalized key length `keyLen n = n`, `DEMOneTimeKeyINDCPAOn` is definitionally
`DEMOneTimeINDCPAOn`. -/
theorem demOneTimeKeyINDCPAOn_id {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (encMsg : Msg ↪ List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)) :
    DEMOneTimeKeyINDCPAOn valid encMsg (fun n => n) encryptSym ↔
      DEMOneTimeINDCPAOn valid encMsg encryptSym :=
  Iff.rfl

/-- Whenever `keyLen n = n` for all `n`, `DEMOneTimeINDCPAOn` implies `DEMOneTimeKeyINDCPAOn`. -/
theorem DEMOneTimeINDCPAOn.demOneTimeKeyINDCPAOn {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : DEMOneTimeINDCPAOn valid encMsg encryptSym) (hkeyLen : ∀ n, keyLen n = n) :
    DEMOneTimeKeyINDCPAOn valid encMsg keyLen encryptSym := by
  intro adversary hadversary
  simpa only [fun n => demKeyGameOn_eq_demGameOn_of_eq valid keyLen encryptSym adversary false
    (hkeyLen n),
    fun n => demKeyGameOn_eq_demGameOn_of_eq valid keyLen encryptSym adversary true
    (hkeyLen n)] using h adversary hadversary

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

/-- Deterministic KEM–DEM hybrid decryption ([BonehShoup2023], Exercises 11.9 and 12.5).
Reject noncanonical ciphertext-pair encodings, decapsulate the KEM component, and decrypt the DEM
component. Either component may reject with `none`; accepted empty keys/messages are preserved. -/
def hybridDecrypt {Msg : Type} (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decryptSym : ℕ → List Bool → List Bool → Option Msg)
    (n : ℕ) (sk ct : List Bool) : Option Msg :=
  if encPair encBits encBits (unframe ct, dropFrame ct) == ct then do
    let k ← decaps n sk (unframe ct)
    decryptSym n k (dropFrame ct)
  else
    none

/-- Hybrid encryption is uniform strict PPT when encapsulation and symmetric encryption are. -/
@[fun_prop]
theorem isPPTOn_hybridEncrypt {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun ⟨n, k, msg⟩ => encryptSym n k msg)) :
    IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun ⟨n, pk, msg⟩ => hybridEncrypt encaps encryptSym n pk msg) := by
  let E0 := encPair encUnary (encPair encBits encMsg)
  let E1 := encPair E0 (encPair encBits encBits)
  let hp1 := ComputableInPolyTime.fst encUnary (encPair encBits encMsg)
  let hp2 := ComputableInPolyTime.snd encUnary (encPair encBits encMsg)
  let hq1 := ComputableInPolyTime.fst E0 (encPair encBits encBits)
  let hq2 := ComputableInPolyTime.snd E0 (encPair encBits encBits)
  let hr1 := ComputableInPolyTime.fst E1 encBits
  let hr2 := ComputableInPolyTime.snd E1 encBits
  exact (hencaps.preprocess (hp1.prod hp2.fst')).bind_with
    ((hencryptSym.preprocess
      ((hp1.comp' hq1).prod (hq2.fst'.prod (hp2.snd'.comp' hq1)))).bind_with
      (((hq2.snd'.comp' hr1).prod hr2).encoding_comp.isPPTOn))

/-- Hybrid decryption is computable in polynomial time when decapsulation and symmetric decryption
are computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_hybridDecrypt {Msg : Type} {encMsg : Msg ↪ List Bool}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    {decryptSym : ℕ → List Bool → List Bool → Option Msg}
    (hdecaps : ComputableInPolyTime
      (fun ⟨n, sk, ctKem⟩ => decaps n sk ctKem)
      (encPair encUnary (encPair encBits encBits)) (encOption encBits))
    (hdecryptSym : ComputableInPolyTime
      (fun ⟨n, k, ctDem⟩ => decryptSym n k ctDem)
      (encPair encUnary (encPair encBits encBits)) (encOption encMsg)) :
    ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => hybridDecrypt decaps decryptSym n sk ct)
      (encPair encUnary (encPair encBits encBits)) (encOption encMsg) := by
  let I := encPair encUnary (encPair encBits encBits)
  have hn := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  have hrest := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  have hsk := hrest.fst'
  have hct := hrest.snd'
  have hkem := ComputableInPolyTime.unframe.comp hct
  have hdem := ComputableInPolyTime.dropFrame.comp hct
  have hcanonical := ComputableInPolyTime.beq (encB := encBits)
    (hkem.prod hdem).encoding_comp hct
  have hkey := hdecaps.comp (hn.prod (hsk.prod hkem))
  have hinput := ComputableInPolyTime.fst I encBits
  have hvalue := ComputableInPolyTime.snd I encBits
  have hbody := hdecryptSym.comp
    ((hn.comp hinput).prod (hvalue.prod (hdem.comp hinput)))
  have hrun := hkey.optionElimWithInput
    (body := fun (p : ℕ × List Bool × List Bool) k => decryptSym p.1 k (dropFrame p.2.2))
    (encC := encOption encMsg) (ComputableInPolyTime.const none) hbody
  have hbind : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => do
        let k ← decaps p.1 p.2.1 (unframe p.2.2)
        decryptSym p.1 k (dropFrame p.2.2)) I (encOption encMsg) := by
    convert hrun using 1
    funext p
    dsimp only [Function.comp_def]
    cases decaps p.1 p.2.1 (unframe p.2.2) <;> rfl
  exact ComputableInPolyTime.ite hcanonical hbind (ComputableInPolyTime.const none)

/-- Malformed ciphertext-pair encodings are rejected before either component is used. -/
theorem hybridDecrypt_of_not_canonical {Msg : Type}
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decryptSym : ℕ → List Bool → List Bool → Option Msg)
    (n : ℕ) (sk ct : List Bool)
    (hct : encPair encBits encBits (unframe ct, dropFrame ct) ≠ ct) :
    hybridDecrypt decaps decryptSym n sk ct = none := by
  simp only [hybridDecrypt, beq_iff_eq, ite_eq_right hct]

/-- Decryption of a canonical pair decapsulates its KEM component and propagates any rejection
before invoking symmetric decryption on the DEM component. -/
theorem hybridDecrypt_encPair {Msg : Type}
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (decryptSym : ℕ → List Bool → List Bool → Option Msg)
    (n : ℕ) (sk ctKem ctDem : List Bool) :
    hybridDecrypt decaps decryptSym n sk (encPair encBits encBits (ctKem, ctDem)) = (do
      let k ← decaps n sk ctKem
      decryptSym n k ctDem) := by
  simp [hybridDecrypt, encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append]

/-- **Hybrid decryption correctness**: supported encapsulations decapsulate to `some k`, and
supported symmetric ciphertexts decrypt to `some msg`. Then every supported hybrid ciphertext
decrypts to `some msg`, including the empty-key and empty-message cases. -/
theorem hybridDecrypt_hybridEncrypt {Msg : Type}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → Option (List Bool)}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decryptSym : ℕ → List Bool → List Bool → Option Msg}
    {n : ℕ} {pk sk ct : List Bool} {msg : Msg}
    (hkem : ∀ k ctKem, (k, ctKem) ∈ (ProbComp.eval (encaps n pk)).support →
      decaps n sk ctKem = some k)
    (hdem : ∀ k ctDem, (∃ ctKem, (k, ctKem) ∈ (ProbComp.eval (encaps n pk)).support) →
      ctDem ∈ (ProbComp.eval (encryptSym n k msg)).support →
      decryptSym n k ctDem = some msg)
    (hct : ct ∈ (ProbComp.eval (hybridEncrypt encaps encryptSym n pk msg)).support) :
    hybridDecrypt decaps decryptSym n sk ct = some msg := by
  simp only [hybridEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  rcases hct with ⟨⟨k, ctKem⟩, hkc, ctDem, hdemSupp, rfl⟩
  rw [hybridDecrypt_encPair, hkem k ctKem hkc]
  exact hdem k ctDem ⟨ctKem, hkc⟩ hdemSupp

/-! ### Boneh–Shoup Exercise 11.9(b) Reductions and Asymptotic Security -/

/-- The intermediate hybrid game $G_1$ for the standard hybrid argument of
[BonehShoup2023], Exercise 11.9(b): identical to
`Encryption.game keyGen (hybridEncrypt encaps encryptSym)` except that the symmetric key passed to
`encryptSym` is an independent uniform `keyLen n`-bit key rather than
`encapsulated.1`. -/
noncomputable def hybridIdealGame {Msg : Type} (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← adversary.choose n keys.1
  let encapsulated ← encaps n keys.1
  let kIdeal ← BitString.sampleList (keyLen n)
  let ctDem ← encryptSym n kIdeal
    (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
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
  let ctDem ← encryptSym n k
    (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
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
  let ctDem ← encryptSym n k
    (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
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
      (fun ⟨n, k, msg⟩ => encryptSym n k msg))
    (hadversary : AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    IsPPT encBool (hybridToKEMDistinguisher encryptSym adversary bit) := by
  let E0 := encPair encUnary encBits
  let EChoice := encPair (encPair encMsg encMsg) encBits
  let E1 := encPair E0 EChoice
  let hp1 := ComputableInPolyTime.fst encUnary encBits
  let hp2 := ComputableInPolyTime.snd encUnary encBits
  let hq1 := ComputableInPolyTime.fst E0 EChoice
  let hq2 := ComputableInPolyTime.snd E0 EChoice
  let hr1 := ComputableInPolyTime.fst E1 encBits
  let hr2 := ComputableInPolyTime.snd E1 encBits
  have hrest := ComputableInPolyTime.dropFrame.comp' hp2
  exact (hadversary.choose.on.preprocess
    (hp1.prod (ComputableInPolyTime.unframe.comp' hp2))).bind_with
    ((hencryptSym.preprocess
      ((hp1.comp' hq1).prod
        ((ComputableInPolyTime.unframe.comp' (hrest.comp' hq1)).prod
          ((ComputableInPolyTime.const (encOut := encBool) bit).ite
            hq2.fst'.snd' hq2.fst'.fst')))).bind_with
      (hadversary.guess.preprocess
        ((hp1.comp' (hq1.comp' hr1)).prod
          ((hq2.snd'.comp' hr1).prod
            (((ComputableInPolyTime.dropFrame.comp' (hrest.comp' (hq1.comp' hr1))).prod
              hr2).encoding_comp)))))

/-- `hybridToKEMHiddenBitDistinguisher` is uniform strict PPT whenever symmetric encryption and the
hybrid adversary are. -/
theorem isPPT_hybridToKEMHiddenBitDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {adversary : AdversaryOf Msg}
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun ⟨n, k, msg⟩ => encryptSym n k msg))
    (hadversary : AdversaryOf.IsPPT encMsg adversary) :
    IsPPT encBool (hybridToKEMHiddenBitDistinguisher encryptSym adversary) := by
  let E0 := encPair encUnary encBits
  let EChoice := encPair (encPair encMsg encMsg) encBits
  let E1 := encPair E0 EChoice
  let E2 := encPair E1 encBool
  let E3 := encPair E2 encBits
  let hp1 := ComputableInPolyTime.fst encUnary encBits
  let hp2 := ComputableInPolyTime.snd encUnary encBits
  let hq1 := ComputableInPolyTime.fst E0 EChoice
  let hq2 := ComputableInPolyTime.snd E0 EChoice
  let hr1 := ComputableInPolyTime.fst E1 encBool
  let hr2 := ComputableInPolyTime.snd E1 encBool
  let hs1 := ComputableInPolyTime.fst E2 encBits
  let hs2 := ComputableInPolyTime.snd E2 encBits
  let ht1 := ComputableInPolyTime.fst E3 encBool
  let ht2 := ComputableInPolyTime.snd E3 encBool
  have hrest := ComputableInPolyTime.dropFrame.comp' hp2
  have h0_2 := hq1.comp' hr1
  have h0_3 := h0_2.comp' hs1
  exact (hadversary.choose.on.preprocess
    (hp1.prod (ComputableInPolyTime.unframe.comp' hp2))).bind_with
    ((isPPTOn_uniform_bool E1).bind_with
      ((hencryptSym.preprocess
        ((hp1.comp' h0_2).prod
          ((ComputableInPolyTime.unframe.comp' (hrest.comp' h0_2)).prod
            (hr2.ite (hq2.fst'.snd'.comp' hr1) (hq2.fst'.fst'.comp' hr1))))).bind_with
        ((hadversary.guess.preprocess
          ((hp1.comp' h0_3).prod
            ((hq2.snd'.comp' (hr1.comp' hs1)).prod
              (((ComputableInPolyTime.dropFrame.comp' (hrest.comp' h0_3)).prod
                hs2).encoding_comp)))).bind_with
          ((ComputableInPolyTime.bool_xor.comp'
            (ht2.prod (hr2.comp' (hs1.comp' ht1)))).isPPTOn))))

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
  let EChoice := encPair (encPair encMsg encMsg) encBits
  let E2 := encPair E1 EChoice
  let hp1 := ComputableInPolyTime.fst encUnary encBits
  let hq1 := ComputableInPolyTime.fst E0 (encPair encBits encBits)
  let hq2 := ComputableInPolyTime.snd E0 (encPair encBits encBits)
  let hr1 := ComputableInPolyTime.fst E1 EChoice
  let hr2 := ComputableInPolyTime.snd E1 EChoice
  let hs1 := ComputableInPolyTime.fst E2 (encPair encBits encBits)
  let hs2 := ComputableInPolyTime.snd E2 (encPair encBits encBits)
  let hg1 := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  let hg2 := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  refine ⟨(hkeyGen.preprocess hp1).bind_with
    ((hadversary.choose.on.preprocess ((hp1.comp' hq1).prod hq2.fst')).bind_with
      ((hencaps.preprocess (((hp1.comp' hq1).comp' hr1).prod (hq2.fst'.comp' hr1))).bind_with
        (((hr2.fst'.comp' hs1).prod
          ((hs2.snd'.prod (hr2.snd'.comp' hs1)).encoding_comp)).isPPTOn))),
    hadversary.guess.preprocess
      (hg1.prod
        ((ComputableInPolyTime.dropFrame.comp' hg2.fst').prod
          (((ComputableInPolyTime.unframe.comp' hg2.fst').prod hg2.snd').encoding_comp)))⟩

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
  simp only [kemRealGame, kemRealGameWith,
    hybridToKEMDistinguisher, game, gameOn, ↓reduceIte, hybridEncrypt,
    encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  pmf_swap

/-- In the ideal KEM experiment, `hybridToKEMDistinguisher` reproduces the intermediate game
`hybridIdealGame`. -/
@[simp] theorem eval_kemIdealGame_hybridToKEMDistinguisher {Msg : Type} (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (kemIdealGame keyLen keyGen encaps
            (hybridToKEMDistinguisher encryptSym adversary bit) n) =
      ProbComp.eval (hybridIdealGame keyLen keyGen encaps encryptSym adversary bit n) := by
  simp only [kemIdealGame, kemIdealGameWith, kemRealGameWith,
    hybridToKEMDistinguisher, hybridIdealGame, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind]
  pmf_swap

/-- In the one-time symmetric DEM experiment, `hybridToDEMAdversary` reproduces the intermediate
game `hybridIdealGame`. -/
@[simp] theorem eval_demKeyGame_hybridToDEMAdversary {Msg : Type} (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (demKeyGame keyLen encryptSym (hybridToDEMAdversary keyGen encaps adversary) bit n) =
      ProbComp.eval (hybridIdealGame keyLen keyGen encaps encryptSym adversary bit n) := by
  simp only [demKeyGame, demKeyGameOn, ↓reduceIte, hybridToDEMAdversary, hybridIdealGame,
    ChoiceOut.msgs, ChoiceOut.msg₀, ChoiceOut.msg₁, encPair_apply,
    encBits_apply, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
    unframe_frame_append, dropFrame_frame_append]
  pmf_swap

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
  simp only [kemRealGame, kemRealGameWith,
    hybridToKEMHiddenBitDistinguisher, game, gameOn, ↓reduceIte,
    hybridEncrypt, encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.bind_bind, PMF.pure_bind, PMF.map_bind]
  pmf_swap

/-- In the ideal KEM experiment, `hybridToKEMHiddenBitDistinguisher` averages the two intermediate
games `hybridIdealGame`, complementing the second. -/
theorem eval_kemIdealGame_hybridToKEMHiddenBitDistinguisher {Msg : Type} (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (n : ℕ) :
    ProbComp.eval
      (kemIdealGame keyLen keyGen encaps
        (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n) =
      (do
        let bit ← PMF.uniformOfFintype Bool
        (ProbComp.eval (hybridIdealGame keyLen keyGen encaps encryptSym adversary bit n)).map
          (fun guess => guess ^^ bit)) := by
  simp only [kemIdealGame, kemIdealGameWith, kemRealGameWith,
    hybridToKEMHiddenBitDistinguisher, hybridIdealGame, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind]
  pmf_swap

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
  exact Game.succProbability_uniform_bool_xor _

/-- Success probability of `hybridToKEMHiddenBitDistinguisher` in `kemIdealGame` is one half plus
half the signed `hybridIdealGame` gap. -/
theorem probability_kemIdealGame_hybridToKEMHiddenBitDistinguisher {Msg : Type} (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (kemIdealGame keyLen keyGen encaps
        (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n)) : ℝ) =
      (1 + (Game.succProbability (ProbComp.eval
        (hybridIdealGame keyLen keyGen encaps encryptSym adversary false n)) : ℝ) -
        Game.succProbability (ProbComp.eval
          (hybridIdealGame keyLen keyGen encaps encryptSym adversary true n))) / 2 := by
  rw [eval_kemIdealGame_hybridToKEMHiddenBitDistinguisher]
  exact Game.succProbability_uniform_bool_xor _

/-- **Quantitative KEM–DEM reduction via two per-bit KEM distinguishers** (two-distinguisher
variant of [BonehShoup2023], Exercise 11.9(b)): the hybrid IND-CPA advantage is bounded by the sum
of the KEM advantages of `hybridToKEMDistinguisher encryptSym adversary false` and
`hybridToKEMDistinguisher encryptSym adversary true`, plus the DEM advantage of
`hybridToDEMAdversary keyGen encaps adversary`. -/
theorem advantage_hybridGame_le {Msg : Type} (keyLen : ℕ → ℕ)
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
          (kemIdealGame keyLen keyGen encaps
            (hybridToKEMDistinguisher encryptSym adversary false) n)) +
      Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary true) n))
        (ProbComp.eval
          (kemIdealGame keyLen keyGen encaps
            (hybridToKEMDistinguisher encryptSym adversary true) n)) +
      Game.advantage
        (ProbComp.eval
          (demKeyGame keyLen encryptSym (hybridToDEMAdversary keyGen encaps adversary) false n))
        (ProbComp.eval
          (demKeyGame keyLen encryptSym
            (hybridToDEMAdversary keyGen encaps adversary) true n)) := by
  simp only [eval_kemRealGame_hybridToKEMDistinguisher, eval_kemIdealGame_hybridToKEMDistinguisher,
    eval_demKeyGame_hybridToDEMAdversary]
  have h1 := Game.advantage_triangle
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary false n))
    (ProbComp.eval (hybridIdealGame keyLen keyGen encaps encryptSym adversary false n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))
  have h2 := Game.advantage_triangle
    (ProbComp.eval (hybridIdealGame keyLen keyGen encaps encryptSym adversary false n))
    (ProbComp.eval (hybridIdealGame keyLen keyGen encaps encryptSym adversary true n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))
  rw [Game.advantage_comm
    (ProbComp.eval (hybridIdealGame keyLen keyGen encaps encryptSym adversary true n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))] at h2
  exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by ac_rfl)

/-- **Quantitative KEM–DEM reduction via a single hidden-bit KEM distinguisher** ([BonehShoup2023],
Exercise 11.9(b)): the hybrid IND-CPA advantage is at most twice the KEM advantage of
`hybridToKEMHiddenBitDistinguisher encryptSym adversary`, plus the DEM advantage of
`hybridToDEMAdversary keyGen encaps adversary`. -/
theorem advantage_hybridGame_le_two_mul {Msg : Type} (keyLen : ℕ → ℕ)
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
          (kemIdealGame keyLen keyGen encaps
        (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n)) +
      Game.advantage
        (ProbComp.eval
          (demKeyGame keyLen encryptSym (hybridToDEMAdversary keyGen encaps adversary) false n))
        (ProbComp.eval
          (demKeyGame keyLen encryptSym
            (hybridToDEMAdversary keyGen encaps adversary) true n)) := by
  rw [eval_demKeyGame_hybridToDEMAdversary, eval_demKeyGame_hybridToDEMAdversary,
    eval_kemRealGame_hybridToKEMHiddenBitDistinguisher,
    eval_kemIdealGame_hybridToKEMHiddenBitDistinguisher]
  exact Game.advantage_le_two_mul_uniform_bool_xor
    (fun bit => ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary bit n))
    (fun bit => ProbComp.eval (hybridIdealGame keyLen keyGen encaps encryptSym adversary bit n))

/-- **IND-CPA security of KEM–DEM hybrid encryption** ([BonehShoup2023], Exercise 11.9(b)):
if `(keyGen, encaps)` is an IND-CPA secure KEM and `encryptSym` is a one-time IND-CPA secure DEM
over `encMsg` at the same `keyLen` (with uniform strict PPT honest algorithms), then
`hybridEncrypt encaps encryptSym` is IND-CPA secure over `encMsg`. -/
theorem KEMINDCPA.hybrid_indcpa {keyLen : ℕ → ℕ} {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hkem : KEMINDCPA keyLen keyGen encaps)
    (hdem : DEMOneTimeKeyINDCPAOf encMsg keyLen encryptSym)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun ⟨n, k, msg⟩ => encryptSym n k msg)) :
    INDCPAOf encMsg keyGen (hybridEncrypt encaps encryptSym) := by
  intro adversary hadversary
  have hkemFalse := hkem (hybridToKEMDistinguisher encryptSym adversary false)
    (isPPT_hybridToKEMDistinguisher hencryptSym hadversary false)
  have hkemTrue := hkem (hybridToKEMDistinguisher encryptSym adversary true)
    (isPPT_hybridToKEMDistinguisher hencryptSym hadversary true)
  have hdemAdv := hdem (hybridToDEMAdversary keyGen encaps adversary)
    (isPPT_hybridToDEMAdversary hkeyGen hencaps hadversary)
  exact negligible_of_le ((hkemFalse.add hkemTrue).add hdemAdv)
    (advantage_hybridGame_le keyLen keyGen encaps encryptSym adversary)

/-- When `valid` ignores the public key, running the unrestricted `demKeyGame keyLen` on the DEM
adversary built from `adversary.restrict valid` has the same output distribution as running
`demKeyGameOn valid keyLen` on it: an invalid pair already makes the restricted
adversary's guess `false`. -/
theorem eval_demKeyGame_hybridToDEMAdversary_restrict {Msg : Type} (keyLen : ℕ → ℕ)
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (hpk : ∀ n pk m₀ m₁, valid n pk m₀ m₁ = valid n [] m₀ m₁)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (demKeyGame keyLen encryptSym
        (hybridToDEMAdversary keyGen encaps (adversary.restrict valid)) bit n) =
      ProbComp.eval (demKeyGameOn valid keyLen encryptSym
        (hybridToDEMAdversary keyGen encaps (adversary.restrict valid)) bit n) := by
  simp only [demKeyGame, demKeyGameOn, hybridToDEMAdversary, AdversaryOf.restrict,
    ChoiceOut.msgs, ChoiceOut.msg₀, ChoiceOut.msg₁, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
    apply_ite ProbComp.eval, encPair_apply, encBits_apply, unframe_frame_append,
    dropFrame_frame_append]
  congr 1 with k : 1
  congr 1 with keys : 1
  congr 1 with choice : 1
  rw [hpk n keys.1]
  cases valid n [] choice.1.1 choice.1.2 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.headD_cons, List.tail_cons, PMF.bind_const]

/-- **IND-CPA security of KEM–DEM hybrid encryption under an admissibility predicate**
([BonehShoup2023], Exercise 11.9(b)), for a polynomial-time predicate `valid` that ignores the
public key, such as the equal-length rule: if `(keyGen, encaps)` is an IND-CPA secure KEM and
`encryptSym` satisfies `DEMOneTimeKeyINDCPAOn valid encMsg keyLen`, then
`hybridEncrypt encaps encryptSym` satisfies `INDCPAOn valid encMsg`. -/
theorem KEMINDCPA.hybrid_indcpaOn {keyLen : ℕ → ℕ} {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hkem : KEMINDCPA keyLen keyGen encaps)
    (hdem : DEMOneTimeKeyINDCPAOn valid encMsg keyLen encryptSym)
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hpk : ∀ n pk m₀ m₁, valid n pk m₀ m₁ = valid n [] m₀ m₁)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun ⟨n, k, msg⟩ => encryptSym n k msg)) :
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
  simpa only [eval_game_restrict, eval_demKeyGame_hybridToDEMAdversary_restrict keyLen valid hpk,
    Pi.add_apply] using
    advantage_hybridGame_le keyLen keyGen encaps encryptSym (adversary.restrict valid) n

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
      (fun ⟨n, k, bit⟩ => otpEncrypt n k bit) :=
  let hp2 := ComputableInPolyTime.snd encUnary (encPair encBits encBool)
  (ComputableInPolyTime.bitsCons
    (ComputableInPolyTime.bool_xor.comp'
      (((ComputableInPolyTime.headD false).comp' hp2.fst').prod hp2.snd'))
    (.const [])).isPPTOn

/-- One-time pad decryption is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_otpDecrypt :
    ComputableInPolyTime
      (fun ⟨n, k, ct⟩ => otpDecrypt n k ct)
      (encPair encUnary (encPair encBits encBits)) encBool :=
  let hp2 := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  ComputableInPolyTime.bool_xor.comp'
    (((ComputableInPolyTime.headD false).comp' hp2.fst').prod
      ((ComputableInPolyTime.headD false).comp' hp2.snd'))

/-- For `1 ≤ n`, a uniform `n`-bit key masks the challenge bit perfectly in `demGame otpEncrypt`,
so the `false` and `true` experiment distributions are identical. -/
theorem eval_demGame_otpEncrypt_false_eq_true {n : ℕ} (hn : 1 ≤ n) (adversary : Adversary) :
    ProbComp.eval (demGame otpEncrypt adversary false n) =
      ProbComp.eval (demGame otpEncrypt adversary true n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [demGame, demGameOn, demKeyGameOn, otpEncrypt,
    ChoiceOut.msgs, ChoiceOut.msg₀, ChoiceOut.msg₁,
    ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, BitString.uniformList_succ, PMF.bind_bind, PMF.bind_map,
    Function.comp_def, PMF.pure_bind, List.headD_cons, Bool.false_eq_true, ↓reduceIte]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1 with tail : 1
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1 with choice : 1
  ext out
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_bool]
  cases choice.1.1 <;> cases choice.1.2 <;>
    simp only [Bool.bne_true, Bool.bne_false, Bool.not_true, Bool.not_false, add_comm]

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
  simp only [advantage_demGame_otpEncrypt_eq_zero hn adversary, mul_zero]

/-- **KEM-to-PKE corollary**: combining any IND-CPA secure KEM with the one-time pad DEM yields an
IND-CPA secure public-key bit-encryption scheme. -/
theorem KEMINDCPA.hybrid_otpEncrypt_indcpa
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkem : KEMINDCPA (fun n => n) keyGen encaps)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2)) :
    INDCPA keyGen (hybridEncrypt encaps otpEncrypt) :=
  hkem.hybrid_indcpa demOneTimeINDCPA_otpEncrypt hkeyGen hencaps isPPTOn_otpEncrypt

/-- One-time pad `keyLen n`-bit word symmetric encryption: XOR the `keyLen n`-bit key `k` with the
plaintext word `m` at width `keyLen n` using `BitString.listXor (keyLen n) [k, m]`. -/
def otpKeyWordEncrypt (keyLen : ℕ → ℕ) (n : ℕ) (k m : List Bool) : ProbComp (List Bool) :=
  pure (BitString.listXor (keyLen n) [k, m])

/-- One-time pad `keyLen n`-bit word symmetric decryption: XOR the `keyLen n`-bit key `k` with the
ciphertext word `ct` at width `keyLen n` using `BitString.listXor (keyLen n) [k, ct]`. -/
def otpKeyWordDecrypt (keyLen : ℕ → ℕ) (n : ℕ) (k ct : List Bool) : List Bool :=
  BitString.listXor (keyLen n) [k, ct]

/-- One-time pad word decryption at key length `keyLen` inverts encryption on every
`keyLen n`-bit plaintext word `m`. -/
theorem otpKeyWordDecrypt_otpKeyWordEncrypt (keyLen : ℕ → ℕ) (n : ℕ) (k : List Bool)
    {m : List Bool} (hm : m.length = keyLen n) :
    otpKeyWordDecrypt keyLen n k (BitString.listXor (keyLen n) [k, m]) = m :=
  BitString.listXor_pair_self_left_of_length k hm

/-- `otpKeyWordEncrypt keyLen` is uniform strict PPT whenever `keyLen` is computable in polynomial
time in unary. -/
@[fun_prop]
theorem isPPTOn_otpKeyWordEncrypt {keyLen : ℕ → ℕ}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => otpKeyWordEncrypt keyLen p.1 p.2.1 p.2.2) :=
  let hp1 := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  let hp2 := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  ((hkeyLen.comp' hp1).bitsXorWithInput (hp2.fst'.cons' (hp2.snd'.cons' (.const [])))).isPPTOn

/-- `otpKeyWordDecrypt keyLen` is computable in polynomial time whenever `keyLen` is computable in
polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_otpKeyWordDecrypt {keyLen : ℕ → ℕ}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        otpKeyWordDecrypt keyLen p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits :=
  let hp1 := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  let hp2 := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  (hkeyLen.comp' hp1).bitsXorWithInput (hp2.fst'.cons' (hp2.snd'.cons' (.const [])))

/-- A uniform `keyLen n`-bit key masks any challenge word perfectly in
`demKeyGame keyLen (otpKeyWordEncrypt keyLen)`, so the `false` and `true` experiment distributions
are identical for every `keyLen` and `n`. -/
theorem eval_demKeyGame_otpKeyWordEncrypt_false_eq_true (keyLen : ℕ → ℕ) (n : ℕ)
    (adversary : WordAdversary) :
    ProbComp.eval (demKeyGame keyLen (otpKeyWordEncrypt keyLen) adversary false n) =
      ProbComp.eval (demKeyGame keyLen (otpKeyWordEncrypt keyLen) adversary true n) := by
  have hpad (msg state : List Bool) :
      (do
        let k ← BitString.uniformList (keyLen n)
        ProbComp.eval
          (adversary.guess n state (BitString.listXor (keyLen n) [k, msg]))) =
      (do
        let ct ← BitString.uniformList (keyLen n)
        ProbComp.eval (adversary.guess n state ct)) := by
    have h := congrArg
      (fun law : PMF (List Bool) => law.bind (ProbComp.eval ∘ adversary.guess n state))
      (BitString.uniformList_map_listXor (keyLen n) msg)
    simpa only [PMF.bind_map, Function.comp_def, PMF.monad_bind_eq_bind] using h
  simp only [demKeyGame, demKeyGameOn, ↓reduceIte, otpKeyWordEncrypt, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind, Bool.false_eq_true]
  pmf_hoist (adversary.choose n []).eval
  congr 1 with choice : 1
  exact (hpad choice.1.1 choice.2).trans (hpad choice.1.2 choice.2).symm

/-- Every word adversary has exact advantage `0` in
`demKeyGame keyLen (otpKeyWordEncrypt keyLen)`. -/
theorem advantage_demKeyGame_otpKeyWordEncrypt_eq_zero (keyLen : ℕ → ℕ) (n : ℕ)
    (adversary : WordAdversary) :
    Game.advantage
      (ProbComp.eval (demKeyGame keyLen (otpKeyWordEncrypt keyLen) adversary false n))
      (ProbComp.eval (demKeyGame keyLen (otpKeyWordEncrypt keyLen) adversary true n)) = 0 := by
  rw [eval_demKeyGame_otpKeyWordEncrypt_false_eq_true keyLen n adversary, Game.advantage_self]

/-- **The `keyLen n`-bit word one-time pad is unconditionally one-time IND-CPA secure**
(`DEMOneTimeKeyINDCPAOf encBits keyLen (otpKeyWordEncrypt keyLen)`). -/
theorem demOneTimeKeyINDCPA_otpKeyWordEncrypt (keyLen : ℕ → ℕ) :
    DEMOneTimeKeyINDCPAOf encBits keyLen (otpKeyWordEncrypt keyLen) := by
  intro adversary _ c
  refine tendsto_const_nhds.congr' ?_
  filter_upwards with n
  simp only [advantage_demKeyGame_otpKeyWordEncrypt_eq_zero keyLen n adversary, mul_zero]

/-- **The `keyLen n`-bit word one-time pad satisfies equal-length word DEM security**
(`DEMOneTimeKeyWordINDCPA keyLen (otpKeyWordEncrypt keyLen)`). -/
theorem demOneTimeKeyWordINDCPA_otpKeyWordEncrypt (keyLen : ℕ → ℕ) :
    DEMOneTimeKeyWordINDCPA keyLen (otpKeyWordEncrypt keyLen) :=
  let hm := (ComputableInPolyTime.snd encUnary (encPair encBits (encPair encBits encBits))).snd'
  (demOneTimeKeyINDCPA_otpKeyWordEncrypt keyLen).demOneTimeKeyINDCPAOn
    (hm.fst'.length_bits_comp.beq hm.snd'.length_bits_comp)

/-- One-time pad `n`-bit word symmetric encryption: `otpKeyWordEncrypt` specialized to
`keyLen n = n`. -/
abbrev otpWordEncrypt (n : ℕ) (k m : List Bool) : ProbComp (List Bool) :=
  otpKeyWordEncrypt (fun m => m) n k m

/-- One-time pad `n`-bit word symmetric decryption: `otpKeyWordDecrypt` specialized to
`keyLen n = n`. -/
abbrev otpWordDecrypt (n : ℕ) (k ct : List Bool) : List Bool :=
  otpKeyWordDecrypt (fun m => m) n k ct

/-- One-time pad word decryption inverts one-time pad word encryption on every `n`-bit plaintext
word `m`. -/
theorem otpWordDecrypt_otpWordEncrypt {n : ℕ} (k : List Bool) {m : List Bool}
    (hm : m.length = n) :
    otpWordDecrypt n k (BitString.listXor n [k, m]) = m :=
  otpKeyWordDecrypt_otpKeyWordEncrypt (fun m => m) n k hm

/-- One-time pad word encryption is uniform strict PPT. -/
@[fun_prop]
theorem isPPTOn_otpWordEncrypt :
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun ⟨n, k, m⟩ => otpWordEncrypt n k m) :=
  isPPTOn_otpKeyWordEncrypt ComputableInPolyTime.id'

/-- One-time pad word decryption is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_otpWordDecrypt :
    ComputableInPolyTime
      (fun ⟨n, k, ct⟩ => otpWordDecrypt n k ct)
      (encPair encUnary (encPair encBits encBits)) encBits :=
  computableInPolyTime_otpKeyWordDecrypt ComputableInPolyTime.id'

/-- A uniform `n`-bit key masks any challenge word perfectly in `demGame otpWordEncrypt`, so the
`false` and `true` experiment distributions are identical for every `n`. -/
theorem eval_demGame_otpWordEncrypt_false_eq_true (n : ℕ) (adversary : WordAdversary) :
    ProbComp.eval (demGame otpWordEncrypt adversary false n) =
      ProbComp.eval (demGame otpWordEncrypt adversary true n) :=
  eval_demKeyGame_otpKeyWordEncrypt_false_eq_true (fun m => m) n adversary

/-- Every word adversary has exact advantage `0` in `demGame otpWordEncrypt`. -/
theorem advantage_demGame_otpWordEncrypt_eq_zero (n : ℕ) (adversary : WordAdversary) :
    Game.advantage (ProbComp.eval (demGame otpWordEncrypt adversary false n))
      (ProbComp.eval (demGame otpWordEncrypt adversary true n)) = 0 :=
  advantage_demKeyGame_otpKeyWordEncrypt_eq_zero (fun m => m) n adversary

/-- **The `n`-bit word one-time pad is unconditionally one-time IND-CPA secure**
(`DEMOneTimeINDCPAOf encBits otpWordEncrypt`). -/
theorem demOneTimeINDCPA_otpWordEncrypt : DEMOneTimeINDCPAOf encBits otpWordEncrypt :=
  demOneTimeKeyINDCPA_otpKeyWordEncrypt (fun m => m)

/-- **The `n`-bit word one-time pad satisfies equal-length word DEM security**
(`DEMOneTimeWordINDCPA otpWordEncrypt`). -/
theorem demOneTimeWordINDCPA_otpWordEncrypt : DEMOneTimeWordINDCPA otpWordEncrypt :=
  demOneTimeKeyWordINDCPA_otpKeyWordEncrypt (fun m => m)

/-- **KEM-to-word-PKE corollary**: combining any IND-CPA secure KEM with the `n`-bit word one-time
pad DEM yields a public-key word-encryption scheme satisfying `WordINDCPA`, through the
equal-length instance of `KEMINDCPA.hybrid_indcpaOn`. -/
theorem KEMINDCPA.hybrid_otpWordEncrypt_indcpa
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkem : KEMINDCPA (fun n => n) keyGen encaps)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2)) :
    WordINDCPA keyGen (hybridEncrypt encaps otpWordEncrypt) :=
  let hm := (ComputableInPolyTime.snd encUnary (encPair encBits (encPair encBits encBits))).snd'
  hkem.hybrid_indcpaOn demOneTimeWordINDCPA_otpWordEncrypt
    (hm.fst'.length_bits_comp.beq hm.snd'.length_bits_comp) (fun _ _ _ _ => rfl) hkeyGen hencaps
    isPPTOn_otpWordEncrypt

end Cslib.Crypto.Encryption
