/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind

/-!
# Key encapsulation from public-key encryption

`encryptKeyEncaps keyLen encrypt` samples a uniform `keyLen n`-bit key and encrypts it using
`encrypt`. This is [BonehShoup2023], Exercise 11.9(e), p. 461, with the source key space represented
by fixed-length bit words. A `WordINDCPA` scheme gives `KEMINDCPA` with exact reduction loss one.
The reduction samples two keys of the same length and retains one alongside the public key;
therefore it respects the existing equal-length challenge rule, including at key length zero.

Key generation and the total deterministic decryptor are reused unchanged. Correctness is a
separate supported-output theorem, and no failure symbol is added to this total-decapsulation
model. Native strict-PPT certificates for encapsulation and for the reduction expose the unary
polynomial-time key-length premise. Security itself does not assert correctness or sampleability
of the honest key generator.

## Main definitions

* `Cslib.Crypto.Encryption.encryptKeyEncaps`: encapsulate by encrypting a uniform key.
* `Cslib.Crypto.Encryption.kemToPKEChoose`: shared two-key chosen-message sampler.
* `Cslib.Crypto.Encryption.kemToPKEAdversary`: the loss-one chosen-message reduction.

## Main results

* `Cslib.Crypto.Encryption.isPPTOn_encryptKeyEncaps`: native encapsulation certificate.
* `Cslib.Crypto.Encryption.decrypt_encryptKeyEncaps`: correctness using the original decryptor.
* `Cslib.Crypto.Encryption.isPPTOn_kemToPKEChoose`: native shared sampler certificate.
* `Cslib.Crypto.Encryption.isPPT_kemToPKEAdversary`: native reduction certificate.
* `Cslib.Crypto.Encryption.advantage_encryptKeyEncaps_eq`: exact advantage preservation.
* `Cslib.Crypto.Encryption.WordINDCPA.kemINDCPA_encryptKeyEncaps`: secure PKE gives a secure KEM.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 11.9(e), p. 461.
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- Sample a uniform symmetric key and encrypt it under the public key
([BonehShoup2023], Exercise 11.9(e)). -/
@[expose] noncomputable def encryptKeyEncaps (keyLen : ℕ → ℕ)
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (n : ℕ) (pk : List Bool) : ProbComp (List Bool × List Bool) := do
  let k ← BitString.sampleList (keyLen n)
  let ct ← encrypt n pk k
  return (k, ct)

/-- Encapsulation is native strict PPT when the key-length schedule and encryption are. -/
@[fun_prop] theorem isPPTOn_encryptKeyEncaps {keyLen : ℕ → ℕ}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encryptKeyEncaps keyLen encrypt p.1 p.2) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 encBits
  let hp1 := ComputableInPolyTime.fst encUnary encBits
  let hq1 := ComputableInPolyTime.fst E0 encBits
  let hq2 := ComputableInPolyTime.snd E0 encBits
  let hr1 := ComputableInPolyTime.fst E1 encBits
  let hr2 := ComputableInPolyTime.snd E1 encBits
  exact ((hkeyLen.comp' hp1).sampleList).bind_with
    ((hencrypt.preprocess (hq1.fst'.prod (hq1.snd'.prod hq2))).bind_with
      ((hq2.comp' hr1).prod hr2).isPPTOn)

/-- The original total decryptor recovers every supported encapsulated key when it correctly
decrypts supported encryptions of words of length `keyLen n`. -/
theorem decrypt_encryptKeyEncaps {keyLen : ℕ → ℕ}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (decrypt : ℕ → List Bool → List Bool → List Bool)
    {n : ℕ} {pk sk k ct : List Bool}
    (hcorrect : ∀ m c, m.length = keyLen n →
      c ∈ (ProbComp.eval (encrypt n pk m)).support → decrypt n sk c = m)
    (h : (k, ct) ∈ (ProbComp.eval (encryptKeyEncaps keyLen encrypt n pk)).support) :
    decrypt n sk ct = k := by
  simp only [encryptKeyEncaps, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨k', hk, ct', hct, heq⟩ := h
  cases heq
  exact hcorrect _ _ (BitString.length_of_mem_support_uniformList hk) hct

/-- The common chosen-message stage of the CPA and CCA reductions: sample two independent
keys of equal length and retain the public key together with the first key. -/
@[expose] noncomputable def kemToPKEChoose (keyLen : ℕ → ℕ)
    (n : ℕ) (pk : List Bool) : ProbComp ((List Bool × List Bool) × List Bool) := do
  let k₀ ← BitString.sampleList (keyLen n)
  let k₁ ← BitString.sampleList (keyLen n)
  return ((k₀, k₁), encPair encBits encBits (pk, k₀))

/-- Reduce KEM distinguishing to word chosen-message encryption: choose independent keys
`k₀, k₁`, store `(pk, k₀)`, and give the distinguisher `(pk, (k₀, ct))` after encryption. -/
@[expose] noncomputable def kemToPKEAdversary (keyLen : ℕ → ℕ)
    (distinguisher : Distinguisher) : WordAdversary where
  choose := kemToPKEChoose keyLen
  guess n state ct :=
    distinguisher n
      (encPair encBits (encPair encBits encBits) (unframe state, (dropFrame state, ct)))

/-- The shared two-key sampler has a native strict-PPT certificate when its key-length
schedule is computable in polynomial time in unary. -/
@[fun_prop] theorem isPPTOn_kemToPKEChoose {keyLen : ℕ → ℕ}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    IsPPTOn (encPair encUnary encBits) (encPair (encPair encBits encBits) encBits)
      (fun p => kemToPKEChoose keyLen p.1 p.2) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 encBits
  let hp1 := ComputableInPolyTime.fst encUnary encBits
  let hq1 := ComputableInPolyTime.fst E0 encBits
  let hq2 := ComputableInPolyTime.snd E0 encBits
  let hr1 := ComputableInPolyTime.fst E1 encBits
  let hr2 := ComputableInPolyTime.snd E1 encBits
  exact ((hkeyLen.comp' hp1).sampleList).bind_with
    (((hkeyLen.comp' hq1.fst').sampleList).bind_with
      (((hq2.comp' hr1).prod hr2).prod
        (((hq1.snd'.comp' hr1).prod (hq2.comp' hr1)).encoding_comp)).isPPTOn)

/-- The KEM-to-PKE reduction is native uniform strict PPT, including its saved public key and
symmetric key, when the distinguisher and the unary key-length schedule are. -/
theorem isPPT_kemToPKEAdversary {keyLen : ℕ → ℕ} {distinguisher : Distinguisher}
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hdist : IsPPT encBool distinguisher) :
    (kemToPKEAdversary keyLen distinguisher).IsPPT := by
  refine ⟨isPPTOn_kemToPKEChoose hkeyLen, ?_⟩
  let hg1 := ComputableInPolyTime.fst encUnary (encPair encBits encBits)
  let hg2 := ComputableInPolyTime.snd encUnary (encPair encBits encBits)
  exact hdist.on.preprocess
    (hg1.prod (((ComputableInPolyTime.unframe.comp' hg2.fst').prod
      ((ComputableInPolyTime.dropFrame.comp' hg2.fst').prod hg2.snd')).encoding_comp))

private theorem eval_gameOn_kemToPKEAdversary (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (distinguisher : Distinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
      keyGen encrypt (kemToPKEAdversary keyLen distinguisher) bit n) =
      (do
        let keys ← ProbComp.eval (keyGen n)
        let k₀ ← BitString.uniformList (keyLen n)
        let k₁ ← BitString.uniformList (keyLen n)
        let ct ← ProbComp.eval (encrypt n keys.1 (if bit then k₁ else k₀))
        ProbComp.eval (distinguisher n
          (encPair encBits (encPair encBits encBits) (keys.1, (k₀, ct))))) := by
  simp only [pmf_norm, gameOn, kemToPKEAdversary, kemToPKEChoose, BitString.eval_sampleList,
    ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.msgs, encPair_apply, encBits_apply,
    unframe_frame_append, dropFrame_frame_append, apply_ite ProbComp.eval]
  congr 1; funext keys
  refine PMF.bind_congr_on_support _ _ _ fun k₀ hk₀ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun k₁ hk₁ => ?_
  simp [BitString.length_of_mem_support_uniformList hk₀,
    BitString.length_of_mem_support_uniformList hk₁]

/-- The first PKE experiment is exactly the real KEM experiment. -/
theorem eval_gameOn_kemToPKEAdversary_false (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (distinguisher : Distinguisher) (n : ℕ) :
    ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
      keyGen encrypt (kemToPKEAdversary keyLen distinguisher) false n) =
      ProbComp.eval (kemRealGame keyGen (encryptKeyEncaps keyLen encrypt) distinguisher n) := by
  rw [eval_gameOn_kemToPKEAdversary]
  simp [kemRealGame, kemRealGameWith, encryptKeyEncaps, ProbComp.eval_bind,
    BitString.eval_sampleList, PMF.bind_const]

/-- The second PKE experiment is exactly the ideal KEM experiment: the retained key is
independent of the key encrypted in the ciphertext. -/
theorem eval_gameOn_kemToPKEAdversary_true (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (distinguisher : Distinguisher) (n : ℕ) :
    ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
      keyGen encrypt (kemToPKEAdversary keyLen distinguisher) true n) =
      ProbComp.eval
        (kemIdealGame keyLen keyGen (encryptKeyEncaps keyLen encrypt) distinguisher n) := by
  rw [eval_gameOn_kemToPKEAdversary]
  simp only [pmf_norm, kemIdealGame, kemIdealGameWith, kemRealGameWith, encryptKeyEncaps,
    BitString.eval_sampleList, ↓reduceIte]
  congr 1; funext keys
  rw [PMF.bind_comm]
  congr 1; funext k
  rw [PMF.bind_comm]

/-- **Exact loss-one reduction** for the encrypted-key KEM of [BonehShoup2023], Exercise 11.9(e).
The two games use the same `keyLen n` key space and the same security parameter `n`. -/
theorem advantage_encryptKeyEncaps_eq (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (distinguisher : Distinguisher) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (kemRealGame keyGen (encryptKeyEncaps keyLen encrypt) distinguisher n))
      (ProbComp.eval
        (kemIdealGame keyLen keyGen (encryptKeyEncaps keyLen encrypt) distinguisher n)) =
    Encryption.advantage (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) keyGen encrypt
      (kemToPKEAdversary keyLen distinguisher)) n := by
  rw [advantage, eval_gameOn_kemToPKEAdversary_false, eval_gameOn_kemToPKEAdversary_true]

/-- **Semantically secure word encryption gives a secure KEM** ([BonehShoup2023],
Exercise 11.9(e)). The native reduction only samples keys and runs the supplied distinguisher. -/
theorem WordINDCPA.kemINDCPA_encryptKeyEncaps {keyLen : ℕ → ℕ}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hsecure : WordINDCPA keyGen encrypt)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    KEMINDCPA keyLen keyGen (encryptKeyEncaps keyLen encrypt) := by
  intro distinguisher hdist
  simpa only [advantage_encryptKeyEncaps_eq] using
    hsecure (kemToPKEAdversary keyLen distinguisher) (isPPT_kemToPKEAdversary hkeyLen hdist)

end Cslib.Crypto.Encryption
