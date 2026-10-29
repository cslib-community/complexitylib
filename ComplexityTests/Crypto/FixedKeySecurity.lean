/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.FixedKey.Bootstrapping
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT

/-!
Tests of the explicit circular experiment and fixed-key security reduction. Plaintext leakage
fails the circular premise, including when the ciphertext marginal hides it but the public key
reveals it. A message-discarding algorithm inhabits the security and native hypotheses, but
explicitly fails correctness; it is not a secure cryptosystem example.
-/

namespace ComplexityTests.Crypto.FixedKeySecurity

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Homomorphic Cslib.Probability
open Turing.MultiTapeTM

private def keyGen (_ : ℕ) : ProbComp (List Bool × List Bool) := pure ([], [true])

private def leak (_ : ℕ) (_ : List Bool) (bit : Bool) : ProbComp (List Bool) := pure [bit]

private def readSelf (_ : ℕ) (word : List Bool) : ProbComp Bool :=
  pure (((FixedKey.publicKeyDecoder.decode word).2.headD []).headD false)

private theorem readSelf_ppt : IsPPT encBool readSelf := by
  have hdecode := FixedKey.publicKeyDecoder.computableInPolyTime
  dsimp only [FixedKey.encPublicKey, Encryption.encCircularPublicKey] at hdecode
  have hread : ComputableInPolyTime
      (fun word => ((FixedKey.publicKeyDecoder.decode word).2.headD []).headD false)
      encBits encBool :=
    (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp
      ((ComputableInPolyTime.headD (encA := encBits) []).comp hdecode.snd')
  exact hread.isPPTOn.preprocess (ComputableInPolyTime.snd encUnary encBits)

private theorem eval_readSelf (real : Bool) (n : ℕ) :
    distinguishingGame
      ((ProbComp.eval (Encryption.circularPublicKey keyGen leak real n)).map
        Encryption.encCircularPublicKey) (readSelf n) = PMF.pure real := by
  cases real <;>
    simp [distinguishingGame, Encryption.circularPublicKey, keyGen, leak, readSelf,
      ProbComp.eval_pure, FixedKey.publicKeyDecoder.decode_enc]

-- The circular definition rejects the real-versus-zero leakage with advantage exactly one.
theorem not_circularSecure_leak : ¬ Encryption.CircularSecure keyGen leak := by
  intro hcircular
  have hnegligible := hcircular readSelf readSelf_ppt
  simp only [eval_readSelf] at hnegligible
  have hone : Game.advantage (PMF.pure true) (PMF.pure false) = 1 := by
    simp [Game.advantage, Game.succProbability]
  rw [hone] at hnegligible
  exact not_negligible_const one_ne_zero hnegligible

-- The ciphertext marginal alone hides the experiment bit, while its correlation with the
-- public key reveals it. This fixture is deliberately insecure and checks joint visibility.
private noncomputable def maskedKeyGen (_ : ℕ) : ProbComp (List Bool × List Bool) :=
  (fun bit => ([bit], [true])) <$> ProbComp.uniform Bool

private def maskedEncrypt (_ : ℕ) (pk : List Bool) (bit : Bool) : ProbComp (List Bool) :=
  pure [pk.headD false ^^ bit]

private def readJoint (_ : ℕ) (word : List Bool) : ProbComp Bool :=
  let artifact := FixedKey.publicKeyDecoder.decode word
  pure (artifact.1.headD false ^^ (artifact.2.headD []).headD false)

private theorem readJoint_ppt : IsPPT encBool readJoint := by
  have hdecode := FixedKey.publicKeyDecoder.computableInPolyTime
  dsimp only [FixedKey.encPublicKey, Encryption.encCircularPublicKey] at hdecode
  have hpublic := (ComputableInPolyTime.headD (encA := encBool)
    (encL := encBits) false).comp hdecode.fst'
  have hcipher := (ComputableInPolyTime.headD (encA := encBool)
    (encL := encBits) false).comp
    ((ComputableInPolyTime.headD (encA := encBits) []).comp hdecode.snd')
  have hread : ComputableInPolyTime
      (fun word => (FixedKey.publicKeyDecoder.decode word).1.headD false ^^
        ((FixedKey.publicKeyDecoder.decode word).2.headD []).headD false)
      encBits encBool := by fun_prop
  exact hread.isPPTOn.preprocess (ComputableInPolyTime.snd encUnary encBits)

private theorem eval_masked (real : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.circularPublicKey maskedKeyGen maskedEncrypt real n) =
      (PMF.uniformOfFintype Bool).map (fun bit => ([bit], [[bit ^^ real]])) := by
  cases real <;>
    simp [Encryption.circularPublicKey, maskedKeyGen, maskedEncrypt, PMF.map, Function.comp_def]

example (n : ℕ) :
    (ProbComp.eval (Encryption.circularPublicKey maskedKeyGen maskedEncrypt true n)).map
      Prod.snd =
    (ProbComp.eval (Encryption.circularPublicKey maskedKeyGen maskedEncrypt false n)).map
      Prod.snd := by
  simp only [eval_masked, PMF.map_comp, Function.comp_def]
  ext ciphertexts
  by_cases hfalse : ciphertexts = [[false]] <;>
    by_cases htrue : ciphertexts = [[true]] <;>
    simp [PMF.map_apply, tsum_fintype, hfalse, htrue]

private theorem eval_readJoint (real : Bool) (n : ℕ) :
    distinguishingGame
      ((ProbComp.eval (Encryption.circularPublicKey maskedKeyGen maskedEncrypt real n)).map
        Encryption.encCircularPublicKey) (readJoint n) = PMF.pure real := by
  rw [eval_masked]
  simp [distinguishingGame, readJoint, FixedKey.publicKeyDecoder.decode_enc,
    PMF.map, Function.comp_def]

example : ¬ Encryption.CircularSecure maskedKeyGen maskedEncrypt := by
  intro hcircular
  have hnegligible := hcircular readJoint readJoint_ppt
  simp only [eval_readJoint] at hnegligible
  have hone : Game.advantage (PMF.pure true) (PMF.pure false) = 1 := by
    simp [Game.advantage, Game.succProbability]
  rw [hone] at hnegligible
  exact not_negligible_const one_ne_zero hnegligible

private def forgetful : Scheme where
  keyGen := keyGen
  encrypt _ _ _ := pure []
  decrypt _ _ _ := false
  evaluate _ _ _ _ := pure []
  permitted _ _ := True

private theorem forgetful_secure : Encryption.INDCPA forgetful.keyGen forgetful.encrypt := by
  intro adversary _
  have heq (n : ℕ) :
      ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt adversary false n) =
      ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt adversary true n) := by
    simp [Encryption.game, Encryption.gameOn, forgetful]
  simpa only [heq, Game.advantage_self] using negligible_zero

private theorem forgetful_circular : Encryption.CircularSecure
    forgetful.keyGen forgetful.encrypt := by
  have heq (n : ℕ) :
      ProbComp.eval (Encryption.circularPublicKey forgetful.keyGen forgetful.encrypt true n) =
      ProbComp.eval (Encryption.circularPublicKey forgetful.keyGen forgetful.encrypt false n) := by
    simp [Encryption.circularPublicKey, forgetful, keyGen]
  simp only [Encryption.CircularSecure, heq]
  exact ComputationallyIndistinguishable.refl _

private theorem keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) forgetful.keyGen := by
  change IsPPTOn encUnary (encPair encBits encBits) (fun _ : ℕ => pure ([], [true]))
  ppt

private theorem encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => forgetful.encrypt p.1 p.2.1 p.2.2) := by
  dsimp only [forgetful]
  ppt

private theorem secret_width (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (forgetful.keyGen n)).support) : keys.2.length = 1 := by
  have heq : keys = ([], [true]) := by simpa [forgetful, keyGen] using hkeys
  simp [heq]

private def forgetfulCircuits : DecryptionCircuits forgetful (fun _ => 1) (fun _ => 0) where
  circuit _ := Circuit.oneGate (.const false) Fin.elim0
  correct _ _ _ _ _ := by simp [Circuit.eval_oneGate, Boolean.interpretation, forgetful]

-- All security premises have concrete inhabitants. The actual output scheme is used.
example : Encryption.INDCPA (FixedKey.scheme forgetfulCircuits).keyGen
    (FixedKey.scheme forgetfulCircuits).encrypt :=
  FixedKey.indCPA_scheme forgetfulCircuits forgetful_secure forgetful_circular keyGen_ppt
    encrypt_ppt secret_width

-- This fixture cannot satisfy correctness: its ciphertext discards the challenge bit.
example : ¬ forgetful.Correct := by
  intro hcorrect
  have h := hcorrect.decrypt_encrypt 0 ([], [true]) (by simp [forgetful, keyGen])
    true [] (by simp [forgetful])
  simp [forgetful] at h

-- Malformed state is still a valid input to the certified guessing stage.
private def stateful : Encryption.Adversary where
  choose _ pk := pure ((pk.headD false, !(pk.headD false)), pk)
  guess _ state ciphertext := pure (ciphertext.headD false ^^ state.headD false)

private theorem stateful_ppt : stateful.IsPPT := by
  constructor <;> dsimp only [stateful] <;> ppt

example : (FixedKey.zeroAdversary forgetful stateful).IsPPT :=
  FixedKey.isPPT_zeroAdversary encrypt_ppt stateful_ppt keyGen_ppt

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
      (FixedKey.zeroAdversary forgetful stateful) bit n) = PMF.pure false := by
  rw [FixedKey.eval_zeroAdversary forgetful stateful bit n 1 (secret_width n)]
  simp [Encryption.circularPublicKey, FixedKey.publicKeyGame, forgetful, keyGen, stateful,
    FixedKey.encPublicKey, Encryption.encCircularPublicKey, encPair, encBits, encList, frame]

end ComplexityTests.Crypto.FixedKeySecurity
