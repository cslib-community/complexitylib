/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.Hybrid

/-!
# Tests for typed KEM–DEM hybrid encryption

A KEM that sends its random bit key in the clear is correct, and so is the one-bit one-time pad;
`KEM.hybrid_correct` combines them into a correct hybrid. With a uniform key, the one-time pad has
one-time advantage zero, so `KEM.advantage_hybrid_le_two_mul` bounds the chosen-plaintext advantage
of the hybrid of any bit-key KEM with the one-time pad by twice a single KEM advantage. The
word-level hybrid experiment at one parameter is the typed experiment of `wordKEM` and
`wordCipher`, played by the adversary's two-stage form.
-/

namespace CslibFrontierTests.Crypto.KEMDEM

open Cslib Cslib.Crypto Cslib.Probability

/-- Encapsulation of a random bit key, sent in the clear as the ciphertext. -/
noncomputable def clearKEM : KEM Unit Unit Bool Bool where
  keyGen := pure ((), ())
  encaps _ := do
    let key ← ProbComp.uniform Bool
    pure (key, key)
  decaps _ ct := some ct

/-- The one-bit one-time pad. -/
def otp : Cipher Bool Bool Bool where
  encrypt k m := pure (m ^^ k)
  decrypt k c := some (c ^^ k)

theorem clearKEM_correct : clearKEM.Correct := by
  intro keys _ ck hck
  simp only [clearKEM, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hck
  obtain ⟨key, -, rfl⟩ := hck
  rfl

theorem otp_correct : otp.Correct := by
  intro k m c hc
  simp only [otp, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
  simp [otp, hc]

-- The hybrid of the two correct components is correct.
example : (clearKEM.hybrid otp).Correct := KEM.hybrid_correct clearKEM_correct otp_correct

/-- With a uniform key, the one-time pad hides which message it encrypts. -/
theorem eval_oneTimeExperiment_otp {σ : Type} (valid : Bool → Bool → Bool)
    (A : TwoStage Unit (MessagePair Bool) Bool Bool σ) :
    ProbComp.eval (otp.oneTimeExperiment (ProbComp.uniform Bool) valid A true) =
      ProbComp.eval (otp.oneTimeExperiment (ProbComp.uniform Bool) valid A false) := by
  simp only [Cipher.oneTimeExperiment, otp, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_lrExperiment, ProbComp.eval_pure, PMF.pure_bind, MessagePair.select_true,
    MessagePair.select_false]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1 with choice : 1
  split
  · ext out
    simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_bool]
    cases choice.1.msg₀ <;> cases choice.1.msg₁ <;>
      simp only [Bool.bne_true, Bool.bne_false, Bool.not_true, Bool.not_false, add_comm]
  · rfl

/-- Every adversary has one-time advantage zero against the one-time pad with a uniform key. -/
theorem advantage_oneTimeExperiment_otp {σ : Type} (valid : Bool → Bool → Bool)
    (A : TwoStage Unit (MessagePair Bool) Bool Bool σ) :
    Experiment.advantage (otp.oneTimeExperiment (ProbComp.uniform Bool) valid A false)
      (otp.oneTimeExperiment (ProbComp.uniform Bool) valid A true) = 0 := by
  rw [Experiment.advantage, eval_oneTimeExperiment_otp, Game.advantage_self]

-- Against the hybrid of any bit-key KEM with the one-time pad, the chosen-plaintext advantage is
-- at most twice the KEM advantage of the single hidden-bit distinguisher.
example {PK SK CT σ : Type} (E : KEM PK SK CT Bool) (valid : Bool → Bool → Bool)
    (A : TwoStage PK (MessagePair Bool) (CT × Bool) Bool σ) :
    Experiment.advantage ((E.hybrid otp).cpaExperiment (fun _ => valid) A false)
        ((E.hybrid otp).cpaExperiment (fun _ => valid) A true) ≤
      2 * Experiment.advantage
        (E.cpaExperiment (ProbComp.uniform Bool) (KEM.hybridHiddenBitDistinguisher otp valid A)
          false)
        (E.cpaExperiment (ProbComp.uniform Bool) (KEM.hybridHiddenBitDistinguisher otp valid A)
          true) :=
  (KEM.advantage_hybrid_le_two_mul E _ otp valid A).trans_eq
    (by rw [advantage_oneTimeExperiment_otp, add_zero])

-- The word-level hybrid experiment at parameter `n` is the typed hybrid experiment of the word
-- KEM and DEM at `n`; decapsulation and symmetric decryption do not affect it.
example {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
        (Encryption.game keyGen (Encryption.hybridEncrypt encaps encryptSym) adversary bit n) =
      ProbComp.eval (((Encryption.wordKEM keyGen encaps (fun _ _ _ => none) n).hybrid
        (Encryption.wordCipher encryptSym (fun _ _ _ => none) n)).cpaExperiment
          (fun _ _ _ => true) (adversary.toHybridTwoStage n) bit) :=
  Encryption.eval_game_hybridEncrypt _ _ adversary bit n

end CslibFrontierTests.Crypto.KEMDEM
