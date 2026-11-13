/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.Basic
import CslibFrontier.Crypto.Computational.Encryption.PublicKeyCPA

/-!
# Tests for typed public-key encryption schemes

A bit scheme that masks the message with its public key is correct, and an adversary that reads
the mask from the public key wins its chosen-plaintext experiment with certainty, so the typed
experiment separates the two challenge bits. An adversary that instead learns the mask by querying
the encryption oracle wins the chosen-plaintext experiment `PKE.cpaOracleExperiment` with
certainty, and `PKE.cpaOracleExperiment_eq_cpaExperiment` turns any such adversary into an
eavesdropper. The word-level experiments `Encryption.gameOn` and `Encryption.cpaOracleGameOn` at one
parameter are the typed experiments of the scheme with the same algorithms; the PPT transfer
`Encryption.AdversaryOf.isPPT_toTwoStage` is checked in `CslibFrontierTests.Crypto.Experiment`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.PKEScheme

open Cslib Cslib.Crypto Cslib.Probability

/-- Bit encryption that masks the message with a random key published as the public key. -/
noncomputable def maskPKE : PKE Bool Bool Bool Bool where
  keyGen := do
    let key ← ProbComp.uniform Bool
    pure (key, key)
  encrypt pk m := pure (m ^^ pk)
  decrypt sk c := some (c ^^ sk)

-- Decryption removes the mask, since the secret key equals the public key.
example : maskPKE.Correct := by
  intro keys hkeys m c hc
  simp only [maskPKE, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hkeys hc
  obtain ⟨key, -, rfl⟩ := hkeys
  simp [maskPKE, hc]

/-- Challenge `false` against `true`, keep the public key, and unmask the challenge. -/
def unmask : TwoStage Bool (MessagePair Bool) Bool Bool Bool where
  choose pk := pure (⟨false, true⟩, pk)
  guess pk c := pure (c ^^ pk)

/-- The unmasking adversary outputs the challenge bit with certainty. -/
theorem eval_cpaExperiment_unmask (b : Bool) :
    ProbComp.eval (maskPKE.cpaExperiment (fun _ _ _ => true) unmask b) = PMF.pure b := by
  have hconst (c : Bool) : (PMF.uniformOfFintype Bool).map (fun _ => c) = PMF.pure c :=
    PMF.map_const _ _
  cases b <;> simp [PKE.cpaExperiment, lrExperiment, maskPKE, unmask, hconst]

-- The typed experiment separates the two challenge bits: the advantage is one.
example : Experiment.advantage (maskPKE.cpaExperiment (fun _ _ _ => true) unmask false)
    (maskPKE.cpaExperiment (fun _ _ _ => true) unmask true) = 1 := by
  rw [Experiment.advantage, eval_cpaExperiment_unmask, eval_cpaExperiment_unmask]
  simp [Game.advantage, Game.succProbability]

-- The word-level experiment at parameter `n` is the left-or-right experiment on the public-key
-- marginal of `keyGen n`, played by the adversary's two-stage form.
example {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.gameOn valid keyGen encrypt adversary bit n) =
      Game.withSetup ((ProbComp.eval (keyGen n)).map Prod.fst)
        (lrExperiment (valid n) (encrypt n) (adversary.toTwoStage n) bit) := by
  rw [Encryption.gameOn_eq_cpaExperiment valid keyGen encrypt (fun _ _ => none),
    PKE.eval_cpaExperiment]

-- A bound on the typed experiment of every fixed scheme bounds the word-level advantage.
example {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : Encryption.AdversaryOf Msg) (ε : ℕ → NNReal)
    (h : ∀ n, Experiment.advantage
      ((PKE.mk (keyGen n) (encrypt n) fun _ _ => none).cpaExperiment (valid n)
        (adversary.toTwoStage n) false)
      ((PKE.mk (keyGen n) (encrypt n) fun _ _ => none).cpaExperiment (valid n)
        (adversary.toTwoStage n) true) ≤ ε n) (n : ℕ) :
    Encryption.advantage (Encryption.gameOn valid keyGen encrypt adversary) n ≤ ε n := by
  rw [Encryption.advantage_gameOn_eq_cpaExperiment valid keyGen encrypt fun _ _ => none]
  exact h n

/-- Learn the mask by asking the encryption oracle for the encryption of `false`, challenge `false`
against `true`, and unmask the challenge. -/
def oracleUnmask : PKE.CPAOracleAdversary Bool Bool Bool Bool where
  choose _ := do
    let mask ← ProbOracleComp.query false
    pure (⟨false, true⟩, mask)
  guess mask c := pure (c ^^ mask)

/-- The adversary that reads the mask from the oracle outputs the challenge bit with certainty. -/
theorem eval_cpaOracleExperiment_oracleUnmask (b : Bool) :
    ProbComp.eval (maskPKE.cpaOracleExperiment (fun _ _ _ => true) oracleUnmask b) =
      PMF.pure b := by
  have hconst (c : Bool) : (PMF.uniformOfFintype Bool).map (fun _ => c) = PMF.pure c :=
    PMF.map_const _ _
  cases b <;> simp [PKE.cpaOracleExperiment, maskPKE, oracleUnmask, hconst]

-- Its eavesdropping form, which encrypts its own query under the saved public key, also has
-- advantage one.
example : Experiment.advantage
    (maskPKE.cpaExperiment (fun _ _ _ => true) (oracleUnmask.toTwoStage maskPKE) false)
    (maskPKE.cpaExperiment (fun _ _ _ => true) (oracleUnmask.toTwoStage maskPKE) true) = 1 := by
  rw [← PKE.cpaOracleExperiment_eq_cpaExperiment, ← PKE.cpaOracleExperiment_eq_cpaExperiment,
    Experiment.advantage, eval_cpaOracleExperiment_oracleUnmask,
    eval_cpaOracleExperiment_oracleUnmask]
  simp [Game.advantage, Game.succProbability]

-- The word-level chosen-plaintext experiment at parameter `n` is the typed one, and hence the
-- eavesdropping experiment of the typed adversary's two-stage form.
example (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (adversary : Encryption.WordCPAAdversary) (bit : Bool) (n : ℕ) :
    Encryption.cpaOracleGameOn valid keyGen encrypt adversary bit n =
      (PKE.mk (keyGen n) (encrypt n) fun _ _ => none).cpaExperiment (valid n)
        ((adversary.toCPAOracleAdversary n).toTwoStage
          (PKE.mk (keyGen n) (encrypt n) fun _ _ => none)) bit := by
  rw [Encryption.cpaOracleGameOn_eq_cpaOracleExperiment valid keyGen encrypt fun _ _ => none,
    PKE.cpaOracleExperiment_eq_cpaExperiment]

end CslibFrontierTests.Crypto.PKEScheme
