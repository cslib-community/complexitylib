/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.Basic

/-!
# Tests for typed public-key encryption schemes

A bit scheme that masks the message with its public key is correct, and an adversary that reads
the mask from the public key wins its chosen-plaintext experiment with certainty, so the typed
experiment separates the two challenge bits. The word-level experiment `Encryption.gameOn` at one
parameter is the typed experiment of the scheme with the same algorithms; the PPT transfer
`Encryption.AdversaryOf.isPPT_toTwoStage` is checked in `CslibFrontierTests.Crypto.Experiment`.
-/

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

end CslibFrontierTests.Crypto.PKEScheme
