/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.TwoStage
import CslibFrontier.Crypto.Computational.Encryption.Basic

/-! Clients of the experiment core (`Experiment`, `distAdvantage`, `Game.withSetup`) and of
two-stage adversaries (`TwoStage`, `TwoStage.IsPPT`, `MessagePair`, `lrExperiment`). -/

namespace CslibFrontierTests.Experiment

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Experiments and advantage -/

-- The experiment that always wins has success probability one.
example : (Experiment.succProbability (pure true) : ℝ) = 1 := by
  rw [Experiment.coe_succProbability, ProbComp.probability_pure, if_pos rfl]

-- The constant experiments are distinguished with advantage one, read as `|Pr[e₀] - Pr[e₁]|`.
example : (Experiment.advantage (pure true) (pure false) : ℝ) = 1 := by
  rw [Experiment.coe_advantage, ProbComp.probability_pure, ProbComp.probability_pure]
  norm_num

-- A distinguisher that outputs its view separates constant views with advantage one.
example : (distAdvantage (pure true) (pure false) pure : ℝ) = 1 := by
  simp only [distAdvantage, pure_bind]
  rw [Experiment.coe_advantage, ProbComp.probability_pure, ProbComp.probability_pure]
  norm_num

-- A perfect simulation gives every distinguisher advantage zero, whatever the distinguisher.
example (real sim : ProbComp ℕ) (h : ProbComp.eval real = ProbComp.eval sim)
    (D : ℕ → Experiment) : distAdvantage real sim D = 0 :=
  distAdvantage_eq_zero_of_eval_eq h D

/-! ### Games with a setup law -/

-- Averaging over a uniform parameter: the game that returns its parameter succeeds with
-- probability one half.
example : (Game.succProbability (Game.withSetup (PMF.uniformOfFintype Bool) pure) : ℝ) = 1 / 2 := by
  simp [Game.withSetup, Game.succProbability, PMF.bind_pure, PMF.uniformOfFintype_apply]

-- Only supported parameters matter: with the point law at `true`, experiments that differ
-- completely at `false` give games with advantage zero.
example (exp₀ exp₁ : Bool → Experiment) (h : exp₀ true = exp₁ true) :
    Game.advantage (Game.withSetup (PMF.pure true) exp₀) (Game.withSetup (PMF.pure true) exp₁) ≤
      0 := by
  refine Game.advantage_withSetup_le _ _ _ fun p hp => ?_
  rw [PMF.mem_support_pure_iff] at hp
  subst hp
  rw [h]
  exact (Game.advantage_self _).le

-- A bound on every supported success probability bounds the game.
example (setup : PMF ℕ) (exp : ℕ → Experiment) (h : ∀ n, Experiment.succProbability (exp n) ≤ 1 / 4) :
    Game.succProbability (Game.withSetup setup exp) ≤ 1 / 4 :=
  Game.succProbability_withSetup_le setup exp fun n _ => h n

/-! ### Two-stage adversaries and the left-or-right experiment -/

/-- The adversary that chooses `(false, true)` and guesses the challenge it receives. -/
def echo : TwoStage Unit (MessagePair Bool) Bool Bool Unit where
  choose _ := pure (⟨false, true⟩, ())
  guess _ challenge := pure challenge

-- Against the identity encryption, `echo` guesses the challenge bit.
theorem lrExperiment_echo (b : Bool) :
    lrExperiment (fun _ _ _ => true) (fun _ m => pure m) echo b () = pure b := by
  cases b <;> simp [lrExperiment, echo]

-- So the two sides of the left-or-right experiment are distinguished with advantage one.
example : (Experiment.advantage
    (lrExperiment (fun _ _ _ => true) (fun _ m => pure m) echo true ())
    (lrExperiment (fun _ _ _ => true) (fun _ m => pure m) echo false ()) : ℝ) = 1 := by
  rw [lrExperiment_echo, lrExperiment_echo, Experiment.coe_advantage, ProbComp.probability_pure,
    ProbComp.probability_pure]
  norm_num

-- An inadmissible pair outputs `false` on both sides.
example (b : Bool) :
    lrExperiment (fun _ _ _ => false) (fun _ m => pure m) echo b () = pure false := by
  simp [lrExperiment, echo]

-- A family with deterministic polynomial-time stages is PPT, with a typed saved state.
example : TwoStage.IsPPT encBits (encMessagePair encBits) encBits encBool encBits
    (fun _ => ⟨fun pk => pure (⟨pk, pk⟩, pk), fun _ _ => pure true⟩) where
  choose := by
    refine ComputableInPolyTime.isPPTOn ?_
    have hpk := ComputableInPolyTime.snd encUnary encBits
    exact (encMessagePair_mk_polyTime hpk hpk).prod hpk
  guess := ComputableInPolyTime.isPPTOn (ComputableInPolyTime.const true)

-- Swapping the challenge messages is polynomial time on the message-pair encoding.
example : ComputableInPolyTime (fun pair : MessagePair (List Bool) => MessagePair.mk pair.msg₁ pair.msg₀)
    (encMessagePair encBits) (encMessagePair encBits) :=
  encMessagePair_mk_polyTime (encMessagePair_msg₁_polyTime .id') (encMessagePair_msg₀_polyTime .id')

/-! ### Word-level adversaries are the instance `σ := List Bool` -/

/-- The two-stage family of a word-level chosen-message adversary: the same stages, with the
challenge pair as a `MessagePair`. -/
def ofWord {Msg : Type} (adversary : Encryption.AdversaryOf Msg) :
    ℕ → TwoStage (List Bool) (MessagePair Msg) (List Bool) Bool (List Bool) := fun n =>
  { choose := fun pk => (fun r => (⟨r.1.1, r.1.2⟩, r.2)) <$> adversary.choose n pk
    guess := adversary.guess n }

-- A PPT word-level adversary is a PPT two-stage family over the same encodings, so typed
-- security quantifying over all state types implies word-level security.
example {Msg : Type} (encMsg : Msg ↪ List Bool) (adversary : Encryption.AdversaryOf Msg)
    (h : adversary.IsPPT encMsg) :
    TwoStage.IsPPT encBits (encMessagePair encMsg) encBits encBool encBits (ofWord adversary) where
  choose := h.choose.on.map (ComputableInPolyTime.of_eq fun _ => rfl)
  guess := h.guess

end CslibFrontierTests.Experiment
