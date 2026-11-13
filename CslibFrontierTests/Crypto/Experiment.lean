/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Probabilistic.PPT.Composition
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
  rw [Experiment.coe_succProbability, ProbComp.probability_pure]
  rfl

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
  have h : Game.withSetup (PMF.uniformOfFintype Bool) pure = PMF.uniformOfFintype Bool := by
    simp only [Game.withSetup, ProbComp.eval_pure, PMF.bind_pure]
  rw [h, Game.coe_succProbability, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num

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
example (setup : PMF ℕ) (exp : ℕ → Experiment)
    (h : ∀ n, Experiment.succProbability (exp n) ≤ 1 / 4) :
    Game.succProbability (Game.withSetup setup exp) ≤ 1 / 4 :=
  Game.succProbability_withSetup_le setup exp fun n _ => h n

/-! ### Experiments with a setup program -/

-- A bound at every key that key generation can output bounds the experiment that generates the
-- key first, as in `do let (pk, _) ← keyGen; lrExperiment … pk`.
example {K M C σ : Type} (keyGen : ProbComp (K × K)) (valid : K → M → M → Bool)
    (enc : K → M → ProbComp C) (A : TwoStage K (MessagePair M) C Bool σ) {ε : ℝ≥0}
    (h : ∀ pk, Experiment.advantage (lrExperiment valid enc A true pk)
      (lrExperiment valid enc A false pk) ≤ ε) :
    Experiment.advantage (keyGen >>= fun key => lrExperiment valid enc A true key.1)
      (keyGen >>= fun key => lrExperiment valid enc A false key.1) ≤ ε :=
  Experiment.advantage_bind_le_of_support keyGen _ _ fun key _ => h key.1

-- Only keys that key generation can output matter: a forgery experiment that never wins on a
-- supported key has success probability zero.
example {K : Type} (keyGen : ProbComp K) (forge : K → Experiment)
    (h : ∀ k ∈ (ProbComp.eval keyGen).support, forge k = pure false) :
    Experiment.succProbability (keyGen >>= forge) ≤ 0 :=
  Experiment.succProbability_bind_le_of_support keyGen forge fun k hk => by
    rw [h k hk]
    simp [Experiment.succProbability, Game.succProbability, PMF.pure_apply]

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

-- With every pair admissible, `eval_lrExperiment` gives the output distribution as the challenge
-- on the chosen pair, the form a reduction's experiment is compared with.
example {I₁ M C σ : Type} (enc : I₁ → M → ProbComp C) (A : TwoStage I₁ (MessagePair M) C Bool σ)
    (b : Bool) (x : I₁) :
    ProbComp.eval (lrExperiment (fun _ _ _ => true) enc A b x) =
      (ProbComp.eval (A.choose x)).bind fun p =>
        (ProbComp.eval (enc x (p.1.select b))).bind fun c => ProbComp.eval (A.guess p.2 c) := by
  simp

-- A family with deterministic polynomial-time stages is PPT. The saved state is a typed pair, a
-- flag and the public key; the guess reads the flag back.
example : TwoStage.IsPPT encBits (encMessagePair encBits) encBits encBool
    (encPair encBool encBits)
    (fun _ => ⟨fun pk => pure (⟨pk, pk⟩, (true, pk)), fun state _ => pure state.1⟩) where
  choose := by
    refine ComputableInPolyTime.isPPTOn ?_
    have hpk := ComputableInPolyTime.snd encUnary encBits
    exact (encMessagePair_mk_polyTime hpk hpk).prod
      ((ComputableInPolyTime.const true).prod hpk)
  guess := ComputableInPolyTime.isPPTOn
    (ComputableInPolyTime.fst' (ComputableInPolyTime.fst'
      (ComputableInPolyTime.snd encUnary (encPair (encPair encBool encBits) encBits))))

-- Swapping the challenge messages is polynomial time on the message-pair encoding.
example : ComputableInPolyTime
    (fun pair : MessagePair (List Bool) => MessagePair.mk pair.msg₁ pair.msg₀)
    (encMessagePair encBits) (encMessagePair encBits) :=
  encMessagePair_mk_polyTime (encMessagePair_msg₁_polyTime .id') (encMessagePair_msg₀_polyTime .id')

/-! ### Word-level adversaries are the instance `σ := List Bool` -/

-- Encoded words unchanged: a message pair and its saved state are encoded exactly as the word
-- choice output `((m₀, m₁), state)` under `Encryption.encChoiceOut`.
example {Msg : Type} (encMsg : Msg ↪ List Bool) (pair : MessagePair Msg) (state : List Bool) :
    encPair (encMessagePair encMsg) encBits (pair, state) =
      Encryption.encChoiceOut encMsg ((pair.msg₀, pair.msg₁), state) :=
  rfl

-- A PPT word-level adversary is a PPT two-stage family over the same encodings, so typed
-- security quantifying over all state types implies word-level security.
example {Msg : Type} (encMsg : Msg ↪ List Bool) (adversary : Encryption.AdversaryOf Msg)
    (h : adversary.IsPPT encMsg) :
    TwoStage.IsPPT encBits (encMessagePair encMsg) encBits encBool encBits
      adversary.toTwoStage :=
  Encryption.AdversaryOf.isPPT_toTwoStage h

end CslibFrontierTests.Experiment
