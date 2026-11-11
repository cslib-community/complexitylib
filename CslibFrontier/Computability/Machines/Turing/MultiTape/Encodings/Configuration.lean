/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Tape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.FiniteConfiguration
import Mathlib.Tactic.Linarith

/-!
# Encodings of finite binary machine configurations

The encoding stores the input, control, unary input position, work tapes, output and every query
and answer buffer. Its length bound charges replies separately from the machine clock: a short
oracle run may receive a long word.

## Main definitions

* `Turing.MultiTapeTM.encFiniteCfg`: encode ordinary finite binary storage.
* `Turing.MultiTapeTM.encFiniteConfig`: include the fixed family of oracle channels.

## Main results

* `Turing.MultiTapeTM.length_encFiniteConfig_le`: linear encoded storage under `SpaceBound`.

## References

Adapts Computability/Probabilistic/Configuration.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the existing finite configuration and encodings.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib.Turing MultiTapeMachine

variable {k : ℕ} {State : Type} [Finite State]

/-- Store the input, control, unary input position, complete work tapes and accumulated output. -/
noncomputable def encFiniteCfg : FiniteCfg k Bool State ↪ List Bool where
  toFun cfg := encPair encBits (encPair (encFinite (Option State))
    (encPair encUnary (encPair (encPi (encBiTape encBool)) encBits)))
    (cfg.input, cfg.state, cfg.inputPos.val, cfg.workTapes, cfg.output)
  inj' := by
    rintro ⟨input, state, pos, work, output⟩ ⟨input', state', pos', work', output'⟩ h
    have heq := (encPair _ _).injective h
    rcases Prod.mk.inj heq with ⟨rfl, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, heq⟩
    rcases Prod.mk.inj heq with ⟨hpos, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    cases Fin.ext hpos
    rfl

@[simp] theorem encFiniteCfg_apply (cfg : FiniteCfg k Bool State) :
    encFiniteCfg cfg = encPair encBits (encPair (encFinite (Option State))
      (encPair encUnary (encPair (encPi (encBiTape encBool)) encBits)))
      (cfg.input, cfg.state, cfg.inputPos.val, cfg.workTapes, cfg.output) := rfl

/-- Store the ordinary finite configuration and all pending requests and answer tapes. -/
noncomputable def encFiniteConfig {Oracle : Type} [Fintype Oracle] :
    FiniteConfig k Bool State Oracle ↪ List Bool where
  toFun cfg := encPair encFiniteCfg (encPi (encPair encBits (encBiTape encBool)))
    (cfg.tapes, cfg.channels)
  inj' := fun _ _ h => FiniteConfig.ext (congrArg Prod.fst ((encPair _ _).injective h))
    (congrArg Prod.snd ((encPair _ _).injective h))

@[simp] theorem encFiniteConfig_apply {Oracle : Type} [Fintype Oracle]
    (cfg : FiniteConfig k Bool State Oracle) :
    encFiniteConfig cfg = encPair encFiniteCfg (encPi (encPair encBits (encBiTape encBool)))
      (cfg.tapes, cfg.channels) := rfl

/-- The whole encoding is linear in input length, elapsed steps and the largest installed reply.
The constant depends only on the fixed control, channel type and number of work tapes. -/
theorem length_encFiniteConfig_le {Oracle : Type} [Fintype Oracle] : ∃ c : ℕ,
    ∀ (inputSize steps answerSize : ℕ) (cfg : FiniteConfig k Bool State Oracle),
      FiniteConfig.SpaceBound inputSize steps answerSize cfg →
      (encFiniteConfig cfg).length ≤ c * (inputSize + steps + answerSize + 1) := by
  refine ⟨19 + 4 * Nat.card (Option State) + 100 * k + 31 * Fintype.card Oracle, ?_⟩
  intro inputSize steps answerSize cfg h
  let bound := inputSize + steps + answerSize + 1
  have hpositive : 1 ≤ bound := by dsimp only [bound]; lia
  have htape (tape : BiTape Bool) (htape : tape.spaceUsed ≤ bound) :
      (encBiTape encBool tape).length ≤ 12 * bound :=
    (length_encBiTape_le encBool tape (bound := 1) (by simp)).trans
      (Nat.mul_le_mul_left 12 htape)
  have hwork : (encPi (encBiTape encBool) cfg.tapes.workTapes).length ≤ 25 * k * bound := by
    calc
      _ ≤ k * (2 * (12 * bound) + 1) := by
        simpa using length_encPi_le (encBiTape encBool) cfg.tapes.workTapes
          (fun tape => htape _ ((h.work tape).trans (by dsimp only [bound]; lia)))
      _ ≤ k * (25 * bound) := Nat.mul_le_mul_left k (by lia)
      _ = _ := by ac_rfl
  have hcontrol : (encFinite (Option State) cfg.tapes.state).length ≤
      Nat.card (Option State) * bound :=
    (length_encFinite_lt _).le.trans (by
      simpa using Nat.mul_le_mul_left (Nat.card (Option State)) hpositive)
  have hinput := h.input
  have hposition := cfg.tapes.inputPos.isLt
  have houtput := h.output
  have hcfg : (encFiniteCfg cfg.tapes).length ≤
      (9 + 2 * Nat.card (Option State) + 50 * k) * bound := by
    simp only [encFiniteCfg_apply, length_encPair, encBits_apply, encUnary_apply,
      List.length_replicate]
    dsimp only [bound] at *
    nlinarith
  have hchannel (channel : Oracle) :
      (encPair encBits (encBiTape encBool) (cfg.channels channel)).length ≤ 15 * bound := by
    have hquery := h.query channel
    have hanswer := htape _ ((h.answer channel).trans (by dsimp only [bound]; lia))
    simp only [length_encPair, encBits_apply]
    dsimp only [bound] at *
    lia
  have hchannels : (encPi (encPair encBits (encBiTape encBool)) cfg.channels).length ≤
      31 * Fintype.card Oracle * bound := by
    calc
      _ ≤ Fintype.card Oracle * (2 * (15 * bound) + 1) := length_encPi_le _ _ hchannel
      _ ≤ Fintype.card Oracle * (31 * bound) := Nat.mul_le_mul_left _ (by lia)
      _ = _ := by ac_rfl
  simp only [encFiniteConfig_apply, length_encPair]
  change _ ≤ (19 + 4 * Nat.card (Option State) + 100 * k + 31 * Fintype.card Oracle) * bound
  nlinarith

end Turing.MultiTapeTM
