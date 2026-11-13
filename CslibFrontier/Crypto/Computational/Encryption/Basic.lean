/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Computational.Encryption.Scheme
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Chosen-message security for public-key encryption

The adversary receives the public key, chooses two messages of type `Msg` and saves a finite
state, then receives an encryption of the selected message. Both stages are single uniform strict
PPT algorithms. Their clocks charge the unary security parameter and the complete encoded input,
including the saved state. The adversary may retain the public key in that state.

This is the single-challenge public-key experiment of
[Boneh and Shoup, Section 11.2, Attack Game 11.1, p. 436][BonehShoup2023]. That game requires the
two challenge messages to have the same length. Here admissibility is a Boolean predicate
`valid : ℕ → List Bool → Msg → Msg → Bool` on the security parameter, the public key and the
challenge pair: `gameOn valid` outputs `false` in both experiments when the pair is invalid, so an
invalid pair contributes no advantage. The unrestricted experiment `game` and notion `INDCPAOf`
are the always-true case. Single-bit messages (`Adversary`, `INDCPA`) are unrestricted, and
bit-word messages (`WordAdversary`, `WordINDCPA`) use the equal-length predicate
`fun _ _ m₀ m₁ => m₀.length == m₁.length`. For public-key encryption, further encryptions can be
computed from the public key. The separate multi-challenge equivalence of their Theorem 11.1 is
not formalized here. Encryption correctness and efficiency of the honest algorithms remain separate
properties.

## Main definitions

* `Cslib.Crypto.Encryption.AdversaryOf`, `Cslib.Crypto.Encryption.Adversary`,
  `Cslib.Crypto.Encryption.WordAdversary`: message selection and guessing with explicit saved
  state, for typed, bit, and bit-word messages.
* `Cslib.Crypto.Encryption.encChoiceOut`, `Cslib.Crypto.Encryption.encGuessInput`,
  `Cslib.Crypto.Encryption.encChallengePairInput`: the encodings of the message-selection output,
  of the guessing-stage input, and of the input of the admissibility predicate.
* `Cslib.Crypto.Encryption.AdversaryOf.IsPPT`, `Cslib.Crypto.Encryption.Adversary.IsPPT`,
  `Cslib.Crypto.Encryption.WordAdversary.IsPPT`: native uniform admissibility of both stages.
* `Cslib.Crypto.Encryption.gameOn`, `Cslib.Crypto.Encryption.game`: the key-generation and
  challenge-encryption experiment, with and without a challenge-pair admissibility predicate.
* `Cslib.Crypto.Encryption.advantage`: the advantage between the two sides of an experiment
  indexed by the challenge bit, such as `gameOn`, at one security parameter.
* `Cslib.Crypto.Encryption.INDCPAOn`, `Cslib.Crypto.Encryption.INDCPAOf`,
  `Cslib.Crypto.Encryption.INDCPA`, `Cslib.Crypto.Encryption.WordINDCPA`: negligible distinguishing
  advantage for every admissible adversary, fixed before the security parameter.
* `Cslib.Crypto.Encryption.AdversaryOf.restrict`: the adversary that plays `gameOn valid` inside
  the unrestricted `game`, by recording validity in its saved state.
* `Cslib.Crypto.Encryption.AdversaryOf.toTwoStage`: the two-stage adversary of the typed
  experiment `Cslib.Crypto.PKE.cpaExperiment` played at one parameter.

## Main results

* `Cslib.Crypto.Encryption.eval_gameOn`, `Cslib.Crypto.Encryption.eval_game`: the experiments
  depend only on the public-key marginal.
* `Cslib.Crypto.Encryption.eval_game_restrict`: `game` on `adversary.restrict valid` has the same
  output distribution as `gameOn valid` on `adversary`.
* `Cslib.Crypto.Encryption.gameOn_eq_cpaExperiment`,
  `Cslib.Crypto.Encryption.advantage_gameOn_eq_cpaExperiment`,
  `Cslib.Crypto.Encryption.AdversaryOf.isPPT_toTwoStage`: at each parameter, `gameOn` and its
  advantage are those of the typed chosen-plaintext experiment of the scheme with the same
  algorithms, and a PPT word-level adversary is a PPT two-stage family.
* `Cslib.Crypto.Encryption.INDCPAOn.congr`, `Cslib.Crypto.Encryption.INDCPAOf.congr`,
  `Cslib.Crypto.Encryption.INDCPA.congr`: distributionally equal honest algorithms have the same
  security guarantee.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2 (Attack Game 11.1, p. 436) and Section 11.3.2.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- A chosen-message adversary over message space `Msg`. The saved word contains all data retained
between stages. -/
structure AdversaryOf (Msg : Type) where
  /-- Receive the public key, choose the two challenge messages, and save a state. -/
  choose : ℕ → List Bool → ProbComp ((Msg × Msg) × List Bool)
  /-- Receive the saved state and challenge ciphertext, then return a distinguishing bit. -/
  guess : ℕ → List Bool → List Bool → ProbComp Bool

/-- Message-selection output `((m₀, m₁), state)`: the two challenge messages, each encoded by
`encMsg`, then the saved state word. The message pair is framed, and `m₀` is framed again inside
it. -/
abbrev encChoiceOut {Msg : Type} (encMsg : Msg ↪ List Bool) :
    (Msg × Msg) × List Bool ↪ List Bool :=
  encPair (encPair encMsg encMsg) encBits

/-- Guessing-stage input `(1ⁿ, state, ct)`: the security parameter `n` in unary, then the state
saved by message selection and the challenge ciphertext, both as bit words. The parameter and the
state are framed. The layout is that of the keyed-algorithm input `Cslib.Crypto.encKeyedInput
encBits`; the name records the role. -/
abbrev encGuessInput : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Input `(1ⁿ, pk, (m₀, m₁))` of a challenge-pair admissibility predicate `valid`: the security
parameter `n` in unary, the public key as a bit word, and the two challenge messages, each encoded
by `encMsg`. The parameter, the public key and `m₀` are framed. -/
abbrev encChallengePairInput {Msg : Type} (encMsg : Msg ↪ List Bool) :
    ℕ × List Bool × Msg × Msg ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encMsg encMsg))

/-- One finite-machine certificate for each whole stage over message encoding `encMsg`, including
the full saved-state cost. There is no parameter-dependent advice or separate algorithm for each
security parameter. -/
structure AdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : AdversaryOf Msg) : Prop where
  /-- Message selection is uniform strict PPT on the parameter and public key. -/
  choose : Probability.IsPPT (encChoiceOut encMsg) adversary.choose
  /-- Guessing is uniform strict PPT on the parameter, saved state, and challenge ciphertext. -/
  guess : IsPPTOn encGuessInput encBool
    (fun ⟨n, state, ciphertext⟩ => adversary.guess n state ciphertext)

/-- A chosen-message adversary for single-bit messages (`Bool`). -/
abbrev Adversary : Type := AdversaryOf Bool

/-- Phase 1 choice `((msg₀, msg₁), state)` returned by an `AdversaryOf Msg`. -/
abbrev ChoiceOut (Msg : Type) : Type := (Msg × Msg) × List Bool

/-- Challenge message pair `(msg₀, msg₁)` of a Phase 1 `ChoiceOut`. -/
abbrev ChoiceOut.msgs {Msg : Type} (c : ChoiceOut Msg) : Msg × Msg := c.1

/-- First challenge message `msg₀` of a Phase 1 `ChoiceOut`. -/
abbrev ChoiceOut.msg₀ {Msg : Type} (c : ChoiceOut Msg) : Msg :=
  (ChoiceOut.msgs c).1

/-- Second challenge message `msg₁` of a Phase 1 `ChoiceOut`. -/
abbrev ChoiceOut.msg₁ {Msg : Type} (c : ChoiceOut Msg) : Msg :=
  (ChoiceOut.msgs c).2

/-- Saved adversary state of a Phase 1 `ChoiceOut`. -/
abbrev ChoiceOut.state {Msg : Type} (c : ChoiceOut Msg) : List Bool := c.2

@[simp] theorem ChoiceOut.msg₀_mk {Msg : Type} (msgs : Msg × Msg) (st : List Bool) :
    ChoiceOut.msg₀ (msgs, st) = msgs.1 := rfl

@[simp] theorem ChoiceOut.msg₁_mk {Msg : Type} (msgs : Msg × Msg) (st : List Bool) :
    ChoiceOut.msg₁ (msgs, st) = msgs.2 := rfl

@[simp] theorem ChoiceOut.state_mk {Msg : Type} (msgs : Msg × Msg) (st : List Bool) :
    ChoiceOut.state (msgs, st) = st := rfl

/-- Native uniform strict PPT admissibility for a bit chosen-message adversary. -/
abbrev Adversary.IsPPT (adversary : Adversary) : Prop := AdversaryOf.IsPPT encBool adversary

/-- A chosen-message adversary for bit-word messages (`List Bool`). -/
abbrev WordAdversary : Type := AdversaryOf (List Bool)

/-- Native uniform strict PPT admissibility for a bit-word chosen-message adversary. -/
abbrev WordAdversary.IsPPT (adversary : WordAdversary) : Prop := AdversaryOf.IsPPT encBits adversary

/-- The single-challenge chosen-message experiment with challenge-pair admissibility predicate
`valid` ([BonehShoup2023], Section 11.2, Attack Game 11.1, p. 436). Sample the key pair and pass
the public key to `adversary.choose`. If `valid n pk m₀ m₁` holds for the chosen pair, encrypt the
selected message with the honest algorithm and return the adversary's guess; otherwise return
`false`, in both experiments. The secret key is never passed to the adversary. -/
def gameOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← adversary.choose n keys.1
  if valid n keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let ciphertext ← encrypt n keys.1
      (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
    adversary.guess n choice.2 ciphertext
  else
    return false

/-- The unrestricted chosen-message experiment: `gameOn` with every challenge pair admissible. -/
abbrev game {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  gameOn (fun _ _ _ _ => true) keyGen encrypt adversary bit n

/-- The distinguishing advantage of a two-sided experiment `experiment bit n` at parameter `n`:
the advantage between its runs with `bit = false` and `bit = true`. The adversary is already part
of `experiment`, as in `gameOn valid keyGen encrypt adversary`; `INDCPAOn` asks that this advantage
be negligible for every admissible adversary. -/
noncomputable abbrev advantage (experiment : Bool → ℕ → ProbComp Bool) (n : ℕ) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (experiment false n)) (ProbComp.eval (experiment true n))

/-- Single-challenge IND-CPA for encryption over message encoding `encMsg` with challenge-pair
admissibility predicate `valid`, against every uniform strict PPT adversary. The negligible bound
may depend on the adversary, which is fixed before the parameter. -/
def INDCPAOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool) (encMsg : Msg ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (gameOn valid keyGen encrypt adversary false n))
    (fun adversary n => ProbComp.eval (gameOn valid keyGen encrypt adversary true n))
    (AdversaryOf.IsPPT encMsg)

/-- Single-challenge IND-CPA with every challenge pair admissible. For message types whose
messages all have one length, such as `Bool`, this is the textbook notion; for `List Bool` it is
stronger than the textbook notion, which `WordINDCPA` states. -/
abbrev INDCPAOf {Msg : Type} (encMsg : Msg ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  INDCPAOn (fun _ _ _ _ => true) encMsg keyGen encrypt

/-- Single-challenge IND-CPA for bit encryption against every uniform strict PPT adversary. -/
abbrev INDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)) : Prop :=
  INDCPAOf encBool keyGen encrypt

/-- Single-challenge IND-CPA for bit-word encryption under Attack Game 11.1's equal-length rule
([BonehShoup2023], Section 11.2, p. 436): challenge pairs with `m₀.length ≠ m₁.length` are
inadmissible. -/
abbrev WordINDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) : Prop :=
  INDCPAOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits keyGen encrypt

/-- Only the public-key marginal of key generation is observed by `gameOn`. -/
theorem eval_gameOn {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (gameOn valid keyGen encrypt adversary bit n) =
      (do
        let pk ← (ProbComp.eval (keyGen n)).map Prod.fst
        let choice ← ProbComp.eval (adversary.choose n pk)
        if valid n pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
          let ciphertext ← ProbComp.eval
            (encrypt n pk (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice))
          ProbComp.eval (adversary.guess n (ChoiceOut.state choice) ciphertext)
        else
          pure false) := by
  simp only [pmf_norm, gameOn, apply_ite ProbComp.eval]

/-- Only the public-key marginal of key generation is observed by the unrestricted experiment. -/
theorem eval_game {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (game keyGen encrypt adversary bit n) =
      (do
        let pk ← (ProbComp.eval (keyGen n)).map Prod.fst
        let choice ← ProbComp.eval (adversary.choose n pk)
        let ciphertext ← ProbComp.eval
          (encrypt n pk (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice))
        ProbComp.eval (adversary.guess n (ChoiceOut.state choice) ciphertext)) := by
  simp only [game, eval_gameOn, ↓reduceIte]

/-- Equal public-key marginals and equal encryption laws preserve `INDCPAOn`. -/
theorem INDCPAOn.congr {Msg : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool}
    {keyGen keyGen' : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt encrypt' : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : INDCPAOn valid encMsg keyGen encrypt)
    (hkeyGen : ∀ n, (ProbComp.eval (keyGen n)).map Prod.fst =
      (ProbComp.eval (keyGen' n)).map Prod.fst)
    (hencrypt : ∀ n pk msg, ProbComp.eval (encrypt n pk msg) =
      ProbComp.eval (encrypt' n pk msg)) : INDCPAOn valid encMsg keyGen' encrypt' := by
  intro adversary hadversary
  simpa only [eval_gameOn, hkeyGen, hencrypt] using h adversary hadversary

/-- Equal public-key marginals and equal encryption laws preserve security. -/
theorem INDCPAOf.congr {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen keyGen' : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt encrypt' : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : INDCPAOf encMsg keyGen encrypt)
    (hkeyGen : ∀ n, (ProbComp.eval (keyGen n)).map Prod.fst =
      (ProbComp.eval (keyGen' n)).map Prod.fst)
    (hencrypt : ∀ n pk msg, ProbComp.eval (encrypt n pk msg) =
      ProbComp.eval (encrypt' n pk msg)) : INDCPAOf encMsg keyGen' encrypt' :=
  INDCPAOn.congr h hkeyGen hencrypt

/-- Equal public-key marginals and equal bit-encryption laws preserve security. -/
theorem INDCPA.congr {keyGen keyGen' : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt encrypt' : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (h : INDCPA keyGen encrypt)
    (hkeyGen : ∀ n, (ProbComp.eval (keyGen n)).map Prod.fst =
      (ProbComp.eval (keyGen' n)).map Prod.fst)
    (hencrypt : ∀ n pk bit, ProbComp.eval (encrypt n pk bit) =
      ProbComp.eval (encrypt' n pk bit)) : INDCPA keyGen' encrypt' :=
  INDCPAOn.congr h hkeyGen hencrypt

/-! ### Playing a restricted game inside the unrestricted one -/

/-- The adversary that plays `gameOn valid` inside the unrestricted `game`. Its `choose` runs
`adversary.choose n pk` and puts the bit `valid n pk m₀ m₁` in front of the saved state; its
`guess` returns `false` when that bit is `false` and otherwise runs `adversary.guess` on the rest of
the state. The challenge pair itself is passed on unchanged. -/
def AdversaryOf.restrict {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (adversary : AdversaryOf Msg) : AdversaryOf Msg where
  choose n pk := do
    let choice ← adversary.choose n pk
    return (choice.1,
      valid n pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) :: choice.2)
  guess n state ciphertext :=
    if state.headD false then adversary.guess n state.tail ciphertext else pure false

/-- Running the unrestricted `game` on `adversary.restrict valid` has the same output distribution
as running `gameOn valid` on `adversary`. -/
theorem eval_game_restrict {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (game keyGen encrypt (adversary.restrict valid) bit n) =
      ProbComp.eval (gameOn valid keyGen encrypt adversary bit n) := by
  simp only [pmf_norm, game, gameOn, AdversaryOf.restrict, ChoiceOut.msgs, ChoiceOut.msg₀,
    ChoiceOut.msg₁, ↓reduceIte, apply_ite ProbComp.eval]
  congr 1 with keys : 1
  congr 1 with choice : 1
  cases valid n keys.1 choice.1.1 choice.1.2 <;>
    simp [PMF.bind_const]

/-! ### Word-level algorithms as a typed scheme -/

/-- The two-stage adversary that `adversary` plays at parameter `n`: message selection returns
the chosen pair as a `MessagePair`, and the saved state word is the two-stage state. -/
def AdversaryOf.toTwoStage {Msg : Type} (adversary : AdversaryOf Msg) (n : ℕ) :
    TwoStage (List Bool) (MessagePair Msg) (List Bool) Bool (List Bool) where
  choose pk := (fun choice : ChoiceOut Msg =>
    (⟨ChoiceOut.msg₀ choice, ChoiceOut.msg₁ choice⟩, ChoiceOut.state choice)) <$>
      adversary.choose n pk
  guess := adversary.guess n

/-- A uniform strict PPT word-level adversary is a uniform strict PPT two-stage family over the
same encodings of the public key, challenge pair, ciphertext and state. -/
theorem AdversaryOf.isPPT_toTwoStage {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : AdversaryOf Msg} (h : adversary.IsPPT encMsg) :
    TwoStage.IsPPT encBits (encMessagePair encMsg) encBits encBool encBits
      adversary.toTwoStage where
  choose := IsPPTOn.map h.choose.on (ComputableInPolyTime.of_eq fun _ => rfl)
  guess := h.guess

/-- At each parameter `n`, the word-level experiment `gameOn` is the chosen-plaintext experiment
of the scheme with key generation `keyGen n` and encryption `encrypt n`, played by
`adversary.toTwoStage n`. The experiment never decrypts, so `decrypt` is arbitrary. -/
theorem gameOn_eq_cpaExperiment {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : List Bool → List Bool → Option Msg) (adversary : AdversaryOf Msg) (bit : Bool)
    (n : ℕ) :
    gameOn valid keyGen encrypt adversary bit n =
      (PKE.mk (keyGen n) (encrypt n) decrypt).cpaExperiment (valid n)
        (adversary.toTwoStage n) bit := by
  cases bit <;>
    simp only [gameOn, PKE.cpaExperiment, lrExperiment, AdversaryOf.toTwoStage, bind_map_left,
      MessagePair.select_false, MessagePair.select_true, Bool.false_eq_true, ↓reduceIte]

/-- The word-level advantage of `gameOn` at parameter `n` is the advantage between the two sides of
the typed chosen-plaintext experiment, so a bound on one fixed scheme transfers to `INDCPAOn`. -/
theorem advantage_gameOn_eq_cpaExperiment {Msg : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool) (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : List Bool → List Bool → Option Msg) (adversary : AdversaryOf Msg) (n : ℕ) :
    advantage (gameOn valid keyGen encrypt adversary) n =
      Experiment.advantage
        ((PKE.mk (keyGen n) (encrypt n) decrypt).cpaExperiment (valid n)
          (adversary.toTwoStage n) false)
        ((PKE.mk (keyGen n) (encrypt n) decrypt).cpaExperiment (valid n)
          (adversary.toTwoStage n) true) := by
  simp only [advantage, Experiment.advantage, gameOn_eq_cpaExperiment valid keyGen encrypt decrypt]

end Cslib.Crypto.Encryption
