/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Game

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
* `Cslib.Crypto.Encryption.AdversaryOf.IsPPT`, `Cslib.Crypto.Encryption.Adversary.IsPPT`,
  `Cslib.Crypto.Encryption.WordAdversary.IsPPT`: native uniform admissibility of both stages.
* `Cslib.Crypto.Encryption.gameOn`, `Cslib.Crypto.Encryption.game`: the key-generation and
  challenge-encryption experiment, with and without a challenge-pair admissibility predicate.
* `Cslib.Crypto.Encryption.INDCPAOn`, `Cslib.Crypto.Encryption.INDCPAOf`,
  `Cslib.Crypto.Encryption.INDCPA`, `Cslib.Crypto.Encryption.WordINDCPA`: negligible distinguishing
  advantage for every admissible adversary, fixed before the security parameter.
* `Cslib.Crypto.Encryption.AdversaryOf.restrict`: the adversary that plays `gameOn valid` inside
  the unrestricted `game`, by recording validity in its saved state.

## Main results

* `Cslib.Crypto.Encryption.eval_gameOn`, `Cslib.Crypto.Encryption.eval_game`: the experiments
  depend only on the public-key marginal.
* `Cslib.Crypto.Encryption.eval_game_restrict`: `game` on `adversary.restrict valid` has the same
  output distribution as `gameOn valid` on `adversary`.
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

/-- A chosen-message adversary over message space `Msg`. The saved word contains all data retained
between stages. -/
structure AdversaryOf (Msg : Type) where
  /-- Receive the public key, choose the two challenge messages, and save a state. -/
  choose : ℕ → List Bool → ProbComp ((Msg × Msg) × List Bool)
  /-- Receive the saved state and challenge ciphertext, then return a distinguishing bit. -/
  guess : ℕ → List Bool → List Bool → ProbComp Bool

/-- One finite-machine certificate for each whole stage over message encoding `encMsg`, including
the full saved-state cost. There is no parameter-dependent advice or separate algorithm for each
security parameter. -/
structure AdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : AdversaryOf Msg) : Prop where
  /-- Message selection is uniform strict PPT on the parameter and public key. -/
  choose : Probability.IsPPT (encPair (encPair encMsg encMsg) encBits) adversary.choose
  /-- Guessing is uniform strict PPT on the parameter, saved state, and challenge ciphertext. -/
  guess : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
    (fun p => adversary.guess p.1 p.2.1 p.2.2)

/-- A chosen-message adversary for single-bit messages (`Bool`). -/
abbrev Adversary : Type := AdversaryOf Bool

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
  if valid n keys.1 choice.1.1 choice.1.2 then
    let ciphertext ← encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
    adversary.guess n choice.2 ciphertext
  else
    return false

/-- The unrestricted chosen-message experiment: `gameOn` with every challenge pair admissible. -/
abbrev game {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  gameOn (fun _ _ _ _ => true) keyGen encrypt adversary bit n

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
        if valid n pk choice.1.1 choice.1.2 then
          let ciphertext ← ProbComp.eval (encrypt n pk (if bit then choice.1.2 else choice.1.1))
          ProbComp.eval (adversary.guess n choice.2 ciphertext)
        else
          pure false) := by
  simp only [gameOn, ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def,
    apply_ite ProbComp.eval, ProbComp.eval_pure, PMF.monad_pure_eq_pure]

/-- Only the public-key marginal of key generation is observed by the unrestricted experiment. -/
theorem eval_game {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (game keyGen encrypt adversary bit n) =
      (do
        let pk ← (ProbComp.eval (keyGen n)).map Prod.fst
        let choice ← ProbComp.eval (adversary.choose n pk)
        let ciphertext ← ProbComp.eval (encrypt n pk (if bit then choice.1.2 else choice.1.1))
        ProbComp.eval (adversary.guess n choice.2 ciphertext)) := by
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
    return (choice.1, valid n pk choice.1.1 choice.1.2 :: choice.2)
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
  simp only [game, gameOn, AdversaryOf.restrict, ↓reduceIte, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, apply_ite ProbComp.eval]
  congr 1; funext keys
  congr 1; funext choice
  cases valid n keys.1 choice.1.1 choice.1.2 <;>
    simp [PMF.bind_const]

end Cslib.Crypto.Encryption
