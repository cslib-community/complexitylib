/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Computational.Encryption.Basic
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# Replacing the public-key distribution in chosen-message security

One uniform distinguisher samples a hidden fair challenge bit after the adversary has chosen its
messages and saved state. It runs the actual encryption and guessing stages, then returns the
guess XOR the hidden bit. Comparing this same distinguisher on two public-key distributions
controls the change in their chosen-message gaps, with an exact factor of two.

## Main definitions

* `publicKeyGame`: the chosen-message experiment for a specified public-key law.
* `keyDistinguisher`: the single reduction, preserving the adversary's saved state.

## Main results

* `eval_game_eq_publicKeyGame`: the actual encryption game uses its public-key marginal.
* `isPPT_keyDistinguisher`: native strict PPT composition of the actual reduction.
* `probability_keyDistinguisher`: the exact affine identity for the signed chosen-message gap.
* `advantage_publicKeyGame_le`: quantitative public-key replacement with loss two.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2, for the chosen-message experiment and game-reduction method.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- Run the chosen-message experiment with a specified public-key distribution. The complete
state returned by message selection is passed unchanged to guessing. -/
noncomputable def publicKeyGame (keys : PMF (List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (security : ℕ) : Game := do
  let pk ← keys
  let choice ← ProbComp.eval (adversary.choose security pk)
  let ciphertext ← ProbComp.eval
    (encrypt security pk (if bit then choice.1.2 else choice.1.1))
  ProbComp.eval (adversary.guess security choice.2 ciphertext)

/-- An honest key generator contributes precisely its public-key marginal. -/
theorem eval_game_eq_publicKeyGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (security : ℕ) :
    ProbComp.eval (game keyGen encrypt adversary bit security) =
      publicKeyGame ((ProbComp.eval (keyGen security)).map Prod.fst)
        encrypt adversary bit security := eval_game keyGen encrypt adversary bit security

/-- A single uniform distinguisher with its own hidden fair challenge bit. The adversary sees
only the supplied public key and the actual challenge ciphertext, with its saved state retained. -/
noncomputable def keyDistinguisher
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) : Distinguisher := fun security pk => do
  let choice ← adversary.choose security pk
  let bit ← ProbComp.uniform Bool
  let ciphertext ← encrypt security pk (if bit then choice.1.2 else choice.1.1)
  let guess ← adversary.guess security choice.2 ciphertext
  return guess ^^ bit

/-- The reduction is one uniform strict PPT program when encryption and both adversary stages
are certified on their complete inputs. -/
theorem isPPT_keyDistinguisher
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)} {adversary : Adversary}
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun input => encrypt input.1 input.2.1 input.2.2))
    (hadversary : adversary.IsPPT) : IsPPT encBool (keyDistinguisher encrypt adversary) := by
  let choiceEncoding := encPair (encPair encBool encBool) encBits
  let baseEncoding := encPair encUnary encBits
  let coinEncoding := encPair (encPair baseEncoding choiceEncoding) encBool
  have hchoose := hadversary.choose.on
  have hcoin := isPPTOn_uniform_bool (encPair baseEncoding choiceEncoding)
  have hencryptArg : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × ((Bool × Bool) × List Bool)) × Bool =>
        (p.1.1.1, p.1.1.2, if p.2 then p.1.2.1.2 else p.1.2.1.1))
      coinEncoding (encPair encUnary (encPair encBits encBool)) := by
    dsimp only [coinEncoding, baseEncoding, choiceEncoding]
    fun_prop
  have hcipher := hencrypt.preprocess hencryptArg
  have hguessArg : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × ((Bool × Bool) × List Bool)) × Bool) × List Bool =>
        (p.1.1.1.1, p.1.1.2.2, p.2)) (encPair coinEncoding encBits)
      (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [coinEncoding, baseEncoding, choiceEncoding]
    fun_prop
  have hguess := hadversary.guess.preprocess hguessArg
  have hxor : ComputableInPolyTime
      (fun p : (((((ℕ × List Bool) × ((Bool × Bool) × List Bool)) × Bool) × List Bool) × Bool) =>
        p.2 ^^ p.1.1.2) (encPair (encPair coinEncoding encBits) encBool) encBool := by
    have hx := ComputableInPolyTime.of_finite
      (encIn := encPair encBool encBool) (encOut := encBool) (fun p : Bool × Bool => p.1 ^^ p.2)
    have harg : ComputableInPolyTime
        (fun p : (((((ℕ × List Bool) × ((Bool × Bool) × List Bool)) × Bool) × List Bool) × Bool) =>
          (p.2, p.1.1.2)) (encPair (encPair coinEncoding encBits) encBool)
        (encPair encBool encBool) := by
      dsimp only [coinEncoding, baseEncoding, choiceEncoding]
      fun_prop
    simpa only [Function.comp_def] using hx.comp harg
  have hlast := hguess.map_with
    (f := fun p guess => guess ^^ p.1.2) hxor
  have hlast' : IsPPTOn (encPair coinEncoding encBits) encBool
      (fun p : (((ℕ × List Bool) × ((Bool × Bool) × List Bool)) × Bool) × List Bool => do
        let guess ← adversary.guess p.1.1.1.1 p.1.1.2.2 p.2
        pure (guess ^^ p.1.2)) := by
    simpa only [bind_pure_comp] using hlast
  have hbody := hcipher.bind_with
    (second := fun p ciphertext => do
      let guess ← adversary.guess p.1.1.1 p.1.2.2 ciphertext
      pure (guess ^^ p.2)) hlast'
  have hbits := hcoin.bind_with
    (second := fun p bit => do
      let ciphertext ← encrypt p.1.1 p.1.2 (if bit then p.2.1.2 else p.2.1.1)
      let guess ← adversary.guess p.1.1 p.2.2 ciphertext
      pure (guess ^^ bit)) hbody
  simpa only [IsPPT, keyDistinguisher, choiceEncoding, baseEncoding, coinEncoding,
    Function.comp_def, bind_pure_comp] using
    hchoose.bind_with (second := fun p choice => do
      let bit ← ProbComp.uniform Bool
      let ciphertext ← encrypt p.1 p.2 (if bit then choice.1.2 else choice.1.1)
      let guess ← adversary.guess p.1 choice.2 ciphertext
      pure (guess ^^ bit)) hbits

/-- The hidden-bit experiment averages the two chosen-message games, complementing the second.
No finiteness or independence assumption is imposed on the saved state. -/
theorem distinguishingGame_keyDistinguisher (keys : PMF (List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (security : ℕ) :
    distinguishingGame keys (keyDistinguisher encrypt adversary security) = (do
      let bit ← PMF.uniformOfFintype Bool
      (publicKeyGame keys encrypt adversary bit security).map (fun guess => guess ^^ bit)) := by
  simp only [distinguishingGame, keyDistinguisher, publicKeyGame, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind]
  rw [PMF.bind_comm]
  congr 1
  funext pk
  rw [PMF.bind_comm]
  rfl

/-- Acceptance is one half plus half the signed chosen-message gap. -/
theorem probability_keyDistinguisher (keys : PMF (List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (security : ℕ) :
    (Game.succProbability
      (distinguishingGame keys (keyDistinguisher encrypt adversary security)) : ℝ) =
      (1 + (Game.succProbability (publicKeyGame keys encrypt adversary false security) : ℝ) -
        Game.succProbability (publicKeyGame keys encrypt adversary true security)) / 2 := by
  rw [distinguishingGame_keyDistinguisher]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    PMF.monad_bind_eq_bind, PMF.bind_apply_toReal, Fintype.sum_bool,
    PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num [PMF.toReal_false_eq_one_sub]
  ring

/-- Replacing the public-key law costs at most twice the advantage of one uniform hidden-bit
distinguisher, plus the chosen-message advantage under the replacement law. -/
theorem advantage_publicKeyGame_le (real ideal : PMF (List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (security : ℕ) :
    Game.advantage (publicKeyGame real encrypt adversary false security)
      (publicKeyGame real encrypt adversary true security) ≤
        2 * Game.advantage
          (distinguishingGame real (keyDistinguisher encrypt adversary security))
          (distinguishingGame ideal (keyDistinguisher encrypt adversary security)) +
            Game.advantage (publicKeyGame ideal encrypt adversary false security)
              (publicKeyGame ideal encrypt adversary true security) := by
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Game.coe_advantage,
    probability_keyDistinguisher]
  have h := abs_sub_le
    ((Game.succProbability (publicKeyGame real encrypt adversary false security) : ℝ) -
      Game.succProbability (publicKeyGame real encrypt adversary true security))
    ((Game.succProbability (publicKeyGame ideal encrypt adversary false security) : ℝ) -
      Game.succProbability (publicKeyGame ideal encrypt adversary true security)) 0
  have hscale (a b c d : ℝ) :
      2 * |(1 + a - b) / 2 - (1 + c - d) / 2| = |(a - b) - (c - d)| := by
    calc
      _ = |2 * ((1 + a - b) / 2 - (1 + c - d) / 2)| := by rw [abs_mul]; norm_num
      _ = _ := by congr 1; ring
  simpa only [hscale, sub_zero] using h

end Cslib.Crypto.Encryption
