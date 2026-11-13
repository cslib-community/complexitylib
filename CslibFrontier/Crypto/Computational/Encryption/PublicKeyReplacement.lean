/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Encoding
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT

/-!
# Replacing the public-key distribution in chosen-message security

One uniform distinguisher samples a hidden fair challenge bit after the adversary has chosen its
messages and saved state. It runs the actual encryption and guessing stages, then returns the
guess XOR the hidden bit. Comparing this same distinguisher on two public-key distributions
controls the change in their chosen-message gaps, with an exact factor of two. The experiment and
the distinguisher take the challenge-pair admissibility predicate `valid` of `gameOn`; an
inadmissible pair outputs `false` on both sides, so the distinguisher returns the hidden bit.

## Main definitions

* `publicKeyGameOn`, `publicKeyGame`: the chosen-message experiment for a specified public-key
  law, with and without an admissibility predicate.
* `keyDistinguisherOn`, `keyDistinguisher`: the single reduction, preserving the adversary's saved
  state.

## Main results

* `eval_gameOn_eq_publicKeyGameOn`, `eval_game_eq_publicKeyGame`: the actual encryption game uses
  its public-key marginal.
* `isPPT_keyDistinguisherOn`, `isPPT_keyDistinguisher`: native strict PPT composition of the actual
  reduction.
* `probability_keyDistinguisherOn`: the exact affine identity for the signed chosen-message gap.
* `advantage_publicKeyGameOn_le`, `advantage_publicKeyGame_le`: quantitative public-key replacement
  with loss two, an instance of `Game.advantage_le_two_mul_uniform_bool_xor`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2, for the chosen-message experiment and game-reduction method.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

variable {Msg : Type}

/-- Run the chosen-message experiment `gameOn valid` with a specified public-key distribution. The
complete state returned by message selection is passed unchanged to guessing, and an inadmissible
challenge pair outputs `false`. -/
noncomputable def publicKeyGameOn (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keys : PMF (List Bool)) (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (security : ℕ) : Game := do
  let pk ← keys
  let choice ← ProbComp.eval (adversary.choose security pk)
  if valid security pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let ciphertext ← ProbComp.eval
      (encrypt security pk (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice))
    ProbComp.eval (adversary.guess security (ChoiceOut.state choice) ciphertext)
  else
    pure false

/-- The unrestricted experiment with a specified public-key distribution: `publicKeyGameOn` with
every challenge pair admissible. -/
noncomputable abbrev publicKeyGame (keys : PMF (List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (security : ℕ) : Game :=
  publicKeyGameOn (fun _ _ _ _ => true) keys encrypt adversary bit security

/-- An honest key generator contributes precisely its public-key marginal to `gameOn`. -/
theorem eval_gameOn_eq_publicKeyGameOn (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (security : ℕ) :
    ProbComp.eval (gameOn valid keyGen encrypt adversary bit security) =
      publicKeyGameOn valid ((ProbComp.eval (keyGen security)).map Prod.fst)
        encrypt adversary bit security :=
  eval_gameOn valid keyGen encrypt adversary bit security

/-- An honest key generator contributes precisely its public-key marginal to `game`. -/
theorem eval_game_eq_publicKeyGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (security : ℕ) :
    ProbComp.eval (game keyGen encrypt adversary bit security) =
      publicKeyGame ((ProbComp.eval (keyGen security)).map Prod.fst)
        encrypt adversary bit security :=
  eval_gameOn_eq_publicKeyGameOn _ keyGen encrypt adversary bit security

/-- A single uniform distinguisher with its own hidden fair challenge bit. The adversary sees
only the supplied public key and the actual challenge ciphertext, with its saved state retained.
On an inadmissible challenge pair both experiments output `false`, so the distinguisher returns
`false ^^ bit`. -/
noncomputable def keyDistinguisherOn (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) : Distinguisher := fun security pk => do
  let choice ← adversary.choose security pk
  let bit ← ProbComp.uniform Bool
  if valid security pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) then
    let ciphertext ← encrypt security pk
      (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
    let guess ← adversary.guess security (ChoiceOut.state choice) ciphertext
    return guess ^^ bit
  else
    return false ^^ bit

/-- The unrestricted reduction: `keyDistinguisherOn` with every challenge pair admissible. -/
noncomputable abbrev keyDistinguisher (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) : Distinguisher :=
  keyDistinguisherOn (fun _ _ _ _ => true) encrypt adversary

/-- The reduction is one uniform strict PPT program when the admissibility predicate is
computable in polynomial time and encryption and both adversary stages are certified on their
complete inputs. -/
theorem isPPT_keyDistinguisherOn {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)} {adversary : AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨security, pk, msg⟩ => encrypt security pk msg))
    (hadversary : adversary.IsPPT encMsg) :
    IsPPT encBool (keyDistinguisherOn valid encrypt adversary) := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  unfold Probability.IsPPT keyDistinguisherOn
  ppt

/-- The unrestricted reduction is one uniform strict PPT program when encryption and both
adversary stages are certified on their complete inputs. -/
theorem isPPT_keyDistinguisher {encMsg : Msg ↪ List Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)} {adversary : AdversaryOf Msg}
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨security, pk, msg⟩ => encrypt security pk msg))
    (hadversary : adversary.IsPPT encMsg) :
    IsPPT encBool (keyDistinguisher encrypt adversary) :=
  isPPT_keyDistinguisherOn (ComputableInPolyTime.const true) hencrypt hadversary

/-- The hidden-bit experiment averages the two chosen-message games, complementing the second.
No finiteness or independence assumption is imposed on the saved state. -/
theorem distinguishingGame_keyDistinguisherOn (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keys : PMF (List Bool)) (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (security : ℕ) :
    distinguishingGame keys (keyDistinguisherOn valid encrypt adversary security) = (do
      let bit ← PMF.uniformOfFintype Bool
      (publicKeyGameOn valid keys encrypt adversary bit security).map
        (fun guess => guess ^^ bit)) := by
  simp only [distinguishingGame_eq_bind, keyDistinguisherOn, publicKeyGameOn, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind,
    apply_ite ProbComp.eval]
  pmf_swap with bit pk choice
  cases valid security pk (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, PMF.monad_pure_eq_pure, PMF.pure_map]
  | true =>
    simp only [↓reduceIte, PMF.map_bind]; rfl

/-- Acceptance is one half plus half the signed chosen-message gap. -/
theorem probability_keyDistinguisherOn (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keys : PMF (List Bool)) (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (security : ℕ) :
    (Game.succProbability
      (distinguishingGame keys (keyDistinguisherOn valid encrypt adversary security)) : ℝ) =
      (1 + (Game.succProbability
          (publicKeyGameOn valid keys encrypt adversary false security) : ℝ) -
        Game.succProbability (publicKeyGameOn valid keys encrypt adversary true security)) / 2 := by
  rw [distinguishingGame_keyDistinguisherOn]
  exact Game.succProbability_uniform_bool_xor _

/-- Replacing the public-key law costs at most twice the advantage of one uniform hidden-bit
distinguisher, plus the chosen-message advantage under the replacement law. -/
theorem advantage_publicKeyGameOn_le (valid : ℕ → List Bool → Msg → Msg → Bool)
    (real ideal : PMF (List Bool)) (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (security : ℕ) :
    Game.advantage (publicKeyGameOn valid real encrypt adversary false security)
      (publicKeyGameOn valid real encrypt adversary true security) ≤
        2 * Game.advantage
          (distinguishingGame real (keyDistinguisherOn valid encrypt adversary security))
          (distinguishingGame ideal (keyDistinguisherOn valid encrypt adversary security)) +
            Game.advantage (publicKeyGameOn valid ideal encrypt adversary false security)
              (publicKeyGameOn valid ideal encrypt adversary true security) := by
  rw [distinguishingGame_keyDistinguisherOn, distinguishingGame_keyDistinguisherOn]
  exact Game.advantage_le_two_mul_uniform_bool_xor
    (publicKeyGameOn valid real encrypt adversary · security)
    (publicKeyGameOn valid ideal encrypt adversary · security)

/-- Public-key replacement for the unrestricted experiment. -/
theorem advantage_publicKeyGame_le (real ideal : PMF (List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (security : ℕ) :
    Game.advantage (publicKeyGame real encrypt adversary false security)
      (publicKeyGame real encrypt adversary true security) ≤
        2 * Game.advantage
          (distinguishingGame real (keyDistinguisher encrypt adversary security))
          (distinguishingGame ideal (keyDistinguisher encrypt adversary security)) +
            Game.advantage (publicKeyGame ideal encrypt adversary false security)
              (publicKeyGame ideal encrypt adversary true security) :=
  advantage_publicKeyGameOn_le _ real ideal encrypt adversary security

end Cslib.Crypto.Encryption
