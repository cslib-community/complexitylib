/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Bind
import Complexity.Crypto.Computational.Homomorphic.Leveled.GuessCoinTape
import Complexity.Crypto.Computational.Homomorphic.Leveled.CoinTape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Concrete link guessing tapes

Randomized bit encryption, adaptive choice, and guessing use separate one-bit seeds. The
fixture instantiates the actual supported-choice theorem without any security assumption.
Explicit replays check both boundary cuts, padding, repeated keys, and the supplied challenge.
-/

namespace ComplexityTests.Crypto.LeveledGuessCoinTape

open Cslib Cslib.Crypto Cslib.Crypto.Homomorphic Cslib.Probability Turing.MultiTapeTM

private def key : List Bool × List Bool := ([false], [true, false])

private def evaluateEncrypt (input : ℕ × List Bool × Bool) (tape : List Bool) : List Bool :=
  input.2.2 :: tape

private def evaluateChoose (_ : ℕ × List Bool) (tape : List Bool) : (Bool × Bool) × List Bool :=
  ((tape.headD false, false), tape)

private def evaluateGuess (input : ℕ × List Bool × List Bool) (tape : List Bool) : Bool :=
  input.2.1.headD false ^^ input.2.2.getD 2 false ^^ tape.headD false

private noncomputable def fixture : Scheme where
  keyGen _ := pure key
  encrypt n pk bit := evaluateEncrypt (n, pk, bit) <$> BitString.sampleList 1
  decrypt _ _ ciphertext := ciphertext.headD false
  evaluate _ _ _ _ := pure []
  permitted _ _ := False

private noncomputable def adversary : Encryption.Adversary where
  choose n pk := evaluateChoose (n, pk) <$> BitString.sampleList 1
  guess n state ciphertext := evaluateGuess (n, state, ciphertext) <$> BitString.sampleList 1

private theorem encrypt_law (n : ℕ) (pk : List Bool) (bit : Bool) :
    ProbComp.eval (fixture.encrypt n pk bit) =
      (BitString.uniformList 1).map (evaluateEncrypt (n, pk, bit)) := by
  simp [fixture, ProbComp.eval_map, BitString.eval_sampleList]

private theorem choose_law (n : ℕ) (artifact) :
    ProbComp.eval (adversary.choose n (Leveled.encPublicKey artifact)) =
      (BitString.uniformList 1).map (evaluateChoose (n, Leveled.encPublicKey artifact)) := by
  simp [adversary, ProbComp.eval_map, BitString.eval_sampleList]

private theorem guess_law (n : ℕ) (state ciphertext : List Bool) :
    ProbComp.eval (adversary.guess n state (false :: ciphertext)) =
      (BitString.uniformList 1).map (evaluateGuess (n, state, false :: ciphertext)) := by
  simp [adversary, ProbComp.eval_map, BitString.eval_sampleList]

-- Repeated plaintexts at the same key consume different seeds.
example : Scheme.encryptBitsCoins evaluateEncrypt 0 1 [] [false, false] [false, true] =
    [[false, false], [false, true]] := by decide

-- The first cut retains the whole supplied challenge as the first middle ciphertext.
example : Scheme.spliceEncryptedKeyLinkCoins evaluateEncrypt 0 1 2 [key] key
    ([false], [false, false]) [] 0 [true, true, true] [false, true, false] =
      [[[true, false], [false, true]], [[true, true, true], [false, false]]] := by decide

-- The last cut puts the challenge after the encrypted zero prefix.
example : Scheme.spliceEncryptedKeyLinkCoins evaluateEncrypt 0 1 2 [key] key
    ([false], [false, false]) [] 1 [true, true, true] [false, true, false] =
      [[[true, false], [false, true]], [[false, false], [true, true, true]]] := by decide

-- A later link encrypts the synthetic target secret as zeros, with fresh row seeds.
example : Scheme.spliceEncryptedKeyLinkCoins evaluateEncrypt 0 1 2 [] key
    ([true], [false, false]) [key] 0 [true, true, true] [false, true, false] =
      [[[true, true, true], [false, false]], [[false, true], [false, false]]] := by decide

-- Padding in the first row is ignored; it does not become the middle link's nonce.
example : Scheme.spliceEncryptedKeyLinkCoins evaluateEncrypt 0 1 2 [([false], [true])] key
    ([false], [false, false]) [] 1 [true, true, true] [false, true, false] =
      [[[true, false]], [[false, false], [true, true, true]]] := by decide

-- An invalid cut cannot satisfy the small-budget law's premise.
example : ¬ 2 < key.2.length := by decide

example (tape challenge : List Bool) : Scheme.guessLinkCoins evaluateEncrypt
    (Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess false 1 1)
    0 1 0 Scheme.rejectLinkState challenge tape = false := by simp

-- The three game seeds independently influence the result through saved state, encryption,
-- and guessing. The ciphertext tag makes the encryption nonce the third received bit.
example : ([ [false, false, false], [true, false, false], [false, true, false],
    [false, false, true] ].map (Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt
      evaluateGuess false 1 1 (0, [key.1], []))) = [false, true, true, true] := by decide

private def selected : (Bool × Bool) × List Bool :=
  Scheme.chooseModLinkCoins (fun _ _ => key) 0 1 0 2 2 [] [false, false]

-- This particular context actually occurs in the original modular choice distribution.
private theorem selected_supported : selected ∈ (ProbComp.eval
    ((fixture.modLinkAdversary (fun _ => 1) (fun _ => 2) (fun _ => 2)
      (Leveled.publicKeyGame fixture adversary false)).choose 0 [])).support := by
  have hkey : ProbComp.eval (fixture.keyGen 0) =
      (BitString.uniformList 0).map (fun _ => key) := by
    simp [fixture, ProbComp.eval_pure, PMF.map]
  rw [fixture.eval_modLinkAdversary_choose_eq_map_coins (fun _ _ => key)
    (fun _ => 1) (fun _ => 2) (fun _ => 2) _ 0 0 [] hkey]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨[false, false], BitString.mem_support_uniformList_iff.mpr rfl, rfl⟩

example : selected.2 = Scheme.activeLinkState [key] key [] [] 0 := by decide

-- All hypotheses of the complete six-bit budget theorem are instantiated by this fixture.
example (challenge : List Bool) : ProbComp.eval
    ((fixture.modLinkAdversary (fun _ => 1) (fun _ => 2) (fun _ => 2)
      (Leveled.publicKeyGame fixture adversary false)).guess 0 selected.2 challenge) =
      (BitString.uniformList 6).map (Scheme.guessLinkCoins evaluateEncrypt
        (Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess false 1 1)
        0 1 2 selected.2 challenge) := by
  apply fixture.eval_modLinkAdversary_guess_eq_map_coins adversary
    (fun _ => 1) (fun _ => 2) (fun _ => 2) evaluateChoose evaluateEncrypt evaluateGuess
      false 0 1 1 1 [] challenge selected selected_supported
  · intro generated hgenerated
    simp only [fixture, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hgenerated
    subst generated
    decide
  · exact choose_law 0
  · exact encrypt_law 0
  · exact guess_law 0

-- The combined concrete evaluator is uniformly native polynomial time in n, state,
-- challenge and tape. All three probabilistic components have explicit native replays.
example : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool × List Bool =>
    Scheme.guessLinkCoins evaluateEncrypt
      (fun input tape => Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess
        false 1 1 input tape) p.1 1 2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool := by
  apply Scheme.computableInPolyTime_modLinkGuessCoins
    (chooseCoins := fun _ => 1) (encCoins := fun _ => 1) (capacity := fun _ => 2)
  · unfold evaluateChoose
    fun_prop
  · unfold evaluateEncrypt
    fun_prop
  · unfold evaluateGuess
    fun_prop
  all_goals fun_prop

end ComplexityTests.Crypto.LeveledGuessCoinTape
