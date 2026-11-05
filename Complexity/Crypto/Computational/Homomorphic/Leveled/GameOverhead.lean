/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.GameCoinTape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native complete-game replay from strict PPT

The original modular leveled reduction has a complete-game saved-tape realization in both
challenge worlds. Strict-PPT components supply the required bounded-input laws; supports are
derived inside the original game. This is an execution and coin-budget theorem, not Gentry's
literal security-loss parameter mapping or multiplicative machine-runtime comparison.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.exists_modLeveledGame_coin_evaluator`: complete native
  replay and an explicit polynomial allocation from the canonical overhead witnesses.
-/

public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability Turing.MultiTapeTM

/-- Native strict-PPT components realize the complete existing modular reduction game from
the stated polynomial allocation. Both challenge worlds use one evaluator family and budget.
There is no supplied key, saved-state or ciphertext support premise: the game itself supplies
all three. Fixed supported secret width and the depth convention `2 * budget` are inherited
from the canonical leveled overhead theorem. -/
theorem exists_modLeveledGame_coin_evaluator {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)
    {width coins budget capacity : ℕ → ℕ}
    (hwidth : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support → keys.2.length = width n)
    (hcapacity_le : ∀ n, width n ≤ capacity n)
    (hcoins : ComputableInPolyTime coins encUnary encUnary)
    (hbudget : ComputableInPolyTime budget encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) :
    ∃ (keyCoins encCoins chooseCoins guessCoins : ℕ → ℕ)
      (evaluate : Bool → ℕ → List Bool → Bool),
      ComputableInPolyTime keyCoins encUnary encUnary ∧
      ComputableInPolyTime encCoins encUnary encUnary ∧
      ComputableInPolyTime chooseCoins encUnary encUnary ∧
      ComputableInPolyTime guessCoins encUnary encUnary ∧
      (∀ bit, ComputableInPolyTime (fun (n, tape) => evaluate bit n tape)
        (encPair encUnary encBits) encBool) ∧
      PolynomiallyBounded (fun n => modLeveledGameCoinBudget (coins n) (2 * budget n)
        (capacity n) (keyCoins n) (encCoins n) (chooseCoins n) (guessCoins n)) ∧
      ∀ bit n, ProbComp.eval (Encryption.game E.keyGen E.encrypt
        (modLeveledAdversary E coins (fun n => 2 * budget n) capacity adversary) bit n) =
        (BitString.uniformList (modLeveledGameCoinBudget (coins n) (2 * budget n)
          (capacity n) (keyCoins n) (encCoins n) (chooseCoins n) (guessCoins n))).map
            (evaluate bit n) := by
  obtain ⟨c_kg, d_kg, c_enc, d_enc, c_ch, d_ch, c_gu, d_gu,
    evalKey, evalEncrypt, evalChoose, evalGuess, hevalKey, hevalEncrypt, hevalChoose, hevalGuess,
    hkey, hkeys, henc, _, hchoose, hguess, _, _, _, _⟩ :=
      exists_leveledAdversary_overhead hkeyGen hencrypt hadversary hwidth hcapacity_le
        hbudget hcapacity
  let keyCoins := fun n => c_kg * (n + 1) ^ d_kg
  let encCoins := fun n => c_enc * (2 * n + 2 * keyCoins n + 5) ^ d_enc
  let pubLen := fun n =>
    publicKeyLengthBound (2 * budget n) (capacity n) (keyCoins n) (encCoins n)
  let chooseCoins := fun n => c_ch * (2 * n + pubLen n + 2) ^ d_ch
  let guessCoins := fun n => c_gu * (2 * n + 2 * chooseCoins n + encCoins n + 4) ^ d_gu
  have hkeyCoins : ComputableInPolyTime keyCoins encUnary encUnary := by
    dsimp only [keyCoins]
    fun_prop
  have hencCoins : ComputableInPolyTime encCoins encUnary encUnary := by
    dsimp only [encCoins]
    fun_prop
  have hchooseCoins : ComputableInPolyTime chooseCoins encUnary encUnary := by
    dsimp only [chooseCoins, pubLen, publicKeyLengthBound]
    fun_prop
  have hguessCoins : ComputableInPolyTime guessCoins encUnary encUnary := by
    dsimp only [guessCoins]
    fun_prop
  refine ⟨keyCoins, encCoins, chooseCoins, guessCoins,
    modLeveledGameCoins evalKey evalEncrypt evalChoose evalGuess coins (fun n => 2 * budget n)
      capacity keyCoins encCoins chooseCoins guessCoins,
    hkeyCoins, hencCoins, hchooseCoins, hguessCoins, ?_, ?_, ?_⟩
  · intro bit
    apply computableInPolyTime_modLeveledGameCoins hevalKey hevalEncrypt hevalChoose hevalGuess
      hcoins (by fun_prop) hcapacity hkeyCoins hencCoins hchooseCoins hguessCoins bit
  · have htotal : ComputableInPolyTime (fun n => modLeveledGameCoinBudget (coins n)
        (2 * budget n) (capacity n) (keyCoins n) (encCoins n) (chooseCoins n) (guessCoins n))
        encUnary encUnary := by
      unfold modLeveledGameCoinBudget modLeveledChooseCoinBudget leveledGuessCoinBudget
      fun_prop
    exact htotal.polynomiallyBounded
  · intro bit n
    exact eval_game_modLeveledAdversary_eq_map_coins E adversary evalKey evalEncrypt evalChoose
      evalGuess coins (fun n => 2 * budget n) capacity keyCoins encCoins chooseCoins guessCoins
      bit n (keyCoins n) (hkey n) (hkeys n)
      (fun pk hpk message => henc n pk message hpk)
      (fun artifact hbound => hchoose n (encPublicKey artifact) hbound) (hguess n)

end Cslib.Crypto.Homomorphic.Leveled
