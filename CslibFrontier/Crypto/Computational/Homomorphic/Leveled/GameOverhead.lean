/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.GameCoinTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native complete-game replay from strict PPT

The original modular leveled reduction has a complete-game saved-tape realization in both
challenge worlds. Strict-PPT components supply the required bounded-input laws; supports are
derived inside the original game. This is an execution and coin-budget theorem, not Gentry's
literal security-loss parameter mapping or multiplicative machine-runtime comparison.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.exists_modLeveledGame_coin_evaluator`: complete native
  replay and an explicit polynomial allocation from `exists_overheadRealization`.
-/

public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability Turing.MultiTapeTM

/-- Native strict-PPT components realize the complete existing modular reduction game from
the stated polynomial allocation. Both challenge worlds use one evaluator family and budget.
There is no supplied key, saved-state or ciphertext support premise: the game itself supplies
all three. Supported secrets are bounded by `capacity`, and the depth convention `2 * budget`
is that of `modLeveledAdversary`'s leveled scheme. The component budgets are those of
`exists_overheadRealization`. -/
theorem exists_modLeveledGame_coin_evaluator {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)
    {coins budget capacity : ℕ → ℕ}
    (hsecret : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support →
      keys.2.length ≤ capacity n)
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
  obtain ⟨B, hB⟩ := exists_overheadRealization hkeyGen hencrypt hadversary
  obtain ⟨R⟩ := hB (fun n => 2 * budget n) capacity
  have hdepth : ComputableInPolyTime (fun n => 2 * budget n) encUnary encUnary := by fun_prop
  have hkeyCoins := B.computableInPolyTime_keyCoins
  have hencCoins := B.computableInPolyTime_encCoins
  have hchooseCoins := B.computableInPolyTime_chooseCoins hdepth hcapacity
  have hguessCoins := B.computableInPolyTime_guessCoins hdepth hcapacity
  refine ⟨B.keyCoins, B.encCoins, B.chooseCoins (fun n => 2 * budget n) capacity,
    B.guessCoins (fun n => 2 * budget n) capacity,
    modLeveledGameCoins R.keyGen.evaluate R.encrypt.evaluate R.choose.evaluate R.guess.evaluate
      coins (fun n => 2 * budget n) capacity B.keyCoins B.encCoins
      (B.chooseCoins (fun n => 2 * budget n) capacity)
      (B.guessCoins (fun n => 2 * budget n) capacity),
    hkeyCoins, hencCoins, hchooseCoins, hguessCoins, fun bit => ?_, ?_, fun bit n => ?_⟩
  · exact computableInPolyTime_modLeveledGameCoins R.keyGen.efficient R.encrypt.efficient
      R.choose.efficient R.guess.efficient hcoins hdepth hcapacity hkeyCoins hencCoins
      hchooseCoins hguessCoins bit
  · have htotal : ComputableInPolyTime (fun n => modLeveledGameCoinBudget (coins n)
        (2 * budget n) (capacity n) (B.keyCoins n) (B.encCoins n)
        (B.chooseCoins (fun n => 2 * budget n) capacity n)
        (B.guessCoins (fun n => 2 * budget n) capacity n)) encUnary encUnary := by
      unfold modLeveledGameCoinBudget modLeveledChooseCoinBudget leveledGuessCoinBudget
      fun_prop
    exact htotal.polynomiallyBounded
  · exact eval_game_modLeveledAdversary_eq_map_coins E adversary R.keyGen.evaluate
      R.encrypt.evaluate R.choose.evaluate R.guess.evaluate coins (fun n => 2 * budget n)
      capacity B.keyCoins B.encCoins (B.chooseCoins (fun n => 2 * budget n) capacity)
      (B.guessCoins (fun n => 2 * budget n) capacity) bit n (B.keyCoins n)
      (R.keyGen.eval_eq n trivial) (R.length_keys_le hsecret n)
      (fun pk hpk message => R.encrypt.eval_eq_and_length_le (a := (n, pk, message)) hpk)
      (fun artifact hpk => ⟨R.choose.eval_eq (n, encPublicKey artifact) hpk,
        fun _ hchoice => R.length_state_le hpk hchoice⟩)
      (fun state ct hstate hct => R.guess.eval_eq (n, state, ct) ⟨hstate, hct⟩)

end Cslib.Crypto.Homomorphic.Leveled
