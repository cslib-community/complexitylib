/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.GameCoinTape

/-!
# Supported intermediates of the complete modular game replay

An exactly allocated tape supplies supported seeds to the actual target-key, modular-choice and
challenge-encryption evaluators. The choice law is derived from bounded component laws, preserving
the original selector, tags, swaps and zero-link fallback. No guess law is needed for these stages.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.modLeveledGameCoins_slice_lengths`: exact lengths of all four
  outer tape slices.
* `Cslib.Crypto.Homomorphic.Leveled.modLeveledGameCoins_intermediate_support`: the actual replay's
  key, choice and ciphertext belong to the corresponding original game supports in either world.
-/

public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability

/-- Exact allocation gives exact slice lengths, including zero budgets. This does not assert
supported replay behavior on shorter raw tapes. -/
theorem modLeveledGameCoins_slice_lengths
    (indexCoins depth capacity keyCoins encCoins chooseCoins guessCoins : ℕ)
    (tape : List Bool)
    (htape : tape.length = modLeveledGameCoinBudget indexCoins depth capacity keyCoins encCoins
      chooseCoins guessCoins) :
    let choiceBudget := modLeveledChooseCoinBudget indexCoins depth capacity keyCoins encCoins
      chooseCoins
    (tape.take keyCoins).length = keyCoins ∧
      ((tape.drop keyCoins).take choiceBudget).length = choiceBudget ∧
      (((tape.drop keyCoins).drop choiceBudget).take encCoins).length = encCoins ∧
      (((tape.drop keyCoins).drop choiceBudget).drop encCoins).length =
        leveledGuessCoinBudget depth capacity encCoins chooseCoins guessCoins := by
  dsimp only
  simp only [List.length_take, List.length_drop]
  unfold modLeveledGameCoinBudget at htape
  omega

/-- Every actual intermediate is supported on an exactly allocated tape. The component seed laws
only cover bounded keys/artifacts, and those bounds are derived from the preceding supports.
Both challenge bits use the same slices and preserve the original choice/challenge correlation. -/
theorem modLeveledGameCoins_intermediate_support (E : Scheme)
    (adversary : Encryption.Adversary)
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (coins depth capacity keyCoins encCoins chooseCoins guessCoins : ℕ → ℕ)
    (bit : Bool) (n pkBound : ℕ)
    (hkey : ProbComp.eval (E.keyGen n) =
      (BitString.uniformList (keyCoins n)).map (evaluateKey n))
    (hkeys : ∀ key ∈ (ProbComp.eval (E.keyGen n)).support,
      key.1.length ≤ pkBound ∧ key.2.length ≤ capacity n)
    (hencrypt : ∀ pk, pk.length ≤ pkBound → ∀ message,
      ProbComp.eval (E.encrypt n pk message) =
        (BitString.uniformList (encCoins n)).map (evaluateEncrypt (n, pk, message)) ∧
      ∀ ciphertext ∈ (ProbComp.eval (E.encrypt n pk message)).support,
        ciphertext.length ≤ encCoins n)
    (hchoose : ∀ artifact, (encPublicKey artifact).length ≤
        publicKeyLengthBound (depth n) (capacity n) pkBound (encCoins n) →
      ProbComp.eval (adversary.choose n (encPublicKey artifact)) =
        (BitString.uniformList (chooseCoins n)).map (evaluateChoose (n, encPublicKey artifact)) ∧
      ∀ chosen ∈ (ProbComp.eval (adversary.choose n (encPublicKey artifact))).support,
        chosen.2.length ≤ chooseCoins n)
    (tape : List Bool)
    (htape : tape.length = modLeveledGameCoinBudget (coins n) (depth n) (capacity n)
      (keyCoins n) (encCoins n) (chooseCoins n) (guessCoins n)) :
    let target := evaluateKey n (tape.take (keyCoins n))
    let remaining := tape.drop (keyCoins n)
    let choiceBudget := modLeveledChooseCoinBudget (coins n) (depth n) (capacity n)
      (keyCoins n) (encCoins n) (chooseCoins n)
    let choice := modLeveledChooseCoins evaluateKey
      (fun input seed => zeroLinkChooseCoins evaluateKey evaluateEncrypt evaluateChoose input.1
        (depth input.1) (capacity input.1) (keyCoins input.1) (encCoins input.1) input.2 seed)
      n (coins n) (depth n) (capacity n) (keyCoins n) target.1 (remaining.take choiceBudget)
    let rest := remaining.drop choiceBudget
    let message := if bit then choice.1.2 else choice.1.1
    let challenge := evaluateEncrypt (n, target.1, message) (rest.take (encCoins n))
    target ∈ (ProbComp.eval (E.keyGen n)).support ∧
      choice ∈ (ProbComp.eval
        ((modLeveledAdversary E coins depth capacity adversary).choose n target.1)).support ∧
      challenge ∈ (ProbComp.eval (E.encrypt n target.1 message)).support := by
  dsimp only
  obtain ⟨hkeyLength, hchoiceLength, hencLength, _⟩ :=
    modLeveledGameCoins_slice_lengths (coins n) (depth n) (capacity n) (keyCoins n)
      (encCoins n) (chooseCoins n) (guessCoins n) tape htape
  have htarget : evaluateKey n (tape.take (keyCoins n)) ∈
      (ProbComp.eval (E.keyGen n)).support := by
    rw [hkey]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨_, BitString.mem_support_uniformList_iff.mpr hkeyLength, rfl⟩
  refine ⟨htarget, ?_, ?_⟩
  · rw [eval_modLeveledAdversary_choose_eq_map_full_coins E adversary evaluateKey evaluateEncrypt
      evaluateChoose coins depth capacity keyCoins encCoins chooseCoins n pkBound
      hkey hkeys hencrypt hchoose _ htarget]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨_, BitString.mem_support_uniformList_iff.mpr hchoiceLength, rfl⟩
  · rw [(hencrypt _ (hkeys _ htarget).1 _).1]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨_, BitString.mem_support_uniformList_iff.mpr hencLength, rfl⟩

end Cslib.Crypto.Homomorphic.Leveled
