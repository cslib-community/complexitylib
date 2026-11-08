/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.ModularCoinTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.PMF.Bind

/-!
# Complete modular leveled game replay

The replay follows the existing unrestricted bit-encryption game: generate its target key,
choose messages through the original modular reduction, encrypt the selected message, and run
the tagged guess. All support restrictions are discharged inside that original game.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.modLeveledChooseCoinBudget`: three modular selector blocks
  and a common padded payload for the original branches.
* `Cslib.Crypto.Homomorphic.Leveled.modLeveledGameCoinBudget`: the complete allocated game tape.
* `Cslib.Crypto.Homomorphic.Leveled.modLeveledGameCoins`: deterministic replay of that game.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.eval_game_modLeveledAdversary_eq_map_coins`: exact original
  game distribution in either challenge world, deriving supports internally.
* `Cslib.Crypto.Homomorphic.Leveled.computableInPolyTime_modLeveledGameCoins`: native complete
  replay in the unary parameter and full supplied tape.
-/

public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability Turing.MultiTapeTM

/-- Three modular selector blocks, generated keys, padded zero-link encryptions and one
adversary choice. This differs from the two-bit selector and logarithmic dyadic allocation. -/
@[expose] def modLeveledChooseCoinBudget
    (indexCoins depth capacity keyCoins encCoins chooseCoins : ℕ) : ℕ :=
  3 * indexCoins + (depth * keyCoins + (depth * capacity * encCoins + chooseCoins))

/-- The actual base-game key generation and challenge encryption surround the complete
modular adversary. These are allocated padded tapes, not a claim that every branch uses all bits. -/
@[expose] def modLeveledGameCoinBudget
    (indexCoins depth capacity keyCoins encCoins chooseCoins guessCoins : ℕ) : ℕ :=
  keyCoins + (modLeveledChooseCoinBudget indexCoins depth capacity keyCoins encCoins chooseCoins +
    (encCoins + leveledGuessCoinBudget depth capacity encCoins chooseCoins guessCoins))

/-- Replay the existing complete modular base IND-CPA game from disjoint blocks, preserving
the selected challenge message and the actual tagged saved state. Both challenge worlds use
the same layout. -/
@[expose] def modLeveledGameCoins
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool)
    (coins depth capacity keyCoins encCoins chooseCoins guessCoins : ℕ → ℕ)
    (bit : Bool) (n : ℕ) (tape : List Bool) : Bool :=
  let target := evaluateKey n (tape.take (keyCoins n))
  let remaining := tape.drop (keyCoins n)
  let choiceBudget := modLeveledChooseCoinBudget (coins n) (depth n) (capacity n)
    (keyCoins n) (encCoins n) (chooseCoins n)
  let choice := modLeveledChooseCoins evaluateKey
    (fun input seed => zeroLinkChooseCoins evaluateKey evaluateEncrypt evaluateChoose input.1
      (depth input.1) (capacity input.1) (keyCoins input.1) (encCoins input.1) input.2 seed)
    n (coins n) (depth n) (capacity n) (keyCoins n) target.1 (remaining.take choiceBudget)
  let rest := remaining.drop choiceBudget
  let challenge := evaluateEncrypt (n, target.1, if bit then choice.1.2 else choice.1.1)
    (rest.take (encCoins n))
  modLeveledGuessCoins evaluateChoose evaluateEncrypt evaluateGuess n (capacity n)
    (encCoins n) (chooseCoins n) (guessCoins n) choice.2 challenge (rest.drop (encCoins n))

/-- Component seed laws are restricted to bounded inputs. The target, saved choice and
challenge supports needed by the guessing law are obtained from the original game's binds;
none is assumed as an external replay premise. No security or correctness hypothesis is used. -/
theorem eval_game_modLeveledAdversary_eq_map_coins (E : Scheme)
    (adversary : Encryption.Adversary)
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool)
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
    (hguess : ∀ state ciphertext, state.length ≤ chooseCoins n →
      ciphertext.length ≤ encCoins n + 1 →
      ProbComp.eval (adversary.guess n state ciphertext) =
        (BitString.uniformList (guessCoins n)).map (evaluateGuess (n, state, ciphertext))) :
    ProbComp.eval (Encryption.game E.keyGen E.encrypt
      (modLeveledAdversary E coins depth capacity adversary) bit n) =
      (BitString.uniformList (modLeveledGameCoinBudget (coins n) (depth n) (capacity n)
        (keyCoins n) (encCoins n) (chooseCoins n) (guessCoins n))).map
        (modLeveledGameCoins evaluateKey evaluateEncrypt evaluateChoose evaluateGuess coins depth
          capacity keyCoins encCoins chooseCoins guessCoins bit n) := by
  let choiceBudget := modLeveledChooseCoinBudget (coins n) (depth n) (capacity n)
    (keyCoins n) (encCoins n) (chooseCoins n)
  let guessBudget := leveledGuessCoinBudget (depth n) (capacity n) (encCoins n)
    (chooseCoins n) (guessCoins n)
  let evaluateZero := fun (input : ℕ × List Bool) seed =>
    zeroLinkChooseCoins evaluateKey evaluateEncrypt evaluateChoose input.1
      (depth input.1) (capacity input.1) (keyCoins input.1)
      (encCoins input.1) input.2 seed
  let chooseReplay := fun pk => modLeveledChooseCoins evaluateKey evaluateZero n (coins n)
    (depth n) (capacity n) (keyCoins n) pk
  let finish := fun (target : List Bool × List Bool) (chosen : (Bool × Bool) × List Bool)
      encSeed guessSeed => modLeveledGuessCoins evaluateChoose evaluateEncrypt evaluateGuess
        n (capacity n) (encCoins n) (chooseCoins n) (guessCoins n) chosen.2
        (evaluateEncrypt (n, target.1, if bit then chosen.1.2 else chosen.1.1) encSeed) guessSeed
  have hchoiceReplay (target) (htarget : target ∈ (ProbComp.eval (E.keyGen n)).support) :
      ProbComp.eval ((modLeveledAdversary E coins depth capacity adversary).choose n target.1) =
        (BitString.uniformList choiceBudget).map (chooseReplay target.1) := by
    apply eval_modLeveledAdversary_choose_eq_map_coins E adversary coins depth capacity
      evaluateKey evaluateZero n (keyCoins n)
        (depth n * keyCoins n + (depth n * capacity n * encCoins n + chooseCoins n)) target.1 hkey
    · exact eval_zeroLinkAdversary_choose_eq_map_coins E adversary depth evaluateKey evaluateEncrypt
        evaluateChoose n (capacity n) pkBound (encCoins n) (keyCoins n) (chooseCoins n)
          target.1 (hkeys target htarget).1 hkey hkeys hencrypt
          (fun artifact hbound => (hchoose artifact hbound).1)
    · omega
  simp only [Encryption.game, Encryption.gameOn, ↓reduceIte, ProbComp.eval_bind]
  trans (ProbComp.eval (E.keyGen n)).bind (fun target =>
    (BitString.uniformList choiceBudget).bind (fun choiceSeed =>
      (BitString.uniformList (encCoins n)).bind (fun encSeed =>
        (BitString.uniformList guessBudget).map
          (finish target (chooseReplay target.1 choiceSeed) encSeed))))
  · apply PMF.bind_congr_on_support
    intro target htarget
    trans (ProbComp.eval ((modLeveledAdversary E coins depth capacity adversary).choose n
      target.1)).bind (fun chosen =>
        (ProbComp.eval (E.encrypt n target.1
          (if bit then chosen.1.2 else chosen.1.1))).bind (fun challenge =>
            (BitString.uniformList guessBudget).map
              (modLeveledGuessCoins evaluateChoose evaluateEncrypt evaluateGuess n (capacity n)
                (encCoins n) (chooseCoins n) (guessCoins n) chosen.2 challenge)))
    · apply PMF.bind_congr_on_support
      intro chosen hchosen
      apply PMF.bind_congr_on_support
      intro challenge hchallenge
      exact eval_modLeveledAdversary_guess_eq_map_coins E adversary coins depth capacity
        evaluateChoose evaluateEncrypt evaluateGuess n pkBound (encCoins n) (chooseCoins n)
          (guessCoins n) target chosen challenge hkeys htarget hchosen
          ((hencrypt target.1 (hkeys target htarget).1 _).2 challenge hchallenge)
          hencrypt hchoose hguess
    rw [hchoiceReplay target htarget, PMF.bind_map]
    simp only [(hencrypt target.1 (hkeys target htarget).1 _).1, PMF.bind_map]
    rfl
  rw [hkey, PMF.bind_map]
  dsimp only [Function.comp_def]
  change _ = (BitString.uniformList (keyCoins n + (choiceBudget +
    (encCoins n + guessBudget)))).bind (fun tape => PMF.pure
      (finish (evaluateKey n (tape.take (keyCoins n)))
        (chooseReplay (evaluateKey n (tape.take (keyCoins n))).1
          ((tape.drop (keyCoins n)).take choiceBudget))
        (((tape.drop (keyCoins n)).drop choiceBudget).take (encCoins n))
        (((tape.drop (keyCoins n)).drop choiceBudget).drop (encCoins n))))
  rw [BitString.uniformList_bind_split (keyCoins n) (choiceBudget + (encCoins n + guessBudget))
    (fun keys rest => PMF.pure (finish (evaluateKey n keys)
      (chooseReplay (evaluateKey n keys).1 (rest.take choiceBudget))
      ((rest.drop choiceBudget).take (encCoins n))
      ((rest.drop choiceBudget).drop (encCoins n))))]
  congr 1 with keys : 1
  rw [BitString.uniformList_bind_split choiceBudget (encCoins n + guessBudget)
    (fun chosen rest => PMF.pure (finish (evaluateKey n keys)
      (chooseReplay (evaluateKey n keys).1 chosen) (rest.take (encCoins n))
      (rest.drop (encCoins n))))]
  congr 1 with chosen : 1
  rw [BitString.uniformList_bind_split (encCoins n) guessBudget
    (fun encSeed guessSeed => PMF.pure (finish (evaluateKey n keys)
      (chooseReplay (evaluateKey n keys).1 chosen) encSeed guessSeed))]
  rfl

/-- The complete replay is native polynomial time in the unary parameter and complete tape,
for either fixed challenge world. This does not assert a multiplicative runtime ratio to the
adversary's running time. -/
@[fun_prop] theorem computableInPolyTime_modLeveledGameCoins
    {evaluateKey : ℕ → List Bool → List Bool × List Bool}
    {evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool}
    {evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool}
    {evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool}
    (hkey : ComputableInPolyTime (fun (n, tape) => evaluateKey n tape)
      (encPair encUnary encBits) (encPair encBits encBits))
    (hencrypt : ComputableInPolyTime (fun (input, tape) => evaluateEncrypt input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    (hchoose : ComputableInPolyTime (fun (input, tape) => evaluateChoose input tape)
      (encPair (encPair encUnary encBits) encBits) (encPair (encPair encBool encBool) encBits))
    (hguess : ComputableInPolyTime (fun (input, tape) => evaluateGuess input tape)
      (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool)
    {coins depth capacity keyCoins encCoins chooseCoins guessCoins : ℕ → ℕ}
    (hcoins : ComputableInPolyTime coins encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary)
    (hkeyCoins : ComputableInPolyTime keyCoins encUnary encUnary)
    (hencCoins : ComputableInPolyTime encCoins encUnary encUnary)
    (hchooseCoins : ComputableInPolyTime chooseCoins encUnary encUnary)
    (hguessCoins : ComputableInPolyTime guessCoins encUnary encUnary) (bit : Bool) :
    ComputableInPolyTime (fun (n, tape) => modLeveledGameCoins evaluateKey evaluateEncrypt
      evaluateChoose evaluateGuess coins depth capacity keyCoins encCoins chooseCoins guessCoins
        bit n tape) (encPair encUnary encBits) encBool := by
  let evaluateZero := fun (input : ℕ × List Bool) seed => zeroLinkChooseCoins evaluateKey
    evaluateEncrypt evaluateChoose input.1 (depth input.1) (capacity input.1)
      (keyCoins input.1) (encCoins input.1) input.2 seed
  have hzero : ComputableInPolyTime (fun (input, seed) => evaluateZero input seed)
      (encPair (encPair encUnary encBits) encBits) (encPair (encPair encBool encBool) encBits) := by
    apply computableInPolyTime_zeroLinkChooseCoins hkey hencrypt hchoose <;> fun_prop
  let choiceBudget := fun n => modLeveledChooseCoinBudget (coins n) (depth n) (capacity n)
    (keyCoins n) (encCoins n) (chooseCoins n)
  have hchoiceBudget : ComputableInPolyTime choiceBudget encUnary encUnary := by
    dsimp only [choiceBudget, modLeveledChooseCoinBudget]
    fun_prop
  let target := fun (p : ℕ × List Bool) => evaluateKey p.1 (p.2.take (keyCoins p.1))
  have htarget : ComputableInPolyTime target (encPair encUnary encBits)
      (encPair encBits encBits) := hkey.comp (show ComputableInPolyTime
        (fun p : ℕ × List Bool => (p.1, p.2.take (keyCoins p.1))) (encPair encUnary encBits)
          (encPair encUnary encBits) by fun_prop)
  let chosen := fun (p : ℕ × List Bool) => modLeveledChooseCoins evaluateKey evaluateZero p.1
    (coins p.1) (depth p.1) (capacity p.1) (keyCoins p.1) (target p).1
      ((p.2.drop (keyCoins p.1)).take (choiceBudget p.1))
  have hn := ComputableInPolyTime.fst encUnary encBits
  have htape := ComputableInPolyTime.snd encUnary encBits
  have hremaining := htape.bitsDropWithInput (hkeyCoins.comp hn)
  have hrest := hremaining.bitsDropWithInput (hchoiceBudget.comp hn)
  -- Explicit replay arguments avoid unfolding the whole selector while inferring its inputs.
  have hchosen : ComputableInPolyTime chosen (encPair encUnary encBits)
      (encPair (encPair encBool encBool) encBits) :=
    computableInPolyTime_modLeveledChooseCoins
      (evaluateKey := evaluateKey) (evaluateZero := evaluateZero)
      (n := fun p : ℕ × List Bool => p.1)
      (indexCoins := fun p => coins p.1) (depth := fun p => depth p.1)
      (capacity := fun p => capacity p.1) (keyCoins := fun p => keyCoins p.1)
      (challengePk := fun p => (target p).1)
      (tape := fun p => (p.2.drop (keyCoins p.1)).take (choiceBudget p.1))
      hkey hzero hn (hcoins.comp hn) (hdepth.comp hn)
      (hcapacity.comp hn) (hkeyCoins.comp hn) htarget.fst'
      (hremaining.bitsTakeWithInput (hchoiceBudget.comp hn))
  let challenge := fun (p : ℕ × List Bool) => evaluateEncrypt
    (p.1, (target p).1, if bit then (chosen p).1.2 else (chosen p).1.1)
    (((p.2.drop (keyCoins p.1)).drop (choiceBudget p.1)).take (encCoins p.1))
  have hmessage : ComputableInPolyTime
      (fun p => if bit then (chosen p).1.2 else (chosen p).1.1)
      (encPair encUnary encBits) encBool := by
    cases bit
    · exact hchosen.fst'.fst'
    · exact hchosen.fst'.snd'
  have hchallenge : ComputableInPolyTime challenge (encPair encUnary encBits) encBits :=
    hencrypt.comp ((hn.prod (htarget.fst'.prod hmessage)).prod
      (hrest.bitsTakeWithInput (hencCoins.comp hn)))
  change ComputableInPolyTime (fun p => modLeveledGuessCoins evaluateChoose evaluateEncrypt
    evaluateGuess p.1 (capacity p.1) (encCoins p.1) (chooseCoins p.1) (guessCoins p.1)
      (chosen p).2 (challenge p)
      (((p.2.drop (keyCoins p.1)).drop (choiceBudget p.1)).drop (encCoins p.1))) _ _
  apply computableInPolyTime_modLeveledGuessCoins hchoose hencrypt hguess hchooseCoins
    hencCoins hguessCoins hcapacity
    hn hchosen.snd' hchallenge (hrest.bitsDropWithInput (hencCoins.comp hn))

end Cslib.Crypto.Homomorphic.Leveled
