/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.ExactSecurity
public import CslibFrontier.Crypto.Computational.Homomorphic.KeyChain.Reduction.CoinTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.PMF.Bind

/-!
# Concrete guessing-stage tapes for leveled encryption

The public-key game consumes independent choice, encryption, and guessing blocks. Combining
this replay with the actual link splice realizes the existing guessing-stage coin budget on
states supported by the original choice sampler. The native certificate charges the full saved
state and ciphertext; it is not the multiplicative runtime ratio in Gentry's source theorem.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.publicKeyGameCoins`: replay the adaptive public-key game.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.eval_publicKeyGame_eq_map_coins`: exact component replay.
* `Cslib.Crypto.Homomorphic.Scheme.eval_modLinkAdversary_guess_eq_map_coins`: the existing
  concrete guessing budget on supported choices.
* `Cslib.Crypto.Homomorphic.Scheme.computableInPolyTime_modLinkGuessCoins`: native combined replay.
-/

public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability Turing.MultiTapeTM

/-- Replay message selection, challenge encryption, and guessing with disjoint seed blocks.
The original saved state and the `false` ciphertext tag are passed to the guessing evaluator. -/
@[expose] def publicKeyGameCoins
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool)
    (bit : Bool) (chooseCoins encCoins : ℕ)
    (input : ℕ × List (List Bool) × List (List (List Bool))) (tape : List Bool) : Bool :=
  let choice := evaluateChoose (input.1, encPublicKey input.2) (tape.take chooseCoins)
  let remaining := tape.drop chooseCoins
  let ciphertext := evaluateEncrypt
    (input.1, input.2.1.getD 0 [], if bit then choice.1.2 else choice.1.1)
    (remaining.take encCoins)
  evaluateGuess (input.1, choice.2, false :: ciphertext) (remaining.drop encCoins)

/-- Component laws realize the original adaptive game exactly. No correctness or security
assumption is needed, and the saved state may depend on the sampled messages. The guessing
law is required only on the correlated supported choice/ciphertext pairs. -/
theorem eval_publicKeyGame_eq_map_coins (E : Scheme) (adversary : Encryption.Adversary)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool)
    (bit : Bool) (n chooseCoins encCoins guessCoins : ℕ)
    (artifact : List (List Bool) × List (List (List Bool)))
    (hchoose : ProbComp.eval (adversary.choose n (encPublicKey artifact)) =
      (BitString.uniformList chooseCoins).map (evaluateChoose (n, encPublicKey artifact)))
    (hencrypt : ∀ message, ProbComp.eval (E.encrypt n (artifact.1.getD 0 []) message) =
      (BitString.uniformList encCoins).map
        (evaluateEncrypt (n, artifact.1.getD 0 [], message)))
    (hguess : ∀ choice ∈ (ProbComp.eval (adversary.choose n (encPublicKey artifact))).support,
      ∀ ciphertext ∈ (ProbComp.eval (E.encrypt n (artifact.1.getD 0 [])
        (if bit then choice.1.2 else choice.1.1))).support,
      ProbComp.eval (adversary.guess n choice.2 (false :: ciphertext)) =
        (BitString.uniformList guessCoins).map
          (evaluateGuess (n, choice.2, false :: ciphertext))) :
    ProbComp.eval (publicKeyGame E adversary bit n artifact) =
      (BitString.uniformList (chooseCoins + (encCoins + guessCoins))).map
        (publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess bit chooseCoins encCoins
          (n, artifact)) := by
  simp only [publicKeyGame, ProbComp.eval_bind]
  trans (ProbComp.eval (adversary.choose n (encPublicKey artifact))).bind (fun choice =>
    (ProbComp.eval (E.encrypt n (artifact.1.getD 0 [])
      (if bit then choice.1.2 else choice.1.1))).bind (fun ciphertext =>
      (BitString.uniformList guessCoins).map
        (evaluateGuess (n, choice.2, false :: ciphertext))))
  · apply PMF.bind_congr_on_support
    intro choice hchoice
    apply PMF.bind_congr_on_support
    exact hguess choice hchoice
  simp only [hchoose, hencrypt, PMF.bind_map, Function.comp_def]
  rw [PMF.map]
  change _ = (BitString.uniformList (chooseCoins + (encCoins + guessCoins))).bind
    (fun tape => PMF.pure (publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess bit
      chooseCoins encCoins (n, artifact) tape))
  unfold publicKeyGameCoins
  rw [BitString.uniformList_bind_split _ _ (fun first rest => PMF.pure
    (evaluateGuess (n, (evaluateChoose (n, encPublicKey artifact) first).2,
      false :: evaluateEncrypt (n, artifact.1.getD 0 [],
        if bit then (evaluateChoose (n, encPublicKey artifact) first).1.2
        else (evaluateChoose (n, encPublicKey artifact) first).1.1) (rest.take encCoins))
      (rest.drop encCoins)))]
  congr 1 with first : 1
  rw [BitString.uniformList_bind_split _ _ (fun second third => PMF.pure
    (evaluateGuess (n, (evaluateChoose (n, encPublicKey artifact) first).2,
      false :: evaluateEncrypt (n, artifact.1.getD 0 [],
        if bit then (evaluateChoose (n, encPublicKey artifact) first).1.2
        else (evaluateChoose (n, encPublicKey artifact) first).1.1) second) third))]
  rfl

/-- The concrete adaptive-game replay is native polynomial time in the public artifact,
parameter, tape, and unary component budgets. -/
@[fun_prop] theorem computableInPolyTime_publicKeyGameCoins
    {evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool}
    {evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool}
    {evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool}
    (hchoose : ComputableInPolyTime (fun (input, tape) => evaluateChoose input tape)
      (encPair (encPair encUnary encBits) encBits) (encPair (encPair encBool encBool) encBits))
    (hencrypt : ComputableInPolyTime (fun (input, tape) => evaluateEncrypt input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    (hguess : ComputableInPolyTime (fun (input, tape) => evaluateGuess input tape)
      (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool)
    (bit : Bool) {α : Type} {input : α ↪ List Bool} {n chooseCoins encCoins : α → ℕ}
    {artifact : α → List (List Bool) × List (List (List Bool))} {tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hchooseCoins : ComputableInPolyTime chooseCoins input encUnary)
    (hencCoins : ComputableInPolyTime encCoins input encUnary)
    (hartifact : ComputableInPolyTime artifact input encPublicKey)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess
      bit (chooseCoins a) (encCoins a) (n a, artifact a) (tape a)) input encBool := by
  have hpublic := hartifact.encoding_comp
  have hchoice := hchoose.comp (show ComputableInPolyTime
    (fun a => ((n a, encPublicKey (artifact a)), (tape a).take (chooseCoins a))) input
      (encPair (encPair encUnary encBits) encBits) by fun_prop)
  have hfirst := (ComputableInPolyTime.listGetD (encA := encBits) []).comp
    (hartifact.fst'.prod (ComputableInPolyTime.const 0))
  have hcipher := hencrypt.comp (show ComputableInPolyTime (fun a =>
    ((n a, (artifact a).1.getD 0 [], if bit then
      (evaluateChoose (n a, encPublicKey (artifact a)) ((tape a).take (chooseCoins a))).1.2
      else (evaluateChoose (n a, encPublicKey (artifact a))
        ((tape a).take (chooseCoins a))).1.1),
      ((tape a).drop (chooseCoins a)).take (encCoins a))) input
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) by
    cases bit <;> fun_prop)
  unfold publicKeyGameCoins
  exact hguess.comp (show ComputableInPolyTime (fun a =>
    ((n a, (evaluateChoose (n a, encPublicKey (artifact a))
      ((tape a).take (chooseCoins a))).2,
      false :: evaluateEncrypt (n a, (artifact a).1.getD 0 [], if bit then
        (evaluateChoose (n a, encPublicKey (artifact a)) ((tape a).take (chooseCoins a))).1.2
        else (evaluateChoose (n a, encPublicKey (artifact a))
          ((tape a).take (chooseCoins a))).1.1)
        (((tape a).drop (chooseCoins a)).take (encCoins a))),
      ((tape a).drop (chooseCoins a)).drop (encCoins a))) input
      (encPair (encPair encUnary (encPair encBits encBits)) encBits) by fun_prop)

end Cslib.Crypto.Homomorphic.Leveled

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

/-- Modular selection preserves the original choice support, including rejected coordinates.
An active choice stores exactly `depth` known keys and a valid selected secret bit. -/
theorem modLinkAdversary_choose_support (E : Scheme) (coins depth capacity : ℕ → ℕ)
    (test : ℕ → (List (List Bool) × List (List (List Bool))) → ProbComp Bool)
    (n : ℕ) (challengePk : List Bool) (choice : (Bool × Bool) × List Bool)
    (hchoice : choice ∈ (ProbComp.eval
      ((E.modLinkAdversary coins depth capacity test).choose n challengePk)).support) :
    choice = rejectLinkChoice ∨ ∃ before predecessor after cut,
      before.length + after.length + 1 = depth n ∧
      (∀ key ∈ before ++ predecessor :: after, key ∈ (ProbComp.eval (E.keyGen n)).support) ∧
      cut < capacity n ∧ cut < predecessor.2.length ∧
      choice = ((predecessor.2.getD cut false, false),
        activeLinkState before predecessor challengePk after cut) := by
  simp only [modLinkAdversary, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hchoice
  obtain ⟨reverseIndex, _, cut, _, hchoice⟩ := hchoice
  split at hchoice
  · rename_i hreverse
    split at hchoice
    · rename_i hcut
      rcases E.chooseLinkAt_support n _ _ cut challengePk choice hchoice with h | h
      · exact Or.inl h
      obtain ⟨before, predecessor, after, hbefore, hafter, hkeys, hbit, hchoice⟩ := h
      exact Or.inr ⟨before, predecessor, after, cut, by omega, hkeys, hcut, hbit, hchoice⟩
    · simpa only [ProbComp.eval_pure, PMF.mem_support_pure_iff] using Or.inl hchoice
  · simpa only [ProbComp.eval_pure, PMF.mem_support_pure_iff] using Or.inl hchoice

/-- The original modular reduction's guess is realized with the existing concrete budget,
for every supported choice and every supplied challenge ciphertext. Validity and chain length
come from the actual choice sampler; the hypotheses concern only component seed laws and
supported generated-key widths. This does not yet assemble the unified reduction's selector. -/
theorem eval_modLinkAdversary_guess_eq_map_coins (E : Scheme)
    (adversary : Encryption.Adversary) (coins depth capacity : ℕ → ℕ)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool)
    (bit : Bool) (n chooseCoins encCoins guessCoins : ℕ)
    (challengePk challenge : List Bool) (choice : (Bool × Bool) × List Bool)
    (hchoice : choice ∈ (ProbComp.eval ((E.modLinkAdversary coins depth capacity
      (Leveled.publicKeyGame E adversary bit)).choose n challengePk)).support)
    (hwidth : ∀ key ∈ (ProbComp.eval (E.keyGen n)).support, key.2.length ≤ capacity n)
    (hchoose : ∀ artifact, ProbComp.eval (adversary.choose n (Leveled.encPublicKey artifact)) =
      (BitString.uniformList chooseCoins).map
        (evaluateChoose (n, Leveled.encPublicKey artifact)))
    (hencrypt : ∀ pk message, ProbComp.eval (E.encrypt n pk message) =
      (BitString.uniformList encCoins).map (evaluateEncrypt (n, pk, message)))
    (hguess : ∀ state ciphertext, ProbComp.eval (adversary.guess n state (false :: ciphertext)) =
      (BitString.uniformList guessCoins).map (evaluateGuess (n, state, false :: ciphertext))) :
    ProbComp.eval ((E.modLinkAdversary coins depth capacity
      (Leveled.publicKeyGame E adversary bit)).guess n choice.2 challenge) =
      (BitString.uniformList (Leveled.leveledGuessCoinBudget (depth n) (capacity n)
        encCoins chooseCoins guessCoins)).map
        (guessLinkCoins evaluateEncrypt
          (Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess bit
            chooseCoins encCoins) n encCoins (capacity n) choice.2 challenge) := by
  rcases E.modLinkAdversary_choose_support coins depth capacity _ n challengePk choice hchoice
    with rfl | ⟨before, predecessor, after, cut, hlength, hkeys, _, hcut, rfl⟩
  · simp [modLinkAdversary, rejectLinkChoice, ProbComp.eval_pure,
      PMF.map, Function.comp_def, guessLinkCoins]
  have hpred := hwidth predecessor (hkeys predecessor (by simp))
  have hpositive : 1 ≤ depth n * capacity n := by
    have hd : 1 ≤ depth n := by omega
    have hc : 1 ≤ capacity n := by omega
    exact Nat.mul_le_mul hd hc
  have hsize : ((before.length + after.length + 1) * capacity n - 1) * encCoins +
      (chooseCoins + (encCoins + guessCoins)) =
      Leveled.leveledGuessCoinBudget (depth n) (capacity n) encCoins chooseCoins guessCoins := by
    rw [hlength]
    have hsum := Nat.sub_add_cancel hpositive
    calc
      _ = ((depth n * capacity n - 1) + 1) * encCoins + chooseCoins + guessCoins := by ring
      _ = _ := by rw [hsum]; rfl
  simpa only [modLinkAdversary, hsize] using
    E.eval_guessLink_active_eq_map_coins (Leveled.publicKeyGame E adversary bit)
      evaluateEncrypt
      (Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess bit
        chooseCoins encCoins) n encCoins (chooseCoins + (encCoins + guessCoins)) (capacity n)
      before predecessor challengePk after cut challenge hcut
      (fun key hkey => hwidth key (hkeys key hkey))
      (fun pk _ message => hencrypt pk message)
      (fun links _ => Leveled.eval_publicKeyGame_eq_map_coins E adversary evaluateChoose
        evaluateEncrypt evaluateGuess bit n chooseCoins encCoins guessCoins _ (hchoose _)
          (hencrypt _) (fun chosen _ ciphertext _ => hguess chosen.2 ciphertext))

/-- The complete link-guess replay has a native deterministic certificate when component
replays and unary budget families do. Its input includes the complete saved context, challenge,
and tape; no validity restriction is needed for this total computational certificate. -/
@[fun_prop] theorem computableInPolyTime_modLinkGuessCoins
    {evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool}
    {evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool}
    {evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool}
    (hchoose : ComputableInPolyTime (fun (input, tape) => evaluateChoose input tape)
      (encPair (encPair encUnary encBits) encBits) (encPair (encPair encBool encBool) encBits))
    (hencrypt : ComputableInPolyTime (fun (input, tape) => evaluateEncrypt input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    (hguess : ComputableInPolyTime (fun (input, tape) => evaluateGuess input tape)
      (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool)
    (bit : Bool) {chooseCoins encCoins capacity : ℕ → ℕ}
    (hchooseCoins : ComputableInPolyTime chooseCoins encUnary encUnary)
    (hencCoins : ComputableInPolyTime encCoins encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    {state challenge tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hstate : ComputableInPolyTime state input encBits)
    (hchallenge : ComputableInPolyTime challenge input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => guessLinkCoins evaluateEncrypt
      (fun p seed => Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess
        bit (chooseCoins p.1) (encCoins p.1) p seed) (n a) (encCoins (n a)) (capacity (n a))
        (state a) (challenge a) (tape a)) input encBool := by
  apply computableInPolyTime_guessLinkCoins hencrypt
  · apply Leveled.computableInPolyTime_publicKeyGameCoins hchoose hencrypt hguess bit
    all_goals fun_prop
  all_goals fun_prop

end Cslib.Crypto.Homomorphic.Scheme
