/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.ZeroCoinTape
public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.GuessOverhead
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.SuppCases

/-!
# Saved tapes for the actual modular leveled adversary

The original three-way selector, message swap and state tags determine which replay runs.
The zero-range fallback still runs the zero-link adversary, including at depth zero.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.modLeveledGuessCoins`: replay the tagged guessing stage.
* `Cslib.Crypto.Homomorphic.Leveled.modLeveledChooseCoins`: replay the original modular selector.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.modLeveledAdversary_choose_support`: actual tagged support.
* `Cslib.Crypto.Homomorphic.Leveled.eval_modLeveledAdversary_guess_eq_map_coins`: supported
  guessing replay from bounded component laws.
* `Cslib.Crypto.Homomorphic.Leveled.eval_modLeveledAdversary_choose_eq_map_coins`: exact choice
  law with three selector blocks and a common padded payload.
* `Cslib.Crypto.Homomorphic.Leveled.computableInPolyTime_modLeveledGuessCoins`,
  `Cslib.Crypto.Homomorphic.Leveled.computableInPolyTime_modLeveledChooseCoins`: native dispatch.
-/

public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Probability Turing.MultiTapeTM

/-- The original selector preserves one of the three tagged branch supports, or rejects.
The second encrypted-link branch swaps its messages before tagging; the saved state is retained. -/
theorem modLeveledAdversary_choose_support (E : Scheme) (adversary : Encryption.Adversary)
    (coins depth capacity : ℕ → ℕ) (n : ℕ) (challengePk : List Bool)
    (choice : (Bool × Bool) × List Bool)
    (hchoice : choice ∈ (ProbComp.eval
      ((modLeveledAdversary E coins depth capacity adversary).choose n challengePk)).support) :
    choice = rejectLeveledChoice ∨
      (∃ chosen, chosen ∈ (ProbComp.eval ((E.modLinkAdversary coins depth capacity
        (publicKeyGame E adversary false)).choose n challengePk)).support ∧
        choice = tagLeveledChoice false false chosen) ∨
      (∃ chosen, chosen ∈ (ProbComp.eval ((E.modLinkAdversary coins depth capacity
        (publicKeyGame E adversary true)).choose n challengePk)).support ∧
        choice = tagLeveledChoice false true (swapLeveledChoice chosen)) ∨
      ∃ chosen, chosen ∈ (ProbComp.eval
        ((zeroLinkAdversary E depth adversary).choose n challengePk)).support ∧
        choice = tagLeveledChoice true false chosen := by
  by_cases hpos : 0 < depth n ∧ 0 < capacity n
  · supp_cases hchoice [modLeveledAdversary, hpos] with ⟨hop, _, hchoice⟩
    split at hchoice
    · supp_cases hchoice with ⟨chosen, hchosen, rfl⟩
      exact Or.inr (Or.inl ⟨chosen, hchosen, rfl⟩)
    · split at hchoice
      · supp_cases hchoice with ⟨chosen, hchosen, rfl⟩
        exact Or.inr (Or.inr (Or.inl ⟨chosen, hchosen, rfl⟩))
      · supp_cases hchoice with ⟨reverseIndex, _, bitIndex, _, hchoice⟩
        split at hchoice
        · split at hchoice
          · supp_cases hchoice with ⟨chosen, hchosen, rfl⟩
            exact Or.inr (Or.inr (Or.inr ⟨chosen, hchosen, rfl⟩))
          · supp_cases hchoice
            exact Or.inl rfl
        · supp_cases hchoice
          exact Or.inl rfl
  · supp_cases hchoice [modLeveledAdversary, hpos] with ⟨chosen, hchosen, rfl⟩
    exact Or.inr (Or.inr (Or.inr ⟨chosen, hchosen, rfl⟩))

/-- Replay the original tagged dispatch. The zero-link branch uses a prefix of the allocated
guess tape; the two link branches retain their original internal public-key-game world. -/
@[expose] def modLeveledGuessCoins
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool)
    (n capacity encCoins chooseCoins guessCoins : ℕ) (state challenge : List Bool) :
    List Bool → Bool := fun tape =>
  if state.headD true then
    if state.tail.headD true then false
    else evaluateGuess (n, state.tail.tail, false :: challenge) (tape.take guessCoins)
  else if state.tail.headD true then
    Scheme.guessLinkCoins evaluateEncrypt
      (publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess true chooseCoins encCoins)
      n encCoins capacity state.tail.tail challenge tape
  else
    Scheme.guessLinkCoins evaluateEncrypt
      (publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess false chooseCoins encCoins)
      n encCoins capacity state.tail.tail challenge tape

/-- Both encrypted-link worlds and the zero-link branch realize the same allocated guess
budget on actual supported choices. The supplied challenge only needs its proved size bound. -/
theorem eval_modLeveledAdversary_guess_eq_map_coins (E : Scheme)
    (adversary : Encryption.Adversary) (coins depth capacity : ℕ → ℕ)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool)
    (n pkBound encCoins chooseCoins guessCoins : ℕ) (target : List Bool × List Bool)
    (choice : (Bool × Bool) × List Bool) (challenge : List Bool)
    (hkeys : ∀ key ∈ (ProbComp.eval (E.keyGen n)).support,
      key.1.length ≤ pkBound ∧ key.2.length ≤ capacity n)
    (htarget : target ∈ (ProbComp.eval (E.keyGen n)).support)
    (hchoice : choice ∈ (ProbComp.eval
      ((modLeveledAdversary E coins depth capacity adversary).choose n target.1)).support)
    (hchallenge : challenge.length ≤ encCoins)
    (hencrypt : ∀ pk, pk.length ≤ pkBound → ∀ message,
      ProbComp.eval (E.encrypt n pk message) =
        (BitString.uniformList encCoins).map (evaluateEncrypt (n, pk, message)) ∧
      ∀ ciphertext ∈ (ProbComp.eval (E.encrypt n pk message)).support,
        ciphertext.length ≤ encCoins)
    (hchoose : ∀ artifact, (encPublicKey artifact).length ≤
        publicKeyLengthBound (depth n) (capacity n) pkBound encCoins →
      ProbComp.eval (adversary.choose n (encPublicKey artifact)) =
        (BitString.uniformList chooseCoins).map (evaluateChoose (n, encPublicKey artifact)) ∧
      ∀ chosen ∈ (ProbComp.eval (adversary.choose n (encPublicKey artifact))).support,
        chosen.2.length ≤ chooseCoins)
    (hguess : ∀ state ciphertext, state.length ≤ chooseCoins → ciphertext.length ≤ encCoins + 1 →
      ProbComp.eval (adversary.guess n state ciphertext) =
        (BitString.uniformList guessCoins).map (evaluateGuess (n, state, ciphertext))) :
    ProbComp.eval ((modLeveledAdversary E coins depth capacity adversary).guess n
      choice.2 challenge) =
      (BitString.uniformList (leveledGuessCoinBudget (depth n) (capacity n)
        encCoins chooseCoins guessCoins)).map
        (modLeveledGuessCoins evaluateChoose evaluateEncrypt evaluateGuess n (capacity n)
          encCoins chooseCoins guessCoins choice.2 challenge) := by
  unfold modLeveledGuessCoins
  rcases modLeveledAdversary_choose_support E adversary coins depth capacity n target.1
    choice hchoice with rfl | ⟨chosen, hchosen, rfl⟩ | ⟨chosen, hchosen, rfl⟩ |
      ⟨chosen, hchosen, rfl⟩
  · simp [modLeveledAdversary, leveledAdversary, rejectLeveledChoice,
      ProbComp.eval_pure, PMF.map, Function.comp_def]
  · simpa only [modLeveledAdversary, leveledAdversary, tagLeveledChoice,
      List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte,
      Scheme.modLinkAdversary, Scheme.linkAdversary] using
        E.eval_modLinkAdversary_guess_eq_map_coins_of_bounds adversary coins depth capacity
          evaluateChoose evaluateEncrypt evaluateGuess false n pkBound encCoins chooseCoins
          guessCoins target challenge chosen hkeys htarget hchosen hchallenge
          hencrypt hchoose hguess
  · simpa only [modLeveledAdversary, leveledAdversary, tagLeveledChoice, swapLeveledChoice,
      List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte,
      Scheme.modLinkAdversary, Scheme.linkAdversary] using
        E.eval_modLinkAdversary_guess_eq_map_coins_of_bounds adversary coins depth capacity
          evaluateChoose evaluateEncrypt evaluateGuess true n pkBound encCoins chooseCoins
          guessCoins target challenge chosen hkeys htarget hchosen hchallenge
          hencrypt hchoose hguess
  · have hstate := zeroLinkAdversary_choose_state_length_le E adversary depth n
      (capacity n) pkBound encCoins chooseCoins target.1 (hkeys target htarget).1 hkeys
      (fun pk hpk message => (hencrypt pk hpk message).2)
      (fun artifact hbound => (hchoose artifact hbound).2) hchosen
    have hct : (false :: challenge).length ≤ encCoins + 1 := by simp only [List.length_cons]; omega
    have hlaw := hguess chosen.2 (false :: challenge) hstate hct
    have hbudget : guessCoins ≤ leveledGuessCoinBudget (depth n) (capacity n)
        encCoins chooseCoins guessCoins := by unfold leveledGuessCoinBudget; omega
    rw [← BitString.uniformList_take hbudget, PMF.map_comp] at hlaw
    simpa only [modLeveledAdversary, leveledAdversary, zeroLinkAdversary, tagLeveledChoice,
      List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte,
      Function.comp_def] using hlaw

/-- Native replay of the tagged dispatch charges the complete saved word, challenge and tape,
including arbitrary malformed words. The small allocated seed law separately requires support. -/
@[fun_prop] theorem computableInPolyTime_modLeveledGuessCoins
    {evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool}
    {evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool}
    {evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool}
    (hchoose : ComputableInPolyTime (fun (input, tape) => evaluateChoose input tape)
      (encPair (encPair encUnary encBits) encBits) (encPair (encPair encBool encBool) encBits))
    (hencrypt : ComputableInPolyTime (fun (input, tape) => evaluateEncrypt input tape)
      (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits)
    (hguess : ComputableInPolyTime (fun (input, tape) => evaluateGuess input tape)
      (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool)
    {chooseCoins encCoins guessCoins capacity : ℕ → ℕ}
    (hchooseCoins : ComputableInPolyTime chooseCoins encUnary encUnary)
    (hencCoins : ComputableInPolyTime encCoins encUnary encUnary)
    (hguessCoins : ComputableInPolyTime guessCoins encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    {state challenge tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hstate : ComputableInPolyTime state input encBits)
    (hchallenge : ComputableInPolyTime challenge input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => modLeveledGuessCoins evaluateChoose evaluateEncrypt evaluateGuess
      (n a) (capacity (n a)) (encCoins (n a)) (chooseCoins (n a)) (guessCoins (n a))
        (state a) (challenge a) (tape a)) input encBool := by
  have htail := ComputableInPolyTime.bitsTail.comp hstate
  have htailtail := ComputableInPolyTime.bitsTail.comp htail
  have hfirst := (ComputableInPolyTime.headD (encA := encBool) true).comp hstate
  have hsecond := (ComputableInPolyTime.headD (encA := encBool) true).comp htail
  have hlink (bit : Bool) : ComputableInPolyTime (fun a => Scheme.guessLinkCoins evaluateEncrypt
      (publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess bit
        (chooseCoins (n a)) (encCoins (n a))) (n a) (encCoins (n a)) (capacity (n a))
        (state a).tail.tail (challenge a) (tape a)) input encBool :=
    Scheme.computableInPolyTime_modLinkGuessCoins hchoose hencrypt hguess bit hchooseCoins
      hencCoins hcapacity hn htailtail hchallenge htape
  unfold modLeveledGuessCoins
  apply ComputableInPolyTime.ite_decide
  · simpa [Function.comp_def] using hfirst
  · apply ComputableInPolyTime.ite_decide
    · simpa [Function.comp_def] using hsecond
    · exact .const _
    · exact hguess.comp (show ComputableInPolyTime (fun a =>
        ((n a, (state a).tail.tail, false :: challenge a), (tape a).take (guessCoins (n a))))
        input (encPair (encPair encUnary (encPair encBits encBits)) encBits) by fun_prop)
  · apply ComputableInPolyTime.ite_decide
    · simpa [Function.comp_def] using hsecond
    · exact hlink true
    · exact hlink false

/-- Replay the actual modular selector and the selected branch. Link branches use a prefix
of the common payload; zero-link branches discard the three selector blocks. No ideal uniform
three-way selector replaces binary decoding modulo three. -/
@[expose] def modLeveledChooseCoins
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (evaluateZero : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (n indexCoins depth capacity keyCoins : ℕ) (challengePk : List Bool) :
    List Bool → (Bool × Bool) × List Bool := fun tape =>
  if 0 < depth ∧ 0 < capacity then
    let hop := min 3 (BitString.binaryValue (tape.take indexCoins) % 3)
    let remaining := tape.drop indexCoins
    if hop = 0 then
      tagLeveledChoice false false (Scheme.chooseModLinkCoins evaluateKey n indexCoins keyCoins
        depth capacity challengePk (remaining.take (2 * indexCoins + depth * keyCoins)))
    else if hop = 1 then
      tagLeveledChoice false true (swapLeveledChoice (Scheme.chooseModLinkCoins evaluateKey n
        indexCoins keyCoins depth capacity challengePk
        (remaining.take (2 * indexCoins + depth * keyCoins))))
    else
      let reverseIndex := min depth (BitString.binaryValue (remaining.take indexCoins) % depth)
      let rest := remaining.drop indexCoins
      let bitIndex := min capacity (BitString.binaryValue (rest.take indexCoins) % capacity)
      if reverseIndex = 0 then
        if bitIndex = 0 then
          tagLeveledChoice true false (evaluateZero (n, challengePk) (rest.drop indexCoins))
        else rejectLeveledChoice
      else rejectLeveledChoice
  else tagLeveledChoice true false (evaluateZero (n, challengePk) (tape.drop (3 * indexCoins)))

/-- A common payload bounds the link key blocks and realizes the original zero-link choice.
The unified modular selector adds three allocated index blocks. Unselected regions are ignored,
including all selector blocks in the original zero-range fallback. -/
theorem eval_modLeveledAdversary_choose_eq_map_coins (E : Scheme)
    (adversary : Encryption.Adversary) (coins depth capacity : ℕ → ℕ)
    (evaluateKey : ℕ → List Bool → List Bool × List Bool)
    (evaluateZero : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (n keyCoins zeroCoins : ℕ) (challengePk : List Bool)
    (hkey : ProbComp.eval (E.keyGen n) =
      (BitString.uniformList keyCoins).map (evaluateKey n))
    (hzero : ProbComp.eval ((zeroLinkAdversary E depth adversary).choose n challengePk) =
      (BitString.uniformList zeroCoins).map (evaluateZero (n, challengePk)))
    (hfits : depth n * keyCoins ≤ zeroCoins) :
    ProbComp.eval ((modLeveledAdversary E coins depth capacity adversary).choose n challengePk) =
      (BitString.uniformList (3 * coins n + zeroCoins)).map
        (modLeveledChooseCoins evaluateKey evaluateZero n (coins n) (depth n) (capacity n)
          keyCoins challengePk) := by
  by_cases hpos : 0 < depth n ∧ 0 < capacity n
  · let index (bound : ℕ) (seed : List Bool) := min bound (BitString.binaryValue seed % bound)
    let afterHop (first remaining : List Bool) :=
      if index 3 first = 0 then
        tagLeveledChoice false false (Scheme.chooseModLinkCoins evaluateKey n (coins n) keyCoins
          (depth n) (capacity n) challengePk
          (remaining.take (2 * coins n + depth n * keyCoins)))
      else if index 3 first = 1 then
        tagLeveledChoice false true (swapLeveledChoice (Scheme.chooseModLinkCoins evaluateKey n
          (coins n) keyCoins (depth n) (capacity n) challengePk
          (remaining.take (2 * coins n + depth n * keyCoins))))
      else if index (depth n) (remaining.take (coins n)) = 0 then
        if index (capacity n) ((remaining.drop (coins n)).take (coins n)) = 0 then
          tagLeveledChoice true false
            (evaluateZero (n, challengePk) ((remaining.drop (coins n)).drop (coins n)))
        else rejectLeveledChoice
      else rejectLeveledChoice
    have hsize : 3 * coins n + zeroCoins = coins n + (2 * coins n + zeroCoins) := by omega
    conv_rhs =>
      unfold modLeveledChooseCoins
      simp only [hpos, and_self, ↓reduceIte]
    change _ = (BitString.uniformList (3 * coins n + zeroCoins)).map
      (fun tape => afterHop (tape.take (coins n)) (tape.drop (coins n)))
    rw [hsize, PMF.map]
    dsimp only [Function.comp_def]
    rw [BitString.uniformList_bind_split (coins n) (2 * coins n + zeroCoins)
      (fun first rest => PMF.pure (afterHop first rest))]
    simp only [pmf_norm, modLeveledAdversary, hpos, and_self, ↓reduceIte, Scheme.sampleModIndex,
      ProbComp.sampleModNat, ProbComp.sampleBinaryNat, BitString.eval_sampleList]
    congr 1 with first : 1
    by_cases hfirst : index 3 first = 0
    · change min 3 (BitString.binaryValue first % 3) = 0 at hfirst
      have hlaw := E.eval_modLinkAdversary_choose_eq_map_coins evaluateKey coins depth capacity
        (publicKeyGame E adversary false) n keyCoins challengePk hkey
      have hbudget : 2 * coins n + depth n * keyCoins ≤ 2 * coins n + zeroCoins := by omega
      rw [← BitString.uniformList_take hbudget, PMF.map_comp] at hlaw
      simpa only [pmf_norm, afterHop, index, hfirst, ↓reduceIte, PMF.map] using
          congrArg (PMF.map (tagLeveledChoice false false)) hlaw
    · change ¬min 3 (BitString.binaryValue first % 3) = 0 at hfirst
      by_cases hsecond : min 3 (BitString.binaryValue first % 3) = 1
      · have hlaw := E.eval_modLinkAdversary_choose_eq_map_coins evaluateKey coins depth capacity
          (publicKeyGame E adversary true) n keyCoins challengePk hkey
        have hbudget : 2 * coins n + depth n * keyCoins ≤ 2 * coins n + zeroCoins := by omega
        rw [← BitString.uniformList_take hbudget, PMF.map_comp] at hlaw
        simpa only [pmf_norm, afterHop, index, hfirst, hsecond, ↓reduceIte, PMF.map,
          Nat.one_ne_zero] using
            congrArg (PMF.map (tagLeveledChoice false true ∘ swapLeveledChoice)) hlaw
      · simp only [pmf_norm, afterHop, index, hfirst, hsecond, ↓reduceIte,
          BitString.eval_sampleList]
        have hsize : 2 * coins n + zeroCoins = coins n + (coins n + zeroCoins) := by omega
        rw [hsize, BitString.uniformList_bind_split (coins n) (coins n + zeroCoins)
          (fun second rest => PMF.pure
            (if index (depth n) second = 0 then
              if index (capacity n) (rest.take (coins n)) = 0 then
                tagLeveledChoice true false (evaluateZero (n, challengePk) (rest.drop (coins n)))
              else rejectLeveledChoice
            else rejectLeveledChoice))]
        congr 1 with second : 1
        rw [BitString.uniformList_bind_split (coins n) zeroCoins
          (fun third rest => PMF.pure
            (if index (depth n) second = 0 then
              if index (capacity n) third = 0 then
                tagLeveledChoice true false (evaluateZero (n, challengePk) rest)
              else rejectLeveledChoice
            else rejectLeveledChoice))]
        congr 1 with third : 1
        split_ifs <;> simp [hzero, PMF.map, Function.comp_def]
  · simp only [modLeveledAdversary, hpos, ↓reduceIte, ProbComp.eval_map, hzero, PMF.map_comp]
    unfold modLeveledChooseCoins
    simp only [hpos, ↓reduceIte, PMF.map, Function.comp_def]
    rw [BitString.uniformList_bind_split (3 * coins n) zeroCoins
      (fun _ rest => PMF.pure (tagLeveledChoice true false (evaluateZero (n, challengePk) rest))),
      PMF.bind_const]

/-- The original modular dispatch is native polynomial time using binary remainders and
unary caps. The zero-link callback supplies its own already-certified actual replay. -/
@[fun_prop] theorem computableInPolyTime_modLeveledChooseCoins
    {evaluateKey : ℕ → List Bool → List Bool × List Bool}
    {evaluateZero : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool}
    (hkey : ComputableInPolyTime (fun (n, tape) => evaluateKey n tape)
      (encPair encUnary encBits) (encPair encBits encBits))
    (hzero : ComputableInPolyTime (fun (input, tape) => evaluateZero input tape)
      (encPair (encPair encUnary encBits) encBits) (encPair (encPair encBool encBool) encBits))
    {α : Type} {input : α ↪ List Bool} {n indexCoins depth capacity keyCoins : α → ℕ}
    {challengePk tape : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hindexCoins : ComputableInPolyTime indexCoins input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hcapacity : ComputableInPolyTime capacity input encUnary)
    (hkeyCoins : ComputableInPolyTime keyCoins input encUnary)
    (hpk : ComputableInPolyTime challengePk input encBits)
    (htape : ComputableInPolyTime tape input encBits) :
    ComputableInPolyTime (fun a => modLeveledChooseCoins evaluateKey evaluateZero (n a)
      (indexCoins a) (depth a) (capacity a) (keyCoins a) (challengePk a) (tape a))
      input (encPair (encPair encBool encBool) encBits) := by
  have hhop := ComputableInPolyTime.binary_min_unary' (ComputableInPolyTime.const 3)
    (ComputableInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.bitsBinaryValue.comp (htape.bitsTakeWithInput hindexCoins)).prod
        (ComputableInPolyTime.const 3)))
  have hremaining := htape.bitsDropWithInput hindexCoins
  have hrest := hremaining.bitsDropWithInput hindexCoins
  have hreverse := ComputableInPolyTime.binary_min_unary' hdepth
    (ComputableInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.bitsBinaryValue.comp
        (hremaining.bitsTakeWithInput hindexCoins)).prod
          (ComputableInPolyTime.unary_to_binary.comp hdepth)))
  have hbit := ComputableInPolyTime.binary_min_unary' hcapacity
    (ComputableInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.bitsBinaryValue.comp (hrest.bitsTakeWithInput hindexCoins)).prod
        (ComputableInPolyTime.unary_to_binary.comp hcapacity)))
  have hlink : ComputableInPolyTime (fun a => Scheme.chooseModLinkCoins evaluateKey (n a)
      (indexCoins a) (keyCoins a) (depth a) (capacity a) (challengePk a)
      (((tape a).drop (indexCoins a)).take (2 * indexCoins a + depth a * keyCoins a)))
      input (encPair (encPair encBool encBool) encBits) := by
    apply Scheme.computableInPolyTime_chooseModLinkCoins hkey <;> fun_prop
  have hzeroActive := hzero.comp ((hn.prod hpk).prod (hrest.bitsDropWithInput hindexCoins))
  have hzeroFallback := hzero.comp ((hn.prod hpk).prod
    (htape.bitsDropWithInput (show ComputableInPolyTime (fun a => 3 * indexCoins a)
      input encUnary by fun_prop)))
  unfold modLeveledChooseCoins
  apply ComputableInPolyTime.ite_decide
  · fun_prop
  · apply ComputableInPolyTime.ite_decide
    · fun_prop
    · dsimp only [tagLeveledChoice]; fun_prop
    · apply ComputableInPolyTime.ite_decide
      · fun_prop
      · dsimp only [tagLeveledChoice, swapLeveledChoice]; fun_prop
      · apply ComputableInPolyTime.ite_decide
        · fun_prop
        · apply ComputableInPolyTime.ite_decide
          · fun_prop
          · dsimp only [tagLeveledChoice]; fun_prop
          · exact .const _
        · exact .const _
  · dsimp only [tagLeveledChoice]; fun_prop

end Cslib.Crypto.Homomorphic.Leveled
