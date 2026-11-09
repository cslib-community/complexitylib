/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.GuessCoinTape
public import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.GuessSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.PMF.Bind

/-!
# Supported guessing budgets from native strict PPT

Component replay laws are used only at proved input-length bounds. In particular, the supplied
challenge must fit the encryption bound; an encryption-supported challenge satisfies it. The
saved-state correlation from adaptive message selection is preserved throughout the game.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.eval_modLinkAdversary_guess_eq_map_coins_of_bounds`: actual
  modular guessing replay from bounded component inputs.
* `Cslib.Crypto.Homomorphic.Scheme.exists_modLinkAdversary_guess_coin_evaluator`: native replay
  and a polynomial composite coin budget from strict-PPT components.
-/

public section

namespace Cslib.Crypto.Homomorphic.Scheme

open Probability Turing.MultiTapeTM

/-- The original supported guess uses only bounded keys, artifacts, states and tagged
ciphertexts. All component laws are restricted to these bounds; no globally fixed-n replay law
is assumed. The challenge-length premise is discharged by encryption support in the native
application. -/
theorem eval_modLinkAdversary_guess_eq_map_coins_of_bounds (E : Scheme)
    (adversary : Encryption.Adversary) (coins depth capacity : ℕ → ℕ)
    (evaluateChoose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (evaluateEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (evaluateGuess : (ℕ × List Bool × List Bool) → List Bool → Bool)
    (bit : Bool) (n pkBound ctBound chooseCoins guessCoins : ℕ)
    (target : List Bool × List Bool) (challenge : List Bool)
    (choice : (Bool × Bool) × List Bool)
    (hkey : ∀ key ∈ (ProbComp.eval (E.keyGen n)).support,
      key.1.length ≤ pkBound ∧ key.2.length ≤ capacity n)
    (htarget : target ∈ (ProbComp.eval (E.keyGen n)).support)
    (hchoice : choice ∈ (ProbComp.eval ((E.modLinkAdversary coins depth capacity
      (Leveled.publicKeyGame E adversary bit)).choose n target.1)).support)
    (hchallenge : challenge.length ≤ ctBound)
    (hencrypt : ∀ pk, pk.length ≤ pkBound → ∀ message,
      ProbComp.eval (E.encrypt n pk message) =
        (BitString.uniformList ctBound).map (evaluateEncrypt (n, pk, message)) ∧
      ∀ ciphertext ∈ (ProbComp.eval (E.encrypt n pk message)).support,
        ciphertext.length ≤ ctBound)
    (hchoose : ∀ artifact,
      (Leveled.encPublicKey artifact).length ≤
        Leveled.publicKeyLengthBound (depth n) (capacity n) pkBound ctBound →
      ProbComp.eval (adversary.choose n (Leveled.encPublicKey artifact)) =
        (BitString.uniformList chooseCoins).map
          (evaluateChoose (n, Leveled.encPublicKey artifact)) ∧
      ∀ chosen ∈ (ProbComp.eval (adversary.choose n (Leveled.encPublicKey artifact))).support,
        chosen.2.length ≤ chooseCoins)
    (hguess : ∀ state ciphertext, state.length ≤ chooseCoins → ciphertext.length ≤ ctBound + 1 →
      ProbComp.eval (adversary.guess n state ciphertext) =
        (BitString.uniformList guessCoins).map (evaluateGuess (n, state, ciphertext))) :
    ProbComp.eval ((E.modLinkAdversary coins depth capacity
      (Leveled.publicKeyGame E adversary bit)).guess n choice.2 challenge) =
      (BitString.uniformList (Leveled.leveledGuessCoinBudget (depth n) (capacity n)
        ctBound chooseCoins guessCoins)).map
        (guessLinkCoins evaluateEncrypt
          (Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess bit
            chooseCoins ctBound) n ctBound (capacity n) choice.2 challenge) := by
  rcases E.modLinkAdversary_choose_support coins depth capacity _ n target.1 choice hchoice
    with rfl | ⟨before, predecessor, after, cut, hlength, hkeys, _, hcut, rfl⟩
  · simp [modLinkAdversary, rejectLinkChoice, ProbComp.eval_pure,
      PMF.map, Function.comp_def, guessLinkCoins]
  let replacement := (target.1, List.replicate predecessor.2.length false)
  have hparticipants : ∀ key ∈ before ++ predecessor :: replacement :: after,
      key.1.length ≤ pkBound ∧ key.2.length ≤ capacity n := by
    intro key hmem
    simp only [List.mem_append, List.mem_cons] at hmem
    rcases hmem with h | rfl | rfl | h
    · exact hkey _ (hkeys _ (by simp [h]))
    · exact hkey _ (hkeys _ (by simp))
    · exact ⟨(hkey target htarget).1,
        by simpa [replacement] using (hkey predecessor (hkeys _ (by simp))).2⟩
    · exact hkey _ (hkeys _ (by simp [h]))
  have hpublic (links) (hlinks : links ∈ (ProbComp.eval
      (E.spliceEncryptedKeyLink n before predecessor replacement after cut challenge)).support) :
      (Leveled.encPublicKey
        ((before ++ predecessor :: replacement :: after).map Prod.fst, links)).length ≤
        Leveled.publicKeyLengthBound (depth n) (capacity n) pkBound ctBound := by
    rw [← hlength]
    exact Leveled.length_encPublicKey_support_splice_le hcut hparticipants
      (fun key hmem message => (hencrypt key.1 (hparticipants key hmem).1 message).2)
      hchallenge hlinks
  have hfirst :
      (((before ++ predecessor :: replacement :: after).map Prod.fst).getD 0 []).length ≤
        pkBound := by
    cases before with
    | nil => simpa using (hparticipants predecessor (by simp)).1
    | cons first rest => simpa using (hparticipants first (by simp)).1
  have htest (links) (hlinks : links ∈ (ProbComp.eval
      (E.spliceEncryptedKeyLink n before predecessor replacement after cut challenge)).support) :
      ProbComp.eval (Leveled.publicKeyGame E adversary bit n
        ((before ++ predecessor :: replacement :: after).map Prod.fst, links)) =
      (BitString.uniformList (chooseCoins + (ctBound + guessCoins))).map
        (Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess bit
          chooseCoins ctBound
          (n, (before ++ predecessor :: replacement :: after).map Prod.fst, links)) := by
    have hchosen := hchoose _ (hpublic links hlinks)
    apply Leveled.eval_publicKeyGame_eq_map_coins E adversary evaluateChoose evaluateEncrypt
      evaluateGuess bit n chooseCoins ctBound guessCoins _ hchosen.1
        (fun message => (hencrypt _ hfirst message).1)
    intro chosen hchosenSupport ciphertext hciphertext
    apply hguess chosen.2 (false :: ciphertext) (hchosen.2 chosen hchosenSupport)
    have hct := (hencrypt _ hfirst _).2 ciphertext hciphertext
    simpa using Nat.add_le_add_right hct 1
  have hpred := (hkey predecessor (hkeys predecessor (by simp))).2
  have hpositive : 1 ≤ depth n * capacity n :=
    Nat.mul_le_mul (by omega : 1 ≤ depth n) (by omega : 1 ≤ capacity n)
  have hsize : ((before.length + after.length + 1) * capacity n - 1) * ctBound +
      (chooseCoins + (ctBound + guessCoins)) =
      Leveled.leveledGuessCoinBudget (depth n) (capacity n) ctBound chooseCoins guessCoins := by
    rw [hlength]
    have hsum := Nat.sub_add_cancel hpositive
    calc
      _ = ((depth n * capacity n - 1) + 1) * ctBound + chooseCoins + guessCoins := by ring
      _ = _ := by rw [hsum]; rfl
  simpa only [modLinkAdversary, hsize] using
    E.eval_guessLink_active_eq_map_coins (Leveled.publicKeyGame E adversary bit)
      evaluateEncrypt
      (Leveled.publicKeyGameCoins evaluateChoose evaluateEncrypt evaluateGuess bit
        chooseCoins ctBound) n ctBound (chooseCoins + (ctBound + guessCoins)) (capacity n)
      before predecessor target.1 after cut challenge hcut
      (fun key hmem => (hkey key (hkeys key hmem)).2)
      (fun pk hmem message => (hencrypt pk (by
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact (hkey target htarget).1
        · obtain ⟨key, hkeyMem, rfl⟩ := List.mem_map.mp hmem
          exact (hkey key (hkeys key hkeyMem)).1) message).1)
      htest

/-- Native strict-PPT components supply the supported guessing replay and its polynomial
composite seed budget. The target key and challenge come from the original key-generation and
encryption supports, and the saved choice comes from the original modular reduction. Thus no
security-parameter-only size bound is imposed on arbitrary attacker-supplied strings. This is
an execution-level coin theorem, not Gentry's multiplicative machine-runtime comparison. -/
theorem exists_modLinkAdversary_guess_coin_evaluator {E : Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) E.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun (n, pk, bit) => E.encrypt n pk bit))
    {adversary : Encryption.Adversary} (hadversary : adversary.IsPPT)
    {width coins budget capacity : ℕ → ℕ}
    (hwidth : ∀ n keys, keys ∈ (ProbComp.eval (E.keyGen n)).support → keys.2.length = width n)
    (hcapacity_le : ∀ n, width n ≤ capacity n)
    (hbudget : ComputableInPolyTime budget encUnary encUnary)
    (hcapacity : ComputableInPolyTime capacity encUnary encUnary) (bit : Bool) :
    ∃ (encCoins chooseCoins guessCoins : ℕ → ℕ)
      (evaluate : (ℕ × List Bool × List Bool) → List Bool → Bool),
      ComputableInPolyTime encCoins encUnary encUnary ∧
      ComputableInPolyTime chooseCoins encUnary encUnary ∧
      ComputableInPolyTime guessCoins encUnary encUnary ∧
      ComputableInPolyTime (fun (input, tape) => evaluate input tape)
        (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool ∧
      PolynomiallyBounded (fun n => Leveled.leveledGuessCoinBudget (2 * budget n) (capacity n)
        (encCoins n) (chooseCoins n) (guessCoins n)) ∧
      ∀ n target, target ∈ (ProbComp.eval (E.keyGen n)).support →
        ∀ choice, choice ∈ (ProbComp.eval ((E.modLinkAdversary coins (fun n => 2 * budget n)
          capacity (Leveled.publicKeyGame E adversary bit)).choose n target.1)).support →
        ∀ message challenge, challenge ∈ (ProbComp.eval (E.encrypt n target.1 message)).support →
        ProbComp.eval ((E.modLinkAdversary coins (fun n => 2 * budget n) capacity
          (Leveled.publicKeyGame E adversary bit)).guess n choice.2 challenge) =
          (BitString.uniformList (Leveled.leveledGuessCoinBudget (2 * budget n) (capacity n)
            (encCoins n) (chooseCoins n) (guessCoins n))).map
              (evaluate (n, choice.2, challenge)) := by
  obtain ⟨c_kg, d_kg, c_enc, d_enc, c_ch, d_ch, c_gu, d_gu, _, evalEncrypt, evalChoose, evalGuess,
    _, hevalEncrypt, hevalChoose, hevalGuess, _, hkeys, henc, _, hchoose, hguess, _, hpoly, _, _⟩ :=
      Leveled.exists_leveledAdversary_overhead hkeyGen hencrypt hadversary hwidth hcapacity_le
        hbudget hcapacity
  let pkBound := fun n => c_kg * (n + 1) ^ d_kg
  let ctBound := fun n => c_enc * (2 * n + 2 * pkBound n + 5) ^ d_enc
  let pubLen := fun n =>
    Leveled.publicKeyLengthBound (2 * budget n) (capacity n) (pkBound n) (ctBound n)
  let chooseCoins := fun n => c_ch * (2 * n + pubLen n + 2) ^ d_ch
  let guessCoins := fun n => c_gu * (2 * n + 2 * chooseCoins n + ctBound n + 4) ^ d_gu
  let evaluate := fun (n, state, challenge) tape => guessLinkCoins evalEncrypt
    (fun input seed => Leveled.publicKeyGameCoins evalChoose evalEncrypt evalGuess bit
      (chooseCoins input.1) (ctBound input.1) input seed) n (ctBound n) (capacity n)
      state challenge tape
  have hctBound : ComputableInPolyTime ctBound encUnary encUnary := by
    dsimp only [ctBound, pkBound]
    fun_prop
  have hchooseCoins : ComputableInPolyTime chooseCoins encUnary encUnary := by
    dsimp only [chooseCoins, pubLen, Leveled.publicKeyLengthBound, ctBound, pkBound]
    fun_prop
  have hguessCoins : ComputableInPolyTime guessCoins encUnary encUnary := by
    dsimp only [guessCoins]
    fun_prop
  refine ⟨ctBound, chooseCoins, guessCoins, evaluate, hctBound, hchooseCoins, hguessCoins,
    ?_, hpoly, ?_⟩
  · apply computableInPolyTime_modLinkGuessCoins hevalChoose hevalEncrypt hevalGuess bit
      hchooseCoins hctBound hcapacity
    all_goals fun_prop
  · intro n target htarget choice hchoice message challenge hchallenge
    have htargetLength := (hkeys n target htarget).1
    have hchallengeLength := (henc n target.1 message htargetLength).2 challenge hchallenge
    have hlaw := E.eval_modLinkAdversary_guess_eq_map_coins_of_bounds adversary coins
      (fun n => 2 * budget n) capacity evalChoose evalEncrypt evalGuess bit n (pkBound n)
      (ctBound n) (chooseCoins n) (guessCoins n) target challenge choice (hkeys n) htarget
      hchoice hchallengeLength
      (fun pk hpk message => henc n pk message hpk)
      (fun artifact hlen => hchoose n (Leveled.encPublicKey artifact) hlen) (hguess n)
    rw [hlaw]
    congr 1

end Cslib.Crypto.Homomorphic.Scheme
