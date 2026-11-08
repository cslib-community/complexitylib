/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Homomorphic.BitEncryption.Time
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.GameCoinTape
import CslibFrontier.Crypto.Computational.Homomorphic.Leveled.FlatSecurity
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Concrete link guessing tapes

Randomized bit encryption, adaptive choice, and guessing use separate one-bit seeds. The
fixture instantiates the actual supported-choice theorem without any security assumption.
Explicit replays check both boundary cuts, padding, repeated keys, and the supplied challenge.
Complete-game clients also inspect all selector branches, the message swap, modulo-three bias
and the zero-range fallback, which still calls the adversary.
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

-- The common encryption envelope covers both its one sampled bit and its two-bit output.
private def paddedEncrypt (input : ℕ × List Bool × Bool) (tape : List Bool) : List Bool :=
  evaluateEncrypt input (tape.take 1)

private def zeroReplay (input : ℕ × List Bool) (tape : List Bool) :
    (Bool × Bool) × List Bool :=
  Leveled.zeroLinkChooseCoins (fun _ _ => key) paddedEncrypt evaluateChoose input.1
    2 2 0 2 input.2 tape

-- All three branches retain their tags, and selectors zero and three share the first branch.
example : ([[false, false], [false, true], [true, false], [true, true]].map fun selector =>
    (Leveled.modLeveledChooseCoins (fun _ _ => key) zeroReplay 0 2 2 2 0 key.1
      (selector ++ List.replicate 13 false)).2.take 2) =
    [[false, false], [false, true], [true, false], [false, false]] := by decide

-- The true-world link branch swaps the predecessor's true message with false.
example : (Leveled.modLeveledChooseCoins (fun _ _ => key) zeroReplay 0 2 2 2 0 key.1
    ([false, true] ++ List.replicate 13 false)).1 = (false, true) := by decide

-- A zero-link hop with a nonzero thinning index rejects, rather than running the payload.
example : Leveled.modLeveledChooseCoins (fun _ _ => key) zeroReplay 0 2 2 2 0 key.1
    ([true, false, false, true] ++ List.replicate 11 false) = Leveled.rejectLeveledChoice := by
  decide

-- The link branch ignores the encryption/choice padding after its selector and key blocks.
example : Leveled.modLeveledChooseCoins (fun _ _ => key) zeroReplay 0 2 2 2 0 key.1
    (List.replicate 6 false ++ List.replicate 9 true) =
    Leveled.modLeveledChooseCoins (fun _ _ => key) zeroReplay 0 2 2 2 0 key.1
      (List.replicate 15 false) := by decide

-- The complete game law has no supplied-context support premise. Both challenge worlds use
-- the same 24-bit allocation: 12 choice bits, two challenge bits and ten guessing bits.
example (bit : Bool) (n : ℕ) : ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
    (Leveled.modLeveledAdversary fixture (fun _ => 1) (fun _ => 2) (fun _ => 2) adversary)
      bit n) =
    (BitString.uniformList 24).map (Leveled.modLeveledGameCoins (fun _ _ => key) paddedEncrypt
      evaluateChoose evaluateGuess (fun _ => 1) (fun _ => 2) (fun _ => 2) (fun _ => 0)
      (fun _ => 2) (fun _ => 1) (fun _ => 1) bit n) := by
  apply Leveled.eval_game_modLeveledAdversary_eq_map_coins fixture adversary
    (fun _ _ => key) paddedEncrypt evaluateChoose evaluateGuess
    (fun _ => 1) (fun _ => 2) (fun _ => 2) (fun _ => 0) (fun _ => 2)
    (fun _ => 1) (fun _ => 1) bit n 1
  · simp [fixture, ProbComp.eval_pure, PMF.map]
  · intro generated hgenerated
    simp only [fixture, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hgenerated
    subst generated
    decide
  · intro pk _ message
    refine ⟨?_, ?_⟩
    · rw [encrypt_law, ← BitString.uniformList_take (n := 2) (k := 1) (by decide), PMF.map_comp]
      rfl
    · intro ciphertext hct
      simp only [fixture, ProbComp.eval_map, BitString.eval_sampleList,
        PMF.mem_support_map_iff] at hct
      obtain ⟨seed, hseed, rfl⟩ := hct
      simp [evaluateEncrypt, BitString.length_of_mem_support_uniformList hseed]
  · intro artifact _
    refine ⟨choose_law n artifact, ?_⟩
    intro chosen hchosen
    simp only [adversary, ProbComp.eval_map, BitString.eval_sampleList,
      PMF.mem_support_map_iff] at hchosen
    obtain ⟨seed, hseed, rfl⟩ := hchosen
    exact (BitString.length_of_mem_support_uniformList hseed).le
  · intro state ciphertext _ _
    simp [adversary, ProbComp.eval_map, BitString.eval_sampleList]

example (bit : Bool) : ComputableInPolyTime (fun p : ℕ × List Bool =>
    Leveled.modLeveledGameCoins (fun _ _ => key) paddedEncrypt evaluateChoose evaluateGuess
      (fun _ => 1) (fun _ => 2) (fun _ => 2) (fun _ => 0)
      (fun _ => 2) (fun _ => 1) (fun _ => 1) bit p.1 p.2)
      (encPair encUnary encBits) encBool := by
  apply Leveled.computableInPolyTime_modLeveledGameCoins
  · exact .const _
  · unfold paddedEncrypt evaluateEncrypt
    fun_prop
  · unfold evaluateChoose
    fun_prop
  · unfold evaluateGuess
    fun_prop
  all_goals fun_prop

-- A probe that reads the plaintext behind the false ciphertext tag detects accidental
-- rejection of the unified zero-range fallback. It must return the challenge world itself.
private def fallbackProbe : Encryption.Adversary where
  choose _ _ := pure ((false, true), [])
  guess _ _ ciphertext := pure (ciphertext.getD 1 false)

example (bit : Bool) (n : ℕ) : ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
    (Leveled.modLeveledAdversary fixture (fun _ => 7) (fun _ => 0) (fun _ => 2) fallbackProbe)
      bit n) = PMF.pure bit := by
  cases bit <;> simp [Encryption.game, Encryption.gameOn, fixture, key, fallbackProbe,
    Leveled.modLeveledAdversary, Leveled.leveledAdversary, Leveled.zeroLinkAdversary,
    Leveled.tagLeveledChoice, Scheme.encryptZeroKeyLinks, evaluateEncrypt,
    ProbComp.eval_map, BitString.eval_sampleList, PMF.map, Function.comp_def]

example (bit : Bool) (n : ℕ) : ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
    (Leveled.modLeveledAdversary fixture (fun _ => 7) (fun _ => 2) (fun _ => 0) fallbackProbe)
      bit n) = PMF.pure bit := by
  cases bit <;> simp [Encryption.game, Encryption.gameOn, fixture, key, fallbackProbe,
    Leveled.modLeveledAdversary, Leveled.leveledAdversary, Leveled.zeroLinkAdversary,
    Leveled.tagLeveledChoice, evaluateEncrypt, ProbComp.eval_bind,
    ProbComp.eval_map, BitString.eval_sampleList, PMF.map, Function.comp_def]

-- The same nonconstant callback has a native linear time and workspace certificate.
private theorem evaluateEncrypt_native : ComputableInO
    (fun p : (ℕ × List Bool × Bool) × List Bool => evaluateEncrypt p.1 p.2)
    (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits
    (fun p => (encPair (encPair encUnary (encPair encBits encBool)) encBits p).length)
    (fun p => (encPair (encPair encUnary (encPair encBits encBool)) encBits p).length) := by
  have hinput := ComputableInO.fst (encPair encUnary (encPair encBits encBool)) encBits
  have hseed := ComputableInO.snd (encPair encUnary (encPair encBits encBool)) encBits
  exact (hinput.snd'.snd'.append hseed (fun _ => rfl)).mono 2
    (fun _ => by omega) (fun _ => by omega)

-- The nonce width is part of the actual program family, including width zero.
private noncomputable def widthFixture : Scheme :=
  { fixture with
    encrypt n pk bit := evaluateEncrypt (n, pk, bit) <$> BitString.sampleList n }

-- Every raw tuple is covered: no hypothesis about tape length is imposed. The callback's
-- explicit clock is linear in the row width; retained output uses its separate support size.
example : ∃ P : ℕ → ℕ, PolynomiallyBounded P ∧ ComputableInO
    (fun p : ℕ × List Bool × List Bool =>
      Scheme.encryptBitsCoins evaluateEncrypt p.1 p.1 [] p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) (encList encBits)
    (fun p => P (encPair encUnary (encPair encBits encBits) p).length +
      (p.2.1.length + 1) * (5 * p.1 + 7 + p.2.1.length * (p.1 + 2)))
    (fun p => P (encPair encUnary (encPair encBits encBits) p).length +
      (5 * p.1 + 7) + p.2.1.length * (p.1 + 2)) := by
  obtain ⟨P, hP, h⟩ := Scheme.exists_encryptBitsCoins_time_bound
    (n := fun p : ℕ × List Bool × List Bool => p.1) (encCoins := fun p => p.1)
    (pk := fun _ => []) (bits := fun p => p.2.1) (tape := fun p => p.2.2)
    (input := encPair encUnary (encPair encBits encBits))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  refine ⟨P, hP, ?_⟩
  have law (p : ℕ × List Bool × List Bool) (bit : Bool) (_ : bit ∈ p.2.1) :
      ProbComp.eval (widthFixture.encrypt p.1 [] bit) =
        (BitString.uniformList p.1).map (evaluateEncrypt (p.1, [], bit)) := by
    simp [widthFixture, ProbComp.eval_map, BitString.eval_sampleList]
  have hrow (p : ℕ × List Bool × List Bool) (row : Bool × List Bool)
      (hr : row ∈ p.2.1.zip (BitString.listRows p.2.1.length p.1 p.2.2)) :
      (encPair (encPair encUnary (encPair encBits encBool)) encBits
        ((p.1, [], row.1), row.2)).length ≤ 5 * p.1 + 7 := by
    have hs := BitString.length_of_mem_listRows (List.of_mem_zip hr).2
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      encBool_apply, List.length_singleton, List.length_nil]
    omega
  have hc (p : ℕ × List Bool × List Bool) (bit : Bool) (hb : bit ∈ p.2.1)
      (ciphertext : List Bool)
      (hc : ciphertext ∈ (ProbComp.eval (widthFixture.encrypt p.1 [] bit)).support) :
      ciphertext.length ≤ p.1 + 1 := by
    rw [law p bit hb] at hc
    obtain ⟨seed, hseed, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
    have := BitString.length_of_mem_support_uniformList hseed
    simp only [evaluateEncrypt, List.length_cons]
    omega
  simpa only [Nat.add_assoc] using h widthFixture evaluateEncrypt _ _ evaluateEncrypt_native
    law (fun p => 5 * p.1 + 7) (fun p => 5 * p.1 + 7) (fun p => p.1 + 1) hrow hrow hc

-- The ciphertext-size premise has content: this supported ciphertext does not fit one bit.
example : [false, true] ∈ (ProbComp.eval (fixture.encrypt 0 [] false)).support ∧
    ¬ [false, true].length ≤ 1 := by
  constructor
  · rw [encrypt_law]
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨[true], BitString.mem_support_uniformList_iff.mpr rfl, rfl⟩
  · decide

-- Short tapes supply false padding independently to every missing row.
example : Scheme.encryptBitsCoins evaluateEncrypt 0 2 [] [true, false] [true] =
    [[true, true, false], [false, false, false]] := by decide

-- Extra raw bits after the allocated rows are ignored.
example : Scheme.encryptBitsCoins evaluateEncrypt 0 1 [] [false, false] [false, true, true] =
    [[false, false], [false, true]] := by decide

-- Width zero retains every plaintext bit, while an empty plaintext list returns no ciphertexts.
example : Scheme.encryptBitsCoins evaluateEncrypt 0 0 [] [true, false] [true] =
    [[true], [false]] := by decide

example (width : ℕ) (tape : List Bool) :
    Scheme.encryptBitsCoins evaluateEncrypt 0 width [] [] tape = [] := by
  simp [Scheme.encryptBitsCoins]

-- At DC=1, all three successful indices select real callbacks; there is no zero-hop thinning.
example (n : ℕ) (pk : List Bool) :
    ((ProbComp.eval (Leveled.flatLeveledChoice fixture (fun _ => 1) (fun _ => 1)
      fallbackProbe n pk 0)).map (fun choice => choice.2.take 2)) = PMF.pure [false, false] ∧
    ((ProbComp.eval (Leveled.flatLeveledChoice fixture (fun _ => 1) (fun _ => 1)
      fallbackProbe n pk 1)).map (fun choice => choice.2.take 2)) = PMF.pure [false, true] ∧
    ((ProbComp.eval (Leveled.flatLeveledChoice fixture (fun _ => 1) (fun _ => 1)
      fallbackProbe n pk 2)).map (fun choice => choice.2.take 2)) = PMF.pure [true, false] := by
  simp [Leveled.flatLeveledChoice, Leveled.tagLeveledChoice, Leveled.swapLeveledChoice,
    ProbComp.eval_map, PMF.map, Function.comp_def]

-- At DC=0, the successful singleton index executes the actual zero-link choice.
example (n : ℕ) (pk : List Bool) :
    Leveled.flatLeveledChoice fixture (fun _ => 0) (fun _ => 2) fallbackProbe n pk 0 =
      Leveled.tagLeveledChoice true false <$>
        (Leveled.zeroLinkAdversary fixture (fun _ => 0) fallbackProbe).choose n pk := by
  simp [Leveled.flatLeveledChoice]

end ComplexityTests.Crypto.LeveledGuessCoinTape
