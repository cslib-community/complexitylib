/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Leveled.Bootstrapping
import Complexity.Crypto.Computational.Homomorphic.Leveled.ExactSecurity
import Complexity.Tactic.PPT

/-!
# Tests for security of the actual leveled encryption algorithms

A stateful adversary chooses messages from the decoded full public artifact, including an
encrypted-link nonce, and saves the entire serialized artifact. The random two-bit fixture
retains encryption randomness and exposes plaintexts, so its games test simulation, not security.

A separate constant-encryption fixture inhabits the security theorem's hypotheses. It cannot
decrypt a true message correctly: satisfying the security predicate alone does not make an
encryption scheme correct.
-/

namespace ComplexityTests.Crypto.LeveledSecurity

open Cslib Cslib.Circuits Cslib.Crypto Cslib.Crypto.Homomorphic Cslib.Probability
open Turing.MultiTapeTM Leveled

private noncomputable def fixture : Scheme where
  keyGen _ := do
    let first ← ProbComp.uniform Bool
    let second ← ProbComp.uniform Bool
    pure ([first], [first, second])
  encrypt _ pk bit := do
    let nonce ← ProbComp.uniform Bool
    pure [pk.headD false, bit, nonce]
  decrypt _ _ ciphertext := ciphertext.getD 1 false
  evaluate _ _ _ _ := pure []
  permitted _ _ := False

private theorem keys_supported (n : ℕ) (key : List Bool × List Bool) :
    key ∈ (ProbComp.eval (fixture.keyGen n)).support ↔
      ∃ first second : Bool, key = ([first], [first, second]) := by
  simp only [fixture, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, PMF.uniformOfFintype,
    PMF.mem_support_uniformOfFinset_iff, Finset.mem_univ, true_and]

private theorem secret_width (n : ℕ) (key : List Bool × List Bool)
    (hkey : key ∈ (ProbComp.eval (fixture.keyGen n)).support) : key.2.length = 2 := by
  obtain ⟨first, second, rfl⟩ := (keys_supported n key).1 hkey
  rfl

/-- Select a message using the initial public bit and a nonce in the first encrypted link. -/
private def stateBit (word : List Bool) : Bool :=
  let artifact := publicKeyDecoder.decode word
  (artifact.1.getD 0 []).getD 0 false ^^
    (((artifact.2.getD 0 []).getD 1 []).getD 2 false)

/-- Save the exact full artifact; guessing checks the fresh tag and decodes the exposed bit. -/
private def adversary : Encryption.Adversary where
  choose _ word := pure ((stateBit word, !(stateBit word)), word)
  guess _ state ciphertext :=
    pure (!(ciphertext.getD 0 true) && (ciphertext.getD 2 false ^^ stateBit state))

-- A changed encrypted-link nonce changes the selected messages while public keys stay fixed.
example (nonce : Bool) :
    adversary.choose 0 (encPublicKey
      ([[false], [true], [false]],
        [[[true, false, false], [true, false, nonce]],
          [[false, false, true], [false, false, false]]])) =
      pure ((nonce, !nonce), encPublicKey
        ([[false], [true], [false]],
          [[[true, false, false], [true, false, nonce]],
            [[false, false, true], [false, false, false]]])) := by
  simp [adversary, stateBit]

-- Every complete artifact is retained through both stages, including the depth-zero artifact.
private theorem eval_publicKeyGame (bit : Bool) (n : ℕ)
    (artifact : List (List Bool) × List (List (List Bool))) :
    ProbComp.eval (publicKeyGame fixture adversary bit n artifact) = PMF.pure bit := by
  cases hstate : stateBit (encPublicKey artifact) <;> cases bit <;>
    simp [publicKeyGame, adversary, fixture, hstate, PMF.map, Function.comp_def]

-- The zero-link simulator preserves the chosen messages, saved artifact and ciphertext tag.
private theorem eval_zeroLinkGame (depth : ℕ → ℕ) (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (zeroLinkAdversary fixture depth adversary) bit n) = PMF.pure bit := by
  rw [eval_zeroLinkAdversary fixture depth adversary bit n 2 (secret_width n)]
  simp [eval_publicKeyGame]

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (zeroLinkAdversary fixture (fun _ => 0) adversary) bit n) = PMF.pure bit :=
  eval_zeroLinkGame (fun _ => 0) bit n

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (zeroLinkAdversary fixture (fun _ => 2) adversary) bit n) = PMF.pure bit :=
  eval_zeroLinkGame (fun _ => 2) bit n

-- The actual serialized leveled game agrees at budgets zero and one (zero and two links).
example (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game (fun n => keyGen fixture n 0) (encrypt fixture)
      adversary bit n) = PMF.pure bit := by
  rw [eval_game_keyGen fixture (fun _ => 0) adversary bit n]
  simp [eval_publicKeyGame]

example (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game (fun n => keyGen fixture n 1) (encrypt fixture)
      adversary bit n) = PMF.pure bit := by
  rw [eval_game_keyGen fixture (fun _ => 1) adversary bit n]
  simp [eval_publicKeyGame]

private theorem keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) fixture.keyGen := by
  dsimp only [fixture]
  ppt

private theorem encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => fixture.encrypt p.1 p.2.1 p.2.2) := by
  dsimp only [fixture]
  ppt

private theorem stateBit_poly : ComputableInPolyTime stateBit encBits encBool := by
  have hcontext := publicKeyDecoder.computableInPolyTime
  dsimp only [encPublicKey] at hcontext
  have hpk := (ComputableInPolyTime.listGetD
    (encA := encBits) (encL := encList encBits) []).comp
      (hcontext.fst'.prod (ComputableInPolyTime.const 0))
  have hfirst := (ComputableInPolyTime.bitsGetD false).comp
    (hpk.prod (ComputableInPolyTime.const 0))
  have hlink := (ComputableInPolyTime.listGetD
    (encA := encList encBits) (encL := encList (encList encBits)) []).comp
      (hcontext.snd'.prod (ComputableInPolyTime.const 0))
  have hct := (ComputableInPolyTime.listGetD
    (encA := encBits) (encL := encList encBits) []).comp
      (hlink.prod (ComputableInPolyTime.const 1))
  have hnonce := (ComputableInPolyTime.bitsGetD false).comp
    (hct.prod (ComputableInPolyTime.const 2))
  unfold stateBit
  simpa only [Function.comp_def] using
    ComputableInPolyTime.bool_xor.comp (hfirst.prod hnonce)

attribute [local fun_prop] stateBit_poly

private theorem adversary_ppt : adversary.IsPPT := by
  constructor <;> dsimp only [adversary] <;> ppt

-- Both stages charge the full artifact and saved word. A nonconstant family is still uniform.
example : (zeroLinkAdversary fixture (fun _ => 0) adversary).IsPPT :=
  isPPT_zeroLinkAdversary encrypt_ppt adversary_ppt keyGen_ppt (by fun_prop)

example : (zeroLinkAdversary fixture (fun n => n + 2) adversary).IsPPT :=
  isPPT_zeroLinkAdversary encrypt_ppt adversary_ppt keyGen_ppt (by fun_prop)

example : (leveledAdversary fixture (fun n => 2 * (n + 1)) (fun _ => 2) adversary).IsPPT :=
  isPPT_leveledAdversary encrypt_ppt adversary_ppt keyGen_ppt (by fun_prop) (by fun_prop)

example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game (fun n => keyGen fixture n 1) (encrypt fixture)
        adversary false n))
      (ProbComp.eval (Encryption.game (fun n => keyGen fixture n 1) (encrypt fixture)
        adversary true n)) =
    4 * (dyadicSize (2 * 1) : NNReal) * dyadicSize 2 *
      Game.advantage
        (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
          (leveledAdversary fixture (fun _ => 2 * 1) (fun _ => 2) adversary) false n))
        (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
          (leveledAdversary fixture (fun _ => 2 * 1) (fun _ => 2) adversary) true n)) :=
  advantage_game_eq_leveledAdversary fixture (fun _ => 1) (fun _ => 2) adversary n 2
    (secret_width n) le_rfl

example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game (fun n => keyGen fixture n 1) (encrypt fixture)
        adversary false n))
      (ProbComp.eval (Encryption.game (fun n => keyGen fixture n 1) (encrypt fixture)
        adversary true n)) ≤
    16 * (2 * (1 : ℕ) + 1 : NNReal) * ((2 : ℕ) + 1) *
      Game.advantage
        (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
          (leveledAdversary fixture (fun _ => 2 * 1) (fun _ => 2) adversary) false n))
        (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
          (leveledAdversary fixture (fun _ => 2 * 1) (fun _ => 2) adversary) true n)) :=
  advantage_game_le_mul_leveledAdversary fixture (fun _ => 1) (fun _ => 2) adversary n 2
    (secret_width n) le_rfl

example (bit : Bool) : IsPPTOn (encPair encUnary encPublicKey) encBool
    (fun p => publicKeyGame fixture adversary bit p.1 p.2) :=
  isPPTOn_publicKeyGame encrypt_ppt adversary_ppt bit

/-- The deliberately degenerate encryption algorithm discards its message completely. -/
private noncomputable def forgetful : Scheme :=
  { fixture with
    encrypt := fun _ _ _ => pure []
    decrypt := fun _ _ _ => false }

private theorem forgetful_secure : Encryption.INDCPA forgetful.keyGen forgetful.encrypt := by
  intro opponent _
  have heq (n : ℕ) :
      ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt opponent false n) =
      ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt opponent true n) := by
    simp [Encryption.game, Encryption.gameOn, forgetful]
  simpa only [heq, Game.advantage_self] using negligible_zero

private theorem forgetful_encrypt_ppt :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => forgetful.encrypt p.1 p.2.1 p.2.2) := by
  dsimp only [forgetful]
  ppt

private def forgetfulCircuits : DecryptionCircuits forgetful (fun _ => 2) (fun _ => 0) where
  circuit _ := Circuit.oneGate (.const false) Fin.elim0
  correct _ _ _ _ _ := by simp [Circuit.eval_oneGate, Boolean.interpretation, forgetful]

-- The security premises are inhabited by actual native algorithms and a nonconstant budget.
example : Encryption.INDCPA (scheme forgetfulCircuits (fun n => n + 1)).keyGen
    (scheme forgetfulCircuits (fun n => n + 1)).encrypt :=
  indCPA_scheme forgetful_secure keyGen_ppt forgetful_encrypt_ppt secret_width
    (by fun_prop) forgetfulCircuits

-- Exact Gentry Theorem 4 reduction loss (without dyadicSize rounding) on the forgetful scheme.
example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game (scheme forgetfulCircuits (fun n => n + 1)).keyGen
        (scheme forgetfulCircuits (fun n => n + 1)).encrypt adversary false n))
      (ProbComp.eval (Encryption.game (scheme forgetfulCircuits (fun n => n + 1)).keyGen
        (scheme forgetfulCircuits (fun n => n + 1)).encrypt adversary true n)) =
    3 * (2 * ((n + 1 : ℕ) : NNReal)) * (2 : ℕ) *
      Game.advantage
        (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
          (exactLeveledAdversary forgetful (fun n => 2 * (n + 1)) (fun _ => 2) adversary)
          false n))
        (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
          (exactLeveledAdversary forgetful (fun n => 2 * (n + 1)) (fun _ => 2) adversary)
          true n)) :=
  advantage_scheme_eq_exactLeveledAdversary forgetfulCircuits (fun n => n + 1) (fun _ => 2)
    adversary n 2 (Nat.succ_pos n) (by decide) (secret_width n) le_rfl

-- Unattenuated three-hop decomposition via exactLinkAdversary and zeroLinkAdversary.
example (n : ℕ) :
    Game.advantage
      (ProbComp.eval (Encryption.game (scheme forgetfulCircuits (fun _ => 1)).keyGen
        (scheme forgetfulCircuits (fun _ => 1)).encrypt adversary false n))
      (ProbComp.eval (Encryption.game (scheme forgetfulCircuits (fun _ => 1)).keyGen
        (scheme forgetfulCircuits (fun _ => 1)).encrypt adversary true n)) ≤
    (2 * (1 : ℕ) : NNReal) * 2 *
      Game.advantage
        (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
          (forgetful.exactLinkAdversary (fun _ => 2 * 1) (fun _ => 2)
            (publicKeyGame forgetful adversary false)) false n))
        (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
          (forgetful.exactLinkAdversary (fun _ => 2 * 1) (fun _ => 2)
            (publicKeyGame forgetful adversary false)) true n)) +
    Game.advantage
      (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
        (zeroLinkAdversary forgetful (fun _ => 2 * 1) adversary) false n))
      (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
        (zeroLinkAdversary forgetful (fun _ => 2 * 1) adversary) true n)) +
    (2 * (1 : ℕ) : NNReal) * 2 *
      Game.advantage
        (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
          (forgetful.exactLinkAdversary (fun _ => 2 * 1) (fun _ => 2)
            (publicKeyGame forgetful adversary true)) false n))
        (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
          (forgetful.exactLinkAdversary (fun _ => 2 * 1) (fun _ => 2)
            (publicKeyGame forgetful adversary true)) true n)) :=
  advantage_scheme_le_exactLinkAdversary_add_zeroLinkAdversary forgetfulCircuits (fun _ => 1)
    (fun _ => 2) adversary n 2 (secret_width n) le_rfl

-- Strict-PPT sampleModNat reduction and concrete advantage bound with O(1 / 2 ^ n) tail.
example : (modLeveledAdversary fixture (fun n => 2 * n) (fun n => 2 * (n + 1))
    (fun _ => 2) adversary).IsPPT :=
  isPPT_modLeveledAdversary_two_mul keyGen_ppt encrypt_ppt adversary_ppt
    (by fun_prop) (by fun_prop)

example (n : ℕ) (htail : 3 + 2 * 1 + 2 ≤ 2 ^ n) :
    Game.advantage
      (ProbComp.eval (Encryption.game (scheme forgetfulCircuits (fun _ => 1)).keyGen
        (scheme forgetfulCircuits (fun _ => 1)).encrypt adversary false n))
      (ProbComp.eval (Encryption.game (scheme forgetfulCircuits (fun _ => 1)).keyGen
        (scheme forgetfulCircuits (fun _ => 1)).encrypt adversary true n)) ≤
    3 * (2 * (1 : ℕ) : NNReal) * 2 *
      (Game.advantage
        (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
          (modLeveledAdversary forgetful (fun n => 2 * n) (fun _ => 2 * 1) (fun _ => 2) adversary)
          false n))
        (ProbComp.eval (Encryption.game forgetful.keyGen forgetful.encrypt
          (modLeveledAdversary forgetful (fun n => 2 * n) (fun _ => 2 * 1) (fun _ => 2) adversary)
          true n)) +
        2 / 2 ^ n) :=
  advantage_scheme_le_modLeveledAdversary_two_mul forgetfulCircuits (fun _ => 1) (fun _ => 2)
    adversary n 2 (by decide) (by decide) (secret_width n) le_rfl htail

-- Explicit public-key length bound on supported leveled keys.
example (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (keyGen fixture n 1)).support) :
    keys.1.length ≤ publicKeyLengthBound (2 * 1) 2 1 3 := by
  refine length_publicKey_support_keyGen_le n 1 2 1 3 ?_ ?_ hkeys
  · intro baseKeys hbase
    obtain ⟨first, second, rfl⟩ := (keys_supported n baseKeys).1 hbase
    exact ⟨by simp, by simp⟩
  · intro baseKeys _ b ct hct
    simp only [fixture, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, PMF.uniformOfFintype,
      PMF.mem_support_uniformOfFinset_iff, Finset.mem_univ, true_and] at hct
    obtain ⟨nonce, rfl⟩ := hct
    simp

-- Quantitative polynomial coin-budget, artifact-length, and seeded-evaluator overhead package.
example :
    ∃ (c_kg d_kg c_enc d_enc c_ch d_ch c_gu d_gu : ℕ)
      (evalChoose : (ℕ × List Bool) → List Bool → ((Bool × Bool) × List Bool))
      (evalGuess : (ℕ × List Bool × List Bool) → List Bool → Bool),
      let pkBound (n : ℕ) := c_kg * (n + 1) ^ d_kg
      let ctBound (n : ℕ) := c_enc * (2 * n + 2 * pkBound n + 5) ^ d_enc
      let pubLen (n : ℕ) :=
        publicKeyLengthBound (2 * (n + 1)) 2 (pkBound n) (ctBound n)
      let advChooseBudget (n : ℕ) := c_ch * (2 * n + pubLen n + 2) ^ d_ch
      let advGuessBudget (n : ℕ) :=
        c_gu * (2 * n + 2 * advChooseBudget n + ctBound n + 4) ^ d_gu
      ComputableInPolyTime (fun (x, coins) => evalChoose x coins)
        (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair encBool encBool) encBits) ∧
      ComputableInPolyTime (fun (x, coins) => evalGuess x coins)
        (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool ∧
      (∀ n cut artifact,
        artifact ∈ (ProbComp.eval (fixture.publicKeyChainHybrid n (2 * (n + 1)) cut)).support →
          (encPublicKey artifact).length ≤ pubLen n) ∧
      (∀ n pk', pk'.length ≤ pubLen n →
        ProbComp.eval (adversary.choose n pk') =
          (BitString.uniformList (advChooseBudget n)).map (evalChoose (n, pk')) ∧
        ∀ choice ∈ (ProbComp.eval (adversary.choose n pk')).support,
          choice.2.length ≤ advChooseBudget n) ∧
      (∀ n state ct', state.length ≤ advChooseBudget n → ct'.length ≤ ctBound n + 1 →
        ProbComp.eval (adversary.guess n state ct') =
          (BitString.uniformList (advGuessBudget n)).map (evalGuess (n, state, ct'))) ∧
      PolynomiallyBounded (fun n =>
        leveledChooseCoinBudget (2 * (n + 1)) 2 (pkBound n) (ctBound n)
          (advChooseBudget n)) ∧
      PolynomiallyBounded (fun n =>
        leveledGuessCoinBudget (2 * (n + 1)) 2 (ctBound n)
          (advChooseBudget n) (advGuessBudget n)) ∧
      (leveledAdversary fixture (fun n => 2 * (n + 1)) (fun _ => 2) adversary).IsPPT ∧
      (modLeveledAdversary fixture (fun n => 2 * n) (fun n => 2 * (n + 1))
        (fun _ => 2) adversary).IsPPT :=
  exists_leveledAdversary_overhead keyGen_ppt encrypt_ppt adversary_ppt
    (budget := fun n => n + 1) (capacity := fun _ => 2) (width := fun _ => 2)
    secret_width (fun _ => le_rfl) (by fun_prop) (by fun_prop)

-- This fixture cannot satisfy encryption correctness: both messages encrypt to the same word.
example : ¬ forgetful.Correct := by
  intro hcorrect
  have hkey : ([false], [false, false]) ∈ (ProbComp.eval (forgetful.keyGen 0)).support :=
    (keys_supported 0 _).2 ⟨false, false, rfl⟩
  have h := hcorrect.decrypt_encrypt 0 ([false], [false, false]) hkey true []
    (by simp [forgetful])
  simp [forgetful] at h

end ComplexityTests.Crypto.LeveledSecurity
