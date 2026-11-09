/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Leveled.Bootstrapping
import Complexity.Crypto.Computational.Homomorphic.Leveled.GameOverhead
import Complexity.Crypto.Computational.Homomorphic.Leveled.FlatSecurity
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
open scoped NNReal ENNReal

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
    Encryption.advantage
      (Encryption.game (fun n => keyGen fixture n 1) (encrypt fixture) adversary) n =
    4 * (dyadicSize (2 * 1) : NNReal) * dyadicSize 2 *
      Encryption.advantage (Encryption.game fixture.keyGen fixture.encrypt
        (leveledAdversary fixture (fun _ => 2 * 1) (fun _ => 2) adversary)) n :=
  advantage_game_eq_leveledAdversary fixture (fun _ => 1) (fun _ => 2) adversary n 2
    (secret_width n) le_rfl

example (n : ℕ) :
    Encryption.advantage
      (Encryption.game (fun n => keyGen fixture n 1) (encrypt fixture) adversary) n ≤
    16 * (2 * (1 : ℕ) + 1 : NNReal) * ((2 : ℕ) + 1) *
      Encryption.advantage (Encryption.game fixture.keyGen fixture.encrypt
        (leveledAdversary fixture (fun _ => 2 * 1) (fun _ => 2) adversary)) n :=
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
    Encryption.advantage (Encryption.game (scheme forgetfulCircuits (fun n => n + 1)).keyGen
      (scheme forgetfulCircuits (fun n => n + 1)).encrypt adversary) n =
    3 * (2 * ((n + 1 : ℕ) : NNReal)) * (2 : ℕ) *
      Encryption.advantage (Encryption.game forgetful.keyGen forgetful.encrypt
        (exactLeveledAdversary forgetful (fun n => 2 * (n + 1)) (fun _ => 2) adversary)) n :=
  advantage_scheme_eq_exactLeveledAdversary forgetfulCircuits (fun n => n + 1) (fun _ => 2)
    adversary n 2 (Nat.succ_pos n) (by decide) (secret_width n) le_rfl

-- Unattenuated three-hop decomposition via exactLinkAdversary and zeroLinkAdversary.
example (n : ℕ) :
    Encryption.advantage (Encryption.game (scheme forgetfulCircuits (fun _ => 1)).keyGen
      (scheme forgetfulCircuits (fun _ => 1)).encrypt adversary) n ≤
    (2 * (1 : ℕ) : NNReal) * 2 *
      Encryption.advantage (Encryption.game forgetful.keyGen forgetful.encrypt
        (forgetful.exactLinkAdversary (fun _ => 2 * 1) (fun _ => 2)
          (publicKeyGame forgetful adversary false))) n +
    Encryption.advantage (Encryption.game forgetful.keyGen forgetful.encrypt
      (zeroLinkAdversary forgetful (fun _ => 2 * 1) adversary)) n +
    (2 * (1 : ℕ) : NNReal) * 2 *
      Encryption.advantage (Encryption.game forgetful.keyGen forgetful.encrypt
        (forgetful.exactLinkAdversary (fun _ => 2 * 1) (fun _ => 2)
          (publicKeyGame forgetful adversary true))) n :=
  advantage_scheme_le_exactLinkAdversary_add_zeroLinkAdversary forgetfulCircuits (fun _ => 1)
    (fun _ => 2) adversary n 2 (secret_width n) le_rfl

-- Strict-PPT sampleModNat reduction and concrete advantage bound with O(1 / 2 ^ n) tail.
example : (modLeveledAdversary fixture (fun n => 2 * n) (fun n => 2 * (n + 1))
    (fun _ => 2) adversary).IsPPT :=
  isPPT_modLeveledAdversary_two_mul keyGen_ppt encrypt_ppt adversary_ppt
    (by fun_prop) (by fun_prop)

example (n : ℕ) (htail : 3 + 2 * 1 + 2 ≤ 2 ^ n) :
    Encryption.advantage (Encryption.game (scheme forgetfulCircuits (fun _ => 1)).keyGen
      (scheme forgetfulCircuits (fun _ => 1)).encrypt adversary) n ≤
    3 * (2 * (1 : ℕ) : NNReal) * 2 *
      (Encryption.advantage (Encryption.game forgetful.keyGen forgetful.encrypt
        (modLeveledAdversary forgetful (fun n => 2 * n) (fun _ => 2 * 1) (fun _ => 2)
          adversary)) n +
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
      (evalKey : ℕ → List Bool → List Bool × List Bool)
      (evalEncrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
      (evalChoose : (ℕ × List Bool) → List Bool → ((Bool × Bool) × List Bool))
      (evalGuess : (ℕ × List Bool × List Bool) → List Bool → Bool),
      let pkBound (n : ℕ) := c_kg * (n + 1) ^ d_kg
      let ctBound (n : ℕ) := c_enc * (2 * n + 2 * pkBound n + 5) ^ d_enc
      let pubLen (n : ℕ) :=
        publicKeyLengthBound (2 * (n + 1)) 2 (pkBound n) (ctBound n)
      let advChooseBudget (n : ℕ) := c_ch * (2 * n + pubLen n + 2) ^ d_ch
      let advGuessBudget (n : ℕ) :=
        c_gu * (2 * n + 2 * advChooseBudget n + ctBound n + 4) ^ d_gu
      ComputableInPolyTime (fun (n, coins) => evalKey n coins)
        (encPair encUnary encBits) (encPair encBits encBits) ∧
      ComputableInPolyTime (fun (x, coins) => evalEncrypt x coins)
        (encPair (encPair encUnary (encPair encBits encBool)) encBits) encBits ∧
      ComputableInPolyTime (fun (x, coins) => evalChoose x coins)
        (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair encBool encBool) encBits) ∧
      ComputableInPolyTime (fun (x, coins) => evalGuess x coins)
        (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool ∧
      (∀ n, ProbComp.eval (fixture.keyGen n) =
        (BitString.uniformList (pkBound n)).map (evalKey n)) ∧
      (∀ n keys, keys ∈ (ProbComp.eval (fixture.keyGen n)).support →
        keys.1.length ≤ pkBound n ∧ keys.2.length ≤ 2) ∧
      (∀ n pk bit, pk.length ≤ pkBound n →
        ProbComp.eval (fixture.encrypt n pk bit) =
          (BitString.uniformList (ctBound n)).map (evalEncrypt (n, pk, bit)) ∧
        ∀ ct ∈ (ProbComp.eval (fixture.encrypt n pk bit)).support, ct.length ≤ ctBound n) ∧
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


-- Both adversary stages use a number of random bits that depends on their actual input.
-- The choice saves its full public artifact followed by an equally long fresh word.
private noncomputable def inputSizedAdversary : Encryption.Adversary where
  choose _ word := do
    let seed ← BitString.sampleList word.length
    pure ((seed.headD false, false), word ++ seed)
  guess _ state ciphertext := do
    let seed ← BitString.sampleList state.length
    pure (seed.headD false ^^ ciphertext.headD false)

private theorem inputSizedAdversary_ppt : inputSizedAdversary.IsPPT := by
  constructor <;> dsimp only [inputSizedAdversary] <;> ppt

example (word : List Bool) (choice : (Bool × Bool) × List Bool)
    (hchoice : choice ∈ (ProbComp.eval (inputSizedAdversary.choose 0 word)).support) :
    choice.2.length = 2 * word.length := by
  simp only [inputSizedAdversary, ProbComp.eval_bind, BitString.eval_sampleList,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hchoice
  obtain ⟨seed, hseed, rfl⟩ := hchoice
  simp [BitString.length_of_mem_support_uniformList hseed, two_mul]

-- The new endpoint derives budgets for this input-sized adversary; no fixed-n global
-- component law is supplied. Both positive and zero depth instantiate the same native result.
example (depthBudget : ℕ → ℕ)
    (hdepthBudget : ComputableInPolyTime depthBudget encUnary encUnary) (bit : Bool) :
    ∃ (encCoins chooseCoins guessCoins : ℕ → ℕ)
      (evaluate : (ℕ × List Bool × List Bool) → List Bool → Bool),
      ComputableInPolyTime (fun (input, tape) => evaluate input tape)
        (encPair (encPair encUnary (encPair encBits encBits)) encBits) encBool ∧
      PolynomiallyBounded (fun n => leveledGuessCoinBudget (2 * depthBudget n) 2
        (encCoins n) (chooseCoins n) (guessCoins n)) ∧
      ∀ n target, target ∈ (ProbComp.eval (fixture.keyGen n)).support →
        ∀ choice, choice ∈ (ProbComp.eval ((fixture.modLinkAdversary (fun _ => 0)
          (fun n => 2 * depthBudget n) (fun _ => 2)
          (publicKeyGame fixture inputSizedAdversary bit)).choose n target.1)).support →
        ∀ message challenge,
          challenge ∈ (ProbComp.eval (fixture.encrypt n target.1 message)).support →
        ProbComp.eval ((fixture.modLinkAdversary (fun _ => 0) (fun n => 2 * depthBudget n)
          (fun _ => 2) (publicKeyGame fixture inputSizedAdversary bit)).guess n
            choice.2 challenge) =
          (BitString.uniformList (leveledGuessCoinBudget (2 * depthBudget n) 2
            (encCoins n) (chooseCoins n) (guessCoins n))).map
              (evaluate (n, choice.2, challenge)) := by
  obtain ⟨encCoins, chooseCoins, guessCoins, evaluate, _, _, _, hevaluate, hpoly, hlaw⟩ :=
    Scheme.exists_modLinkAdversary_guess_coin_evaluator keyGen_ppt encrypt_ppt
      inputSizedAdversary_ppt (coins := fun _ => 0) (budget := depthBudget)
      (capacity := fun _ => 2) (width := fun _ => 2) secret_width (fun _ => le_rfl)
      hdepthBudget (by fun_prop) bit
  exact ⟨encCoins, chooseCoins, guessCoins, evaluate, hevaluate, hpoly, hlaw⟩

-- Zero depth still samples its indices but can only return the original rejection.
-- This concerns the link sub-reduction; the complete modular reduction has a zero-link fallback.
example (n : ℕ) : ProbComp.eval ((fixture.modLinkAdversary (fun _ => 1) (fun _ => 0)
    (fun _ => 2) (publicKeyGame fixture inputSizedAdversary false)).choose n []) =
      PMF.pure Scheme.rejectLinkChoice := by
  simp [Scheme.modLinkAdversary, ProbComp.eval_bind, PMF.map, Function.comp_def]

example (n : ℕ) (challenge : List Bool) : ProbComp.eval
    ((fixture.modLinkAdversary (fun _ => 1) (fun _ => 0) (fun _ => 2)
      (publicKeyGame fixture inputSizedAdversary false)).guess n Scheme.rejectLinkState
        challenge) = PMF.pure false := by
  simp [Scheme.modLinkAdversary, ProbComp.eval_pure]

-- The new size theorem applies to the actual boundary splice, including its external challenge.
example {links : List (List (List Bool))}
    (hlinks : links ∈ (ProbComp.eval (fixture.spliceEncryptedKeyLink 0
      [([false], [false, false])] ([false], [false, false]) ([true], [false, false]) []
      1 [true, false, true])).support) :
    (encPublicKey ([[false], [false], [true]], links)).length ≤
      publicKeyLengthBound 2 2 1 3 := by
  have hbound := length_encPublicKey_support_splice_le (E := fixture)
    (capacity := 2) (pkBound := 1) (ctBound := 3) (by decide : 1 < [false, false].length)
    (before := [([false], [false, false])]) (after := [])
    (predecessor := ([false], [false, false])) (next := ([true], [false, false]))
    (by
      intro key hkey
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hkey
      rcases hkey with rfl | rfl | rfl <;> decide)
    (by
      intro key _ message ciphertext hct
      simp only [fixture, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
      obtain ⟨nonce, _, rfl⟩ := hct
      exact le_rfl)
    (by decide : [true, false, true].length ≤ 3) hlinks
  simpa using hbound

-- A generated target has a three-bit supported challenge. An arbitrary four-bit word does
-- not satisfy the encryption-support premise, regardless of the challenge message.
example : ([false], [false, false]) ∈ (ProbComp.eval (fixture.keyGen 0)).support :=
  (keys_supported 0 _).mpr ⟨false, false, rfl⟩

example : [false, true, false] ∈ (ProbComp.eval (fixture.encrypt 0 [false] true)).support := by
  simp [fixture, ProbComp.eval_uniform]

example (message : Bool) : [false, true, false, true] ∉
    (ProbComp.eval (fixture.encrypt 0 [false] message)).support := by
  simp [fixture, ProbComp.eval_uniform]

-- The complete game derives all support premises internally, for both challenge worlds and
-- the input-sized adversary. The selector's unary coin family may be any native polynomial.
example (indexCoins depthBudget : ℕ → ℕ)
    (hindexCoins : ComputableInPolyTime indexCoins encUnary encUnary)
    (hdepthBudget : ComputableInPolyTime depthBudget encUnary encUnary) :
    ∃ (keyCoins encCoins chooseCoins guessCoins : ℕ → ℕ)
      (evaluate : Bool → ℕ → List Bool → Bool),
      (∀ bit, ComputableInPolyTime (fun (n, tape) => evaluate bit n tape)
        (encPair encUnary encBits) encBool) ∧
      PolynomiallyBounded (fun n => modLeveledGameCoinBudget (indexCoins n) (2 * depthBudget n)
        2 (keyCoins n) (encCoins n) (chooseCoins n) (guessCoins n)) ∧
      ∀ bit n, ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
        (modLeveledAdversary fixture indexCoins (fun n => 2 * depthBudget n) (fun _ => 2)
          inputSizedAdversary) bit n) =
        (BitString.uniformList (modLeveledGameCoinBudget (indexCoins n) (2 * depthBudget n)
          2 (keyCoins n) (encCoins n) (chooseCoins n) (guessCoins n))).map (evaluate bit n) := by
  obtain ⟨keyCoins, encCoins, chooseCoins, guessCoins, evaluate, _, _, _, _, hevaluate,
    hpoly, hlaw⟩ := exists_modLeveledGame_coin_evaluator keyGen_ppt encrypt_ppt
      inputSizedAdversary_ppt (coins := indexCoins) (budget := depthBudget)
      (capacity := fun _ => 2) (width := fun _ => 2) secret_width (fun _ => le_rfl)
      hindexCoins hdepthBudget (by fun_prop)
  exact ⟨keyCoins, encCoins, chooseCoins, guessCoins, evaluate, hevaluate, hpoly, hlaw⟩

-- This fixture cannot satisfy encryption correctness: both messages encrypt to the same word.
example : ¬ forgetful.Correct := by
  intro hcorrect
  have hkey : ([false], [false, false]) ∈ (ProbComp.eval (forgetful.keyGen 0)).support :=
    (keys_supported 0 _).2 ⟨false, false, rfl⟩
  have h := hcorrect.decrypt_encrypt 0 ([false], [false, false]) hkey true []
    (by simp [forgetful])
  simp [forgetful] at h

-- Native execution includes a runtime-varying attempt count and all original callbacks.
example (attempts depth capacity : ℕ → ℕ)
    (ha : ComputableInPolyTime attempts encUnary encUnary)
    (hd : ComputableInPolyTime depth encUnary encUnary)
    (hc : ComputableInPolyTime capacity encUnary encUnary) :
    (flatLeveledAdversary fixture attempts depth capacity adversary).IsPPT :=
  isPPT_flatLeveledAdversary keyGen_ppt encrypt_ppt adversary_ppt ha hd hc

-- This exposed-plaintext fixture has signed source gap -1, not a vacuous zero advantage.
private theorem flat_signed_gap (attempts budget : ℕ → ℕ) (n : ℕ) :
    (Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (flatLeveledAdversary fixture attempts (fun n => 2 * budget n) (fun _ => 2) adversary)
        false n)) : ℝ) -
    Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (flatLeveledAdversary fixture attempts (fun n => 2 * budget n) (fun _ => 2) adversary)
        true n)) =
      -(ProbComp.intervalSuccess (2 * (2 * budget n * 2) + 1) (attempts n) : ℝ) /
        (2 * (2 * budget n * 2) + 1 : ℕ) := by
  rw [gap_flatLeveledAdversary fixture attempts budget (fun _ => 2) adversary n 2
    (secret_width n) le_rfl, eval_game_keyGen fixture budget adversary false n,
    eval_game_keyGen fixture budget adversary true n]
  simp [eval_publicKeyGame, Game.succProbability, neg_div]

-- Three attempts strictly improve the actual reduction's selector loss at four link-bit slots.
example : (9 : ℝ≥0) / ProbComp.intervalSuccess 9 3 < 12 :=
  by convert flatLeveled_loss_lt 2 2 3 (by decide) (by decide) using 1; norm_num

-- Exhaustion at zero attempts aborts in both worlds even though the exposed source gap is -1.
example (depth capacity : ℕ → ℕ) (bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (flatLeveledAdversary fixture (fun _ => 0) depth capacity adversary) bit n) =
        PMF.pure false := by
  simp [Encryption.game, Encryption.gameOn, flatLeveledAdversary, leveledAdversary,
    rejectLeveledChoice, ProbComp.eval_bind, PMF.map, Function.comp_def]

-- A concrete nonzero gap: N=9, failure (7/16)^3, and one surviving mass per hybrid step.
example (n : ℕ) :
    (Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (flatLeveledAdversary fixture (fun _ => 3) (fun _ => 2) (fun _ => 2) adversary)
        false n)) : ℝ) -
    Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (flatLeveledAdversary fixture (fun _ => 3) (fun _ => 2) (fun _ => 2) adversary)
        true n)) = -(417 / 4096) := by
  have h := flat_signed_gap (fun _ => 3) (fun _ => 1) n
  have hp : ProbComp.intervalFailure 9 = (7 / 16 : ℝ≥0) := by
    norm_num [ProbComp.intervalFailure, dyadicSize, show Nat.log 2 9 = 3 by decide]
  have hle : (7 / 16 : ℝ≥0) ^ 3 ≤ 1 := by
    exact_mod_cast (show (7 / 16 : ℝ) ^ 3 ≤ 1 by norm_num)
  convert h using 1
  change -(417 / 4096 : ℝ) = -(ProbComp.intervalSuccess 9 3 : ℝ) / 9
  rw [ProbComp.intervalSuccess, hp, NNReal.coe_sub hle]
  norm_num

-- A singleton selector retains its exhaustion probability: the source's nonzero gap is halved.
example (n : ℕ) :
    (Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (flatLeveledAdversary fixture (fun _ => 1) (fun _ => 0) (fun _ => 2) adversary)
        false n)) : ℝ) -
    Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (flatLeveledAdversary fixture (fun _ => 1) (fun _ => 0) (fun _ => 2) adversary)
        true n)) = -(1 / 2) := by
  have h := flat_signed_gap (fun _ => 1) (fun _ => 0) n
  have hp : ProbComp.intervalFailure 1 = (1 / 2 : ℝ≥0) := by
    norm_num [ProbComp.intervalFailure, dyadicSize]
  have hle : (1 / 2 : ℝ≥0) ≤ 1 := by
    exact_mod_cast (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  convert h using 1; norm_num [ProbComp.intervalSuccess, hp, NNReal.coe_sub hle]

private theorem eval_one_slot_link (testBit bit : Bool) (n : ℕ) :
    ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (fixture.exactLinkAdversary (fun _ => 1) (fun _ => 1)
        (publicKeyGame fixture adversary testBit)) bit n) = PMF.pure testBit := by
  rw [fixture.eval_exactLinkAdversary _ _ _ n 2 bit (secret_width n)]
  simp [Scheme.exactKeyChainHybridGame, eval_publicKeyGame]

-- The one-slot selector has no claimed improvement over the ideal factor `3`. Its two actual
-- worlds have probabilities 1/4 and 1/2 after one attempt, retaining the fourth abort outcome.
example (bit : Bool) (n : ℕ) :
    (Game.succProbability (ProbComp.eval (Encryption.game fixture.keyGen fixture.encrypt
      (flatLeveledAdversary fixture (fun _ => 1) (fun _ => 1) (fun _ => 1) adversary)
        bit n)) : ℝ) = if bit then 1 / 2 else 1 / 4 := by
  rw [succProbability_flatLeveledAdversary]
  simp only [eval_one_slot_link, eval_zeroLinkGame]
  have hp : ProbComp.intervalFailure 3 = (1 / 4 : ℝ≥0) := by
    norm_num [ProbComp.intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]
  have hle : (1 / 4 : ℝ≥0) ≤ 1 := by
    exact_mod_cast (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  cases bit <;> norm_num [Game.succProbability, ProbComp.intervalSuccess, hp, NNReal.coe_sub hle]

end ComplexityTests.Crypto.LeveledSecurity
