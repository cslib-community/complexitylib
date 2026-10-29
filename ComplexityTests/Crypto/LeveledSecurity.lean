/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.Leveled.Bootstrapping
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

-- This fixture cannot satisfy encryption correctness: both messages encrypt to the same word.
example : ¬ forgetful.Correct := by
  intro hcorrect
  have hkey : ([false], [false, false]) ∈ (ProbComp.eval (forgetful.keyGen 0)).support :=
    (keys_supported 0 _).2 ⟨false, false, rfl⟩
  have h := hcorrect.decrypt_encrypt 0 ([false], [false, false]) hkey true []
    (by simp [forgetful])
  simp [forgetful] at h

end ComplexityTests.Crypto.LeveledSecurity
