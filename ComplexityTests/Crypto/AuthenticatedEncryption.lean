/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Encryption.Authenticated

/-!
# Tests for Authenticated Encryption and Chosen-Ciphertext Security

Provides concrete instantiations of `SymmetricCipher`, verifies oracle behavior on concrete inputs,
proves that `echoCipher` fails both `INDCPA` (via `not_indcpa_of_ciphertext_length_eq`,
Boneh–Shoup Example 5.1 / Exercise 5.10(a)) and `CiphertextIntegrity` (via an explicit zero-query
oracle-PPT adversary), and exercises the composed runtime certificates (`IsPPT`, `IsOraclePPT`) and
quantitative security bounds for Boneh–Shoup Theorem 9.1 (`AE ⇒ CCA`) on `echoCipher`.
-/

namespace ComplexityTests.Crypto.AuthenticatedEncryption

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete unauthenticated identity cipher on `n`-bit messages. Used to witness that the
`SymmetricCipher` fields are satisfiable and to verify that both
`not_indcpa_of_ciphertext_length_eq` and `CiphertextIntegrity` reject deterministic unauthenticated
ciphers. -/
noncomputable def echoCipher : SymmetricCipher where
  keyGen _ := pure []
  encrypt _ _ msg := pure msg
  decrypt _ _ ct := some ct
  keyGen_ppt := by ppt
  encrypt_ppt := by ppt
  decrypt_polyTime := by polytime
  decrypt_encrypt := by
    intro _ _ _ msg _ ct hct
    rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hct
    subst hct
    rfl

theorem echoCipher_ctLen :
    ∀ n ke, ke ∈ (ProbComp.eval (echoCipher.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (echoCipher.encrypt n ke msg)).support, c.length = n := by
  intro n _ _ msg hmsg c hc
  change c ∈ (ProbComp.eval (pure msg)).support at hc
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hc
  subst hc
  exact hmsg

/-- `echoCipher` has zero ciphertext expansion (`c.length = n`), so by Boneh–Shoup Example 5.1 and
Exercise 5.10(a) (`SymmetricCipher.not_indcpa_of_ciphertext_length_eq`), it cannot satisfy
`INDCPA`. -/
theorem not_indcpa_echoCipher : ¬ echoCipher.INDCPA :=
  echoCipher.not_indcpa_of_ciphertext_length_eq echoCipher_ctLen

-- Wrong-length query to `ciEncryptionOracle` returns `[]` without modifying the queried list.
example :
    echoCipher.ciEncryptionOracle 2 [] ((), [true]) [] = pure ([], []) := by
  rfl

-- Valid `n`-bit query to `ciEncryptionOracle` records the produced ciphertext.
example :
    echoCipher.ciEncryptionOracle 2 [] ((), [true, false]) [] =
      pure ([true, false], [[true, false]]) := by
  rfl

-- In `ccaOracle`, querying decryption on a previously returned challenge ciphertext is rejected.
example :
    echoCipher.ccaOracle 2 [] false (true, [true, false]) [[true, false]] =
      pure ([], [[true, false]]) := by
  rfl

-- In `ccaOracle`, querying decryption on a fresh ciphertext returns `encOption encBits (some msg)`.
example :
    echoCipher.ccaOracle 2 [] false (true, [true, false]) [] =
      pure (encOption encBits (some [true, false]), []) := by
  rfl

/-- `echoCipher` does not satisfy `CiphertextIntegrity`: a zero-query oracle-PPT adversary that
outputs `0^n` wins `ciGame` with probability `1` for every `n`. -/
theorem not_ciphertextIntegrity_echoCipher :
    ¬ echoCipher.CiphertextIntegrity := by
  intro hci
  let adversary : CIAdversary := fun n _ =>
    ProbOracleComp.sample (pure (List.replicate n false))
  have hadvBody : IsPPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool => (pure (List.replicate p.1 false) : ProbComp (List Bool))) := by
    have hrep : ComputableInPolyTime
        (fun p : ℕ × List Bool => List.replicate p.1 false)
        (encPair encUnary encBits) encBits := by polytime
    exact hrep.isPPTOn
  have hadv : IsOraclePPT encBits adversary :=
    hadvBody.isOraclePPTOn.isOraclePPT
  have hneg := hci.negligible adversary hadv
  have heval (n : ℕ) :
      Game.succProbability (ProbComp.eval (echoCipher.ciGame adversary n)) = 1 := by
    simp [SymmetricCipher.ciGame, echoCipher, adversary, Game.succProbability]
  simp only [heval] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- Consequently, `echoCipher` is not an `AuthenticatedEncryption` scheme. -/
theorem not_authenticatedEncryption_echoCipher :
    ¬ echoCipher.AuthenticatedEncryption :=
  fun hae => not_ciphertextIntegrity_echoCipher hae.2

/-! ### Concrete Reduction Certificates and Quantitative Bounds on `echoCipher` -/

/-- Zero-query CCA adversary that always outputs `false`. -/
def zeroCCAAdversary : CCAAdversary :=
  fun _ _ => ProbOracleComp.sample (pure false)

theorem isOraclePPT_zeroCCAAdversary : IsOraclePPT encBool zeroCCAAdversary := by
  have hbody : IsPPTOn (encPair encUnary encBits) encBool
      (fun _ : ℕ × List Bool => (pure false : ProbComp Bool)) :=
    (ComputableInPolyTime.const false).isPPTOn
  exact hbody.isOraclePPTOn.isOraclePPT

theorem isQueryBounded_zeroCCAAdversary (n : ℕ) :
    (zeroCCAAdversary n []).IsQueryBounded 0 :=
  ProbOracleComp.IsQueryBounded.sample (pure false)

-- Composed closed-game `IsPPT` and Theorem 9.1 reduction `IsOraclePPT` certificates on
-- `echoCipher` with `ctBound = id` and `Q = 0`.
example (bit : Bool) :
    IsPPT encBool
      (fun n _ =>
        echoCipher.cpaGame (SymmetricCipher.ccaToCPAAdversary id zeroCCAAdversary) bit n) ∧
    IsPPT encBool
      (fun n _ =>
        echoCipher.ciGame
          (SymmetricCipher.ccaToCIAdversary id (fun _ => 0) bit zeroCCAAdversary) n) ∧
    IsPPT encBool
      (fun n _ =>
        echoCipher.ciGame
          (SymmetricCipher.ccaToCIHiddenBitAdversary id (fun _ => 0) zeroCCAAdversary) n) :=
  ⟨echoCipher.isPPT_cpaGame
    (SymmetricCipher.isOraclePPT_ccaToCPAAdversary ComputableInPolyTime.id'
      isOraclePPT_zeroCCAAdversary)
    bit,
   echoCipher.isPPT_ciGame
    (SymmetricCipher.isOraclePPT_ccaToCIAdversary ComputableInPolyTime.id'
      (ComputableInPolyTime.const 0) bit isOraclePPT_zeroCCAAdversary),
   echoCipher.isPPT_ciGame
    (SymmetricCipher.isOraclePPT_ccaToCIHiddenBitAdversary ComputableInPolyTime.id'
      (ComputableInPolyTime.const 0) isOraclePPT_zeroCCAAdversary)⟩

-- Quantitative Theorem 9.1 bounds instantiated on `echoCipher` and `zeroCCAAdversary`, with
-- `dyadicSize 0 = 2` evaluated and `echoCipher_ctLen` discharging the ciphertext-length premise.
example (n : ℕ) :
    (Game.advantage (ProbComp.eval (echoCipher.ccaGame zeroCCAAdversary false n))
        (ProbComp.eval (echoCipher.ccaGame zeroCCAAdversary true n)) : ℝ) ≤
      2 *
        (Game.succProbability
          (ProbComp.eval
            (echoCipher.ciGame
              (SymmetricCipher.ccaToCIAdversary id (fun _ => 0) false zeroCCAAdversary) n)) :
            ℝ) +
      (Game.advantage
        (ProbComp.eval
          (echoCipher.cpaGame (SymmetricCipher.ccaToCPAAdversary id zeroCCAAdversary) false n))
        (ProbComp.eval
          (echoCipher.cpaGame (SymmetricCipher.ccaToCPAAdversary id zeroCCAAdversary) true n)) :
          ℝ) +
      2 *
        (Game.succProbability
          (ProbComp.eval
            (echoCipher.ciGame
              (SymmetricCipher.ccaToCIAdversary id (fun _ => 0) true zeroCCAAdversary) n)) :
            ℝ) := by
  have hct (k : List Bool) (hk : k ∈ (ProbComp.eval (echoCipher.keyGen n)).support)
      (msg : List Bool) (hmsg : msg.length = n)
      (ct : List Bool) (hct : ct ∈ (ProbComp.eval (echoCipher.encrypt n k msg)).support) :
      ct.length ≤ id n :=
    (echoCipher_ctLen n k hk msg hmsg ct hct).le
  have h0 : dyadicSize 0 = 2 := by decide
  have hd : (dyadicSize 0 : ℝ) = 2 := by exact_mod_cast h0
  simpa [hd] using
    echoCipher.advantage_ccaGame_le id (fun _ => 0) zeroCCAAdversary n
      (isQueryBounded_zeroCCAAdversary n) hct

example (n : ℕ) :
    (Game.advantage (ProbComp.eval (echoCipher.ccaGame zeroCCAAdversary false n))
        (ProbComp.eval (echoCipher.ccaGame zeroCCAAdversary true n)) : ℝ) ≤
      4 *
        (Game.succProbability
          (ProbComp.eval
            (echoCipher.ciGame
              (SymmetricCipher.ccaToCIHiddenBitAdversary id (fun _ => 0) zeroCCAAdversary) n)) :
            ℝ) +
      (Game.advantage
        (ProbComp.eval
          (echoCipher.cpaGame (SymmetricCipher.ccaToCPAAdversary id zeroCCAAdversary) false n))
        (ProbComp.eval
          (echoCipher.cpaGame (SymmetricCipher.ccaToCPAAdversary id zeroCCAAdversary) true n)) :
          ℝ) := by
  have hct (k : List Bool) (hk : k ∈ (ProbComp.eval (echoCipher.keyGen n)).support)
      (msg : List Bool) (hmsg : msg.length = n)
      (ct : List Bool) (hct : ct ∈ (ProbComp.eval (echoCipher.encrypt n k msg)).support) :
      ct.length ≤ id n :=
    (echoCipher_ctLen n k hk msg hmsg ct hct).le
  have hd : 2 * (dyadicSize 0 : ℝ) = 4 := by
    have h0 : dyadicSize 0 = 2 := by decide
    rw [h0]
    norm_num
  simpa [hd] using
    echoCipher.advantage_ccaGame_le_two_mul id (fun _ => 0) zeroCCAAdversary n
      (isQueryBounded_zeroCCAAdversary n) hct

end ComplexityTests.Crypto.AuthenticatedEncryption
