/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Encryption.Authenticated


import Diag1155.Measure
/-!
# Tests for Authenticated Encryption and Chosen-Ciphertext Security

Provides concrete instantiations of `SymmetricCipher`, verifies oracle behavior on concrete inputs,
proves that `echoCipher` fails both `INDCPA` (via `not_indcpa_of_ciphertext_length_eq`,
Boneh–Shoup Example 5.1 / Exercise 5.10(a)) and `CiphertextIntegrity` (via an explicit zero-query
oracle-PPT adversary), and exercises the runtime certificates (`IsPPT`, `IsOraclePPT`) and
quantitative/asymptotic security theorems for Boneh–Shoup Theorem 9.1 (`AE ⇒ CCA`).
-/


diag1155_install
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
  decrypt_polyTime := .of_tidy (by polytime)
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
    have hrep : ComputableTidilyInPolyTime
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

/-! ### API and Certificate Smoke Checks -/

section CertificatesAndReductions

variable (E : SymmetricCipher)
  {ctBound Q : ℕ → ℕ}
  (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
  (hQ : ComputableInPolyTime Q encUnary encUnary)
  {cpaAdv : OracleDistinguisher} (hcpaAdv : IsOraclePPT encBool cpaAdv)
  {ciAdv : CIAdversary} (hciAdv : IsOraclePPT encBits ciAdv)
  {ccaAdv : CCAAdversary} (hccaAdv : IsOraclePPT encBool ccaAdv)

-- Closed game `IsPPT` certificates.
example (bit : Bool) : IsPPT encBool (fun n _ => E.cpaGame cpaAdv bit n) :=
  E.isPPT_cpaGame hcpaAdv bit

example : IsPPT encBool (fun n _ => E.ciGame ciAdv n) :=
  E.isPPT_ciGame hciAdv

example (bit : Bool) : IsPPT encBool (fun n _ => E.ccaGame ccaAdv bit n) :=
  E.isPPT_ccaGame hccaAdv bit

-- Theorem 9.1 reduction `IsOraclePPT` certificates.
example : IsOraclePPT encBool (SymmetricCipher.ccaToCPAAdversary ctBound ccaAdv) :=
  SymmetricCipher.isOraclePPT_ccaToCPAAdversary hctBound hccaAdv

example (bit : Bool) :
    IsOraclePPT encBits (SymmetricCipher.ccaToCIAdversary ctBound Q bit ccaAdv) :=
  SymmetricCipher.isOraclePPT_ccaToCIAdversary hctBound hQ bit hccaAdv

example : IsOraclePPT encBits (SymmetricCipher.ccaToCIHiddenBitAdversary ctBound Q ccaAdv) :=
  SymmetricCipher.isOraclePPT_ccaToCIHiddenBitAdversary hctBound hQ hccaAdv

-- Quantitative security bounds (Theorem 9.1).
example (n : ℕ)
    (hq : (ccaAdv n []).IsQueryBounded (Q n))
    (hctBoundN : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaGame ccaAdv false n))
        (ProbComp.eval (E.ccaGame ccaAdv true n)) : ℝ) ≤
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (SymmetricCipher.ccaToCIAdversary ctBound Q false ccaAdv) n)) :
            ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaGame (SymmetricCipher.ccaToCPAAdversary ctBound ccaAdv) false n))
        (ProbComp.eval (E.cpaGame (SymmetricCipher.ccaToCPAAdversary ctBound ccaAdv) true n)) :
          ℝ) +
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (SymmetricCipher.ccaToCIAdversary ctBound Q true ccaAdv) n)) :
            ℝ) :=
  E.advantage_ccaGame_le ctBound Q ccaAdv n hq hctBoundN

example (n : ℕ)
    (hq : (ccaAdv n []).IsQueryBounded (Q n))
    (hctBoundN : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaGame ccaAdv false n))
        (ProbComp.eval (E.ccaGame ccaAdv true n)) : ℝ) ≤
      2 * (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval
            (E.ciGame (SymmetricCipher.ccaToCIHiddenBitAdversary ctBound Q ccaAdv) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaGame (SymmetricCipher.ccaToCPAAdversary ctBound ccaAdv) false n))
        (ProbComp.eval (E.cpaGame (SymmetricCipher.ccaToCPAAdversary ctBound ccaAdv) true n)) :
          ℝ) :=
  E.advantage_ccaGame_le_two_mul ctBound Q ccaAdv n hq hctBoundN

-- End-to-end asymptotic composition (Theorem 9.1).
example (hae : E.AuthenticatedEncryption) : E.INDCCA :=
  hae.indcca

end CertificatesAndReductions

end ComplexityTests.Crypto.AuthenticatedEncryption
