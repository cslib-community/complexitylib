/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Computational.GoldwasserMicali
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Goldwasser–Micali public-key encryption

Concrete evaluation and non-vacuity checks for `Complexity.Crypto.Computational.GoldwasserMicali`:

* arithmetic encryption, Euler-criterion decryption, and homomorphic XOR at `N = 15 = 3 * 5`
  (`z = 2 ∈ QNR_{15}^{+1}`) and at the Blum modulus `N = 21 = 3 * 7` (`z = 20 = -1 mod 21`);
* support-level correctness, XOR homomorphism, bitwise multi-bit encryption, and Exercise 15.11
  distributional equality / re-randomization on the Blum key `k21`;
* two bad-`z` counterexamples at `N = 21`: `z = 2 ∈ J_{21}^{-1}` is still decryptable by `(3, 7)`
  yet broken with exact IND-CPA advantage `1` (hence non-negligible) by the certified uniform
  strict-PPT `jacobiAttackAdversary`, whereas `z = 4 ∈ QR_{21}` breaks decryption correctness and
  collapses ciphertext distributions;
* concrete client instantiations of `isPPTOn_qrDistinguisher`, `isPPTOn_qrWordDistinguisher`,
  `indcpa_goldwasserMicali`, and `indcpaOn_goldwasserMicali_bits`.
-/

namespace ComplexityTests.Crypto.GoldwasserMicali

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.GoldwasserMicali
open Turing.MultiTapeTM
open scoped NNReal

/-! ### Arithmetic evaluation at `N = 15 = 3 * 5` (`z = 2 ∈ QNR_{15}^{+1}`) -/

def d15 : ModulusDesc := ⟨3, 5, by norm_num, by norm_num, by decide, by decide, by decide⟩

example :
    let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    (ZMod.unitOfCoprime 2 (by decide) : (ZMod 15)ˣ) ∈ positiveNonresidues 3 5 := by decide

example : ciphertext 15 2 false 7 = 4 := by decide
example : ciphertext 15 2 true 7 = 8 := by decide
example : decryptNat 3 5 4 = false := by decide
example : decryptNat 3 5 8 = true := by decide

example : ∀ b₁ b₂ : Bool,
    decryptNat 3 5
      (mulCiphertextsNat 15 (ciphertext 15 2 b₁ 7) (ciphertext 15 2 b₂ 11)) = (b₁ ^^ b₂) := by
  decide

/-! ### Blum modulus `N = 21 = 3 * 7` (`z = 20 = -1 mod 21`) and supported `ProbComp` clients -/

def d21 : ModulusDesc := ⟨3, 7, by norm_num, by norm_num, by decide, by decide, by decide⟩

theorem isBlumModulus_3_7 : IsBlumModulus 3 7 :=
  ⟨⟨by norm_num, by decide⟩, ⟨by norm_num, by decide⟩, by decide⟩

def k21 : KeyDesc := KeyDesc.ofBlum d21 isBlumModulus_3_7

example : k21.modulus = 21 ∧ k21.z = 20 := ⟨rfl, rfl⟩
example : ciphertext 21 20 false 5 = 4 ∧ ciphertext 21 20 true 5 = 17 := by decide
example : decryptNat 3 7 4 = false ∧ decryptNat 3 7 17 = true := by decide

noncomputable def constKeyGen : ℕ → ProbComp KeyDesc := fun _ => pure k21

theorem isPPTOn_constKeyGen : IsPPTOn encUnary encKeyDesc constKeyGen :=
  (ComputableInPolyTime.const k21).isPPTOn

example : IsPPTOn encUnary (encPair encBits encBits) (keyGen constKeyGen) :=
  isPPTOn_keyGen isPPTOn_constKeyGen

theorem mem_support_keyGen_k21 (n : ℕ) :
    (encPair encNat encNat (21, 20), encPair encNat encNat (3, 7)) ∈
      (ProbComp.eval (keyGen constKeyGen n)).support := by
  simp only [keyGen, constKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    PMF.support_pure, Set.mem_singleton_iff]
  rfl

example (n : ℕ) (m : Bool) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n (encPair encNat encNat (21, 20)) m)).support) :
    decrypt (encPair encNat encNat (3, 7)) ct = m :=
  decrypt_encrypt (gen := constKeyGen) (mem_support_keyGen_k21 n) m hct

example (n : ℕ) {ct₁ ct₂ : List Bool}
    (hct₁ : ct₁ ∈ (ProbComp.eval (encrypt n (encPair encNat encNat (21, 20)) true)).support)
    (hct₂ : ct₂ ∈ (ProbComp.eval (encrypt n (encPair encNat encNat (21, 20)) true)).support) :
    decrypt (encPair encNat encNat (3, 7))
      (mulCiphertexts (encPair encNat encNat (21, 20)) ct₁ ct₂) = false :=
  decrypt_mulCiphertexts (gen := constKeyGen) (mem_support_keyGen_k21 n) hct₁ hct₂

example (n : ℕ) {cts : List (List Bool)}
    (hcts : cts ∈ (ProbComp.eval
      (encryptBits n (encPair encNat encNat (21, 20)) [true, false, true, true])).support) :
    decryptBits (encPair encNat encNat (3, 7)) cts = [true, false, true, true] :=
  decryptBits_encryptBits (gen := constKeyGen) (mem_support_keyGen_k21 n)
    [true, false, true, true] hcts

/-- Exercise 15.11 exact distributional XOR homomorphism and re-randomization on `k21`. -/
example (b₁ b₂ : Bool) :
    (do
      let ct₁ ← idealEncrypt k21.modulus k21.zUnit b₁
      let ct₂ ← idealEncrypt k21.modulus k21.zUnit b₂
      pure (mulCiphertexts (encPair encNat encNat (21, 20)) ct₁ ct₂)) =
      idealEncrypt k21.modulus k21.zUnit (b₁ ^^ b₂) := by
  have hpk : (21, 20) = (k21.modulus, k21.zUnit.val.val) := Prod.ext rfl k21.val_zUnit.symm
  rw [hpk]
  exact idealEncrypt_mulCiphertexts_eq k21.modulus k21.zUnit b₁ b₂

example (m : Bool) :
    (do
      let ct ← idealEncrypt k21.modulus k21.zUnit false
      pure (mulCiphertexts (encPair encNat encNat (21, 20))
        (encNat ((if m then k21.zUnit else 1) * (1 : (ZMod k21.modulus)ˣ) ^ 2).val.val) ct)) =
      idealEncrypt k21.modulus k21.zUnit m := by
  have hpk : (21, 20) = (k21.modulus, k21.zUnit.val.val) := Prod.ext rfl k21.val_zUnit.symm
  rw [hpk]
  exact rerandomize_idealEncrypt_eq k21.modulus k21.zUnit 1 m

/-! ### Non-vacuity and bad-`z` insecurity witnesses at `N = 21` -/

def badZ2 : (ZMod (d21.p * d21.q))ˣ := ZMod.unitOfCoprime 2 (by decide)

theorem badZ2_mem_jacobiNegSet : badZ2 ∈ jacobiNegSet d21.p d21.q := by
  simp only [jacobiNegSet, Finset.mem_filter, Finset.mem_univ, true_and]
  decide

example : ∀ m : Bool, decryptNat 3 7 (ciphertext 21 2 m 5) = m := by decide

theorem advantage_badZ2_eq_one (n : ℕ) :
    Game.advantage
      (Encryption.publicKeyGame (PMF.pure (encPair encNat encNat (21, 2)))
        encrypt jacobiAttackAdversary false n)
      (Encryption.publicKeyGame (PMF.pure (encPair encNat encNat (21, 2)))
        encrypt jacobiAttackAdversary true n) = 1 :=
  advantage_jacobiAttackAdversary_eq_one d21 badZ2 badZ2_mem_jacobiNegSet n

example : ¬ Negligible fun n =>
    Game.advantage
      (Encryption.publicKeyGame (PMF.pure (encPair encNat encNat (21, 2)))
        encrypt jacobiAttackAdversary false n)
      (Encryption.publicKeyGame (PMF.pure (encPair encNat encNat (21, 2)))
        encrypt jacobiAttackAdversary true n) := by
  simpa only [advantage_badZ2_eq_one] using not_negligible_const (one_ne_zero : (1 : ℝ≥0) ≠ 0)

example : decryptNat 3 7 (ciphertext 21 4 true 5) = false := by decide

example :
    let y4 : (ZMod 21)ˣ := ZMod.unitOfCoprime 4 (by decide)
    idealEncrypt 21 y4 true = idealEncrypt 21 y4 false :=
  idealEncrypt_of_isSquare 21 ⟨ZMod.unitOfCoprime 2 (by decide), by decide⟩ true

/-! ### IND-CPA reduction and security theorem clients -/

noncomputable def constBitAdversary : Encryption.Adversary where
  choose _ _ := pure ((false, true), [])
  guess _ _ _ := pure true

theorem constBitAdversary_isPPT : constBitAdversary.IsPPT where
  choose := (ComputableInPolyTime.const ((false, true), ([] : List Bool))).isPPTOn
  guess := (ComputableInPolyTime.const true).isPPTOn

example : IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
    (fun input => qrDistinguisher constBitAdversary input.1 input.2) :=
  isPPTOn_qrDistinguisher constBitAdversary_isPPT

example {setup : ℕ → PMF ModulusDesc} {gen : ℕ → ProbComp KeyDesc}
    (hsize : ∀ n, ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hkeys : ComputationallyIndistinguishable
      (fun n => (ProbComp.eval (keyGen gen n)).map Prod.fst) (publicKeyLaw setup))
    (hQR : QuadraticResiduosityHard setup) :
    Negligible fun n =>
      Encryption.advantage (Encryption.game (keyGen gen) encrypt constBitAdversary) n :=
  indcpa_goldwasserMicali hsize hkeys hQR constBitAdversary constBitAdversary_isPPT

noncomputable def constWordAdversary : Encryption.WordAdversary where
  choose _ _ := pure (([false, false], [true, false]), [])
  guess _ _ _ := pure true

theorem constWordAdversary_isPPT : constWordAdversary.IsPPT where
  choose :=
    (ComputableInPolyTime.const (([false, false], [true, false]), ([] : List Bool))).isPPTOn
  guess := (ComputableInPolyTime.const true).isPPTOn

example : IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
    (fun input => qrWordDistinguisher id constWordAdversary input.1 input.2) :=
  isPPTOn_qrWordDistinguisher .id' constWordAdversary_isPPT

example {setup : ℕ → PMF ModulusDesc} {gen : ℕ → ProbComp KeyDesc}
    (hsize : ∀ n, ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hkeys : ComputationallyIndistinguishable
      (fun n => (ProbComp.eval (keyGen gen n)).map Prod.fst) (publicKeyLaw setup))
    (hQR : QuadraticResiduosityHard setup) :
    Negligible fun n =>
      Encryption.advantage
        (Encryption.gameOn (validBoundedWords id) (keyGen gen) encryptWord constWordAdversary)
        n :=
  indcpaOn_goldwasserMicali_bits .id' hsize hkeys hQR constWordAdversary constWordAdversary_isPPT

end ComplexityTests.Crypto.GoldwasserMicali
