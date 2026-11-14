/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.GoldwasserMicali
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Goldwasser–Micali public-key encryption

Concrete evaluation and non-vacuity checks for
`CslibFrontier.Crypto.Computational.GoldwasserMicali`:

* arithmetic encryption, Euler-criterion decryption, and homomorphic XOR at `N = 15 = 3 * 5`
  (`z = 2 ∈ QNR_{15}^{+1}`) and at the Blum modulus `N = 21 = 3 * 7` (`z = 20 = -1 mod 21`);
* support-level correctness, XOR homomorphism, bitwise multi-bit encryption, and Exercise 15.11
  distributional equality / re-randomization on the Blum key `k21`;
* two bad-`z` counterexamples at `N = 21`: `z = 2 ∈ J_{21}^{-1}` is still decryptable by `(3, 7)`
  yet broken with exact IND-CPA advantage `1` (hence non-negligible) by the certified uniform
  strict-PPT `jacobiAttackAdversary`, whereas `z = 4 ∈ QR_{21}` breaks decryption correctness and
  collapses ciphertext distributions;
* Blum-modulus key generation `blumKeyGen` on the constant modulus `21`: its public key, uniform
  strict PPT, and correctness;
* concrete client instantiations of `isPPTOn_qrDistinguisher`, `isPPTOn_qrWordDistinguisher`,
  `isPPTOn_blumQRDistinguisher`, the headline `indcpa_blumGoldwasserMicali`, and the ideal-key-law
  statements `indistinguishable_publicKeyGame` and `indistinguishable_publicKeyWordGame`;
* joint satisfiability of the headline's premises `hblum` and `hsize`: the sampler
  `blumWitnessGen` draws Blum moduli with `n`-bit primes at every `n` (Dirichlet's theorem), so
  instantiating the headline at it leaves quadratic residuosity as the only premise.
-/

namespace CslibFrontierTests.Crypto.GoldwasserMicali

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

/-- The `KeyDesc` record keeps the former left-grouped triple encoding `((p, q), z)`. -/
example (k : KeyDesc) :
    encKeyDesc k = encPair (encPair encNat encNat) encNat ((k.p, k.q), k.z) := rfl
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

/-! ### Blum-modulus key generation on the constant modulus `21` -/

/-- `ModulusDesc` is encoded as the binary pair `(p, q)`. -/
example (d : ModulusDesc) : encModulusDesc d = encPair encNat encNat (d.p, d.q) := rfl

/-- The Blum public key at `N = 21` is the `k21` public key `⟨21, 20⟩`. -/
example : blumPublicKey 21 = encPair encNat encNat (k21.modulus, k21.z) := rfl

noncomputable def constBlumGen : ℕ → ProbComp ModulusDesc := fun _ => pure d21

theorem isBlum_constBlumGen (n : ℕ) :
    ∀ d ∈ (ProbComp.eval (constBlumGen n)).support, IsBlumModulus d.p d.q := by
  intro d hd
  simp only [constBlumGen, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hd
  exact hd ▸ isBlumModulus_3_7

example : IsPPTOn encUnary (encPair encBits encBits) (blumKeyGen constBlumGen) :=
  isPPTOn_blumKeyGen (ComputableInPolyTime.const d21).isPPTOn

example (n : ℕ) {keys : List Bool × List Bool}
    (hkeys : keys ∈ (ProbComp.eval (blumKeyGen constBlumGen n)).support) (m : Bool)
    {ct : List Bool} (hct : ct ∈ (ProbComp.eval (encrypt n keys.1 m)).support) :
    decrypt keys.2 ct = m :=
  decrypt_encrypt_blumKeyGen (isBlum_constBlumGen n) hkeys m hct

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

example : IsPPTOn encQRInput encBool
    (fun input => qrDistinguisher constBitAdversary input.1 input.2) :=
  isPPTOn_qrDistinguisher constBitAdversary_isPPT

example : IsPPTOn encQRInput encBool
    (fun input => blumQRDistinguisher constBitAdversary input.1 input.2) :=
  isPPTOn_blumQRDistinguisher constBitAdversary_isPPT

/-- The headline theorem: quadratic residuosity relative to a Blum-modulus generator with `n`-bit
primes is the only assumption. -/
example {gen : ℕ → ProbComp ModulusDesc}
    (hblum : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (gen n)) :
    Negligible fun n =>
      Encryption.advantage (Encryption.game (blumKeyGen gen) encrypt constBitAdversary) n :=
  indcpa_blumGoldwasserMicali hblum hsize hQR constBitAdversary constBitAdversary_isPPT

example {setup : ℕ → PMF ModulusDesc}
    (hsize : ∀ n, ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQR : QuadraticResiduosityHard setup) :
    Negligible fun n =>
      Game.advantage
        (Encryption.publicKeyGame (publicKeyLaw setup n) encrypt constBitAdversary false n)
        (Encryption.publicKeyGame (publicKeyLaw setup n) encrypt constBitAdversary true n) :=
  indistinguishable_publicKeyGame hsize hQR constBitAdversary constBitAdversary_isPPT

noncomputable def constWordAdversary : Encryption.WordAdversary where
  choose _ _ := pure (([false, false], [true, false]), [])
  guess _ _ _ := pure true

theorem constWordAdversary_isPPT : constWordAdversary.IsPPT where
  choose :=
    (ComputableInPolyTime.const (([false, false], [true, false]), ([] : List Bool))).isPPTOn
  guess := (ComputableInPolyTime.const true).isPPTOn

example : IsPPTOn encQRInput encBool
    (fun input => qrWordDistinguisher id constWordAdversary input.1 input.2) :=
  isPPTOn_qrWordDistinguisher .id' constWordAdversary_isPPT

example {setup : ℕ → PMF ModulusDesc}
    (hsize : ∀ n, ∀ d ∈ (setup n).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hQR : QuadraticResiduosityHard setup) :
    Negligible fun n =>
      Game.advantage
        (publicKeyWordGame id (publicKeyLaw setup n) constWordAdversary false n)
        (publicKeyWordGame id (publicKeyLaw setup n) constWordAdversary true n) :=
  indistinguishable_publicKeyWordGame .id' hsize hQR constWordAdversary constWordAdversary_isPPT

/-! ### The headline's premises `hblum` and `hsize` hold together

`constBlumGen` satisfies `hblum` but violates `hsize` for every `n ≥ 3`, since `Nat.size 3 = 2`.
The sampler `blumWitnessGen` below satisfies both premises at every `n`, by Dirichlet's theorem on
primes `≡ 3 (mod 4)`. So the headline's conditions on the modulus law are jointly satisfiable, and
at `blumWitnessGen` quadratic residuosity is its only remaining premise. The sampler is a
noncomputable choice: it witnesses satisfiability, not an efficient modulus generator, and nothing
here discharges the cryptographic assumption `hQR`. -/

/-- Dirichlet: there are Blum primes above every bound. -/
theorem exists_isBlumPrime_gt (m : ℕ) : ∃ p > m, IsBlumPrime p := by
  obtain ⟨p, hpm, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq m (q := 4) (a := 3) (by norm_num) (by decide)
  refine ⟨p, hpm, hp, ?_⟩
  rw [Int.ModEq] at hmod
  omega

/-- Every security parameter admits a Blum modulus with `n`-bit primes. -/
theorem exists_blumModulusDesc (n : ℕ) :
    ∃ d : ModulusDesc, IsBlumModulus d.p d.q ∧ n ≤ d.p.size ∧ n ≤ d.q.size := by
  obtain ⟨p, hpn, hp⟩ := exists_isBlumPrime_gt (2 ^ n)
  obtain ⟨q, hqp, hq⟩ := exists_isBlumPrime_gt p
  have hp3 := hp.2
  have hq3 := hq.2
  refine ⟨⟨p, q, hp.1, hq.1, by omega, by omega, by omega⟩, ⟨hp, hq, hqp.ne⟩, ?_, ?_⟩
  · exact (Nat.lt_size.mpr hpn.le).le
  · exact (Nat.lt_size.mpr (show 2 ^ n ≤ q by omega)).le

/-- A modulus sampler satisfying both premises `hblum` and `hsize` of the headline. -/
noncomputable def blumWitnessGen (n : ℕ) : ProbComp ModulusDesc :=
  pure (exists_blumModulusDesc n).choose

theorem isBlum_blumWitnessGen (n : ℕ) :
    ∀ d ∈ (ProbComp.eval (blumWitnessGen n)).support, IsBlumModulus d.p d.q := by
  intro d hd
  simp only [blumWitnessGen, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hd
  subst hd
  exact (exists_blumModulusDesc n).choose_spec.1

theorem size_blumWitnessGen (n : ℕ) :
    ∀ d ∈ (ProbComp.eval (blumWitnessGen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size := by
  intro d hd
  simp only [blumWitnessGen, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hd
  subst hd
  exact (exists_blumModulusDesc n).choose_spec.2

/-- At `blumWitnessGen`, quadratic residuosity is the headline's only premise. -/
example (hQR : QuadraticResiduosityHard fun n => ProbComp.eval (blumWitnessGen n)) :
    Encryption.INDCPA (blumKeyGen blumWitnessGen) encrypt :=
  indcpa_blumGoldwasserMicali isBlum_blumWitnessGen size_blumWitnessGen hQR

end CslibFrontierTests.Crypto.GoldwasserMicali
