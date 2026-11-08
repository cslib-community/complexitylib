/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Computational.Paillier
import Complexity.Crypto.Computational.Paillier.Security
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Paillier encryption

The arithmetic of [KatzLindell2020], Example 15.12 (`N = 187 = 11 * 17`, `m = 175`, `r = 83`) is
checked by evaluation. The factor pair `(11, 13)` is a valid description of a balanced modulus,
and the premises of the efficiency, correctness and homomorphism theorems are satisfiable: the
constant modulus generator for `N = 143` is uniform strict PPT, and its key pair is in the support
of key generation. For the IND-CPA reduction, the admissibility predicate is checked by evaluation,
and the reduction distinguisher and the security theorem are applied to a concrete adversary.
-/

namespace ComplexityTests.Crypto.Paillier

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Paillier BalancedModulus
open Turing.MultiTapeTM

/-! ### [KatzLindell2020], Example 15.12 -/

/-- Encrypting `m = 175` with randomness `r = 83` under `N = 187` gives `c = 23911`. -/
example : ciphertext 187 175 83 = 23911 := by decide

/-- The randomness `83` is a unit modulo `187`, so encryption uses it as is. -/
example : unitOrOne 187 83 = 83 := by decide

/-- Decrypting `c = 23911` with `φ(187) = 160` recovers `m = 175`. -/
example : decryptNat 187 160 23911 = 175 := by decide

/-! ### Homomorphic addition, by evaluation -/

/-- The product of encryptions of `5` and `7` modulo `143 ^ 2` decrypts to `12`. -/
example : decryptNat 143 120 (ciphertext 143 5 2 * ciphertext 143 7 3 % 143 ^ 2) = 12 := by
  decide

/-- Plaintexts add modulo `N`: encryptions of `100` and `50` under `N = 143` combine to an
encryption of `7`. -/
example : decryptNat 143 120 (ciphertext 143 100 2 * ciphertext 143 50 3 % 143 ^ 2) = 7 := by
  decide

/-! ### A valid description and a constant modulus generator -/

private theorem size_eq_four {m : ℕ} (h₁ : 2 ^ 3 ≤ m) (h₂ : m < 2 ^ 4) : m.size = 4 :=
  le_antisymm (Nat.size_le.mpr h₂) (Nat.lt_size.mpr h₁)

/-- The balanced modulus `143 = 11 * 13`. -/
def d143 : Desc :=
  ⟨(11, 13), ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num,
    (size_eq_four (by norm_num) (by norm_num)).trans
      (size_eq_four (by norm_num) (by norm_num)).symm⟩⟩

example : d143.modulus = 143 := rfl

example : d143.totient = 120 := rfl

/-- `gcd(143, φ(143)) = 1` ([KatzLindell2020], Claim 15.7). -/
example : Nat.Coprime 143 (Nat.totient 143) := d143.coprime_totient

/-- The modulus generator that always outputs `d143`. -/
noncomputable def constGen : ℕ → ProbComp Desc := fun _ => pure d143

/-- The constant modulus generator is uniform strict PPT. -/
theorem isPPTOn_constGen : IsPPTOn encUnary encDesc constGen :=
  (ComputableInPolyTime.const _).isPPTOn

/-- Key generation over the constant generator is uniform strict PPT. -/
example : IsPPTOn encUnary (encPair encBits encBits) (keyGen constGen) :=
  isPPTOn_keyGen isPPTOn_constGen

/-- The key pair `(143, ⟨143, 120⟩)` is in the support of key generation. -/
theorem mem_support_keyGen_constGen (n : ℕ) :
    (encNat 143, encPair encNat encNat (143, 120)) ∈
      (ProbComp.eval (keyGen constGen n)).support := by
  simp only [keyGen, constGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    PMF.support_pure, Set.mem_singleton_iff]
  rfl

/-- Every encryption of `42` under `N = 143` decrypts to `42`. -/
example (n : ℕ) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n (encNat 143) 42)).support) :
    decrypt (encPair encNat encNat (143, 120)) ct = encNat 42 :=
  decrypt_encrypt (gen := constGen) (keys := (encNat 143, encPair encNat encNat (143, 120)))
    (mem_support_keyGen_constGen n) (by decide) hct

/-- Combining encryptions of `100` and `50` under `N = 143` gives a ciphertext that decrypts to
`7`. -/
example (n : ℕ) {ct₁ ct₂ : List Bool}
    (hct₁ : ct₁ ∈ (ProbComp.eval (encrypt n (encNat 143) 100)).support)
    (hct₂ : ct₂ ∈ (ProbComp.eval (encrypt n (encNat 143) 50)).support) :
    decrypt (encPair encNat encNat (143, 120)) (addCiphertexts (encNat 143) ct₁ ct₂) =
      encNat 7 := by
  have h := decrypt_addCiphertexts (gen := constGen)
    (keys := (encNat 143, encPair encNat encNat (143, 120))) (mem_support_keyGen_constGen n)
    hct₁ hct₂
  exact h.trans (by decide)

/-! ### Decisional composite residuosity assumption client -/

/-- The constant-true distinguisher is uniform strict PPT. -/
theorem isPPTOn_constDistinguisher :
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
      (fun _ => pure true) :=
  (ComputableInPolyTime.const true).isPPTOn

/-- Under the DCR assumption for any modulus generator `setup`, the constant distinguisher has
negligible advantage. -/
example (setup : ℕ → PMF Desc) (h : DCR setup) :
    Negligible (fun n => Game.advantage (dcrRealGame setup (fun _ _ => pure true) n)
      (dcrIdealGame setup (fun _ _ => pure true) n)) :=
  h (fun _ _ => pure true) isPPTOn_constDistinguisher

/-! ### IND-CPA security under decisional composite residuosity -/

/-- Both challenge messages must be below the modulus. -/
example : validMessages 0 (encNat 143) 5 142 = true := by
  rw [validMessages, ofBits_encNat]
  decide

example : validMessages 0 (encNat 143) 5 143 = false := by
  rw [validMessages, ofBits_encNat]
  decide

/-- The adversary that challenges with `0` and `1` and always guesses `true`. -/
noncomputable def constAdversary : Encryption.AdversaryOf ℕ where
  choose _ _ := pure ((0, 1), [])
  guess _ _ _ := pure true

theorem constAdversary_isPPT : constAdversary.IsPPT encNat where
  choose := (ComputableInPolyTime.const _).isPPTOn
  guess := (ComputableInPolyTime.const true).isPPTOn

/-- The reduction distinguisher built from a concrete adversary is uniform strict PPT. -/
example (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
      (fun input => dcrDistinguisher constAdversary bit input.1 input.2) :=
  isPPTOn_dcrDistinguisher constAdversary_isPPT bit

/-- Under DCR, for a generator whose primes have at least `n` bits, the concrete adversary has
negligible IND-CPA advantage. -/
example {gen : ℕ → ProbComp Desc}
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hDCR : DCR fun n => ProbComp.eval (gen n)) :
    Negligible fun n => Game.advantage
      (ProbComp.eval
        (Encryption.gameOn validMessages (keyGen gen) encrypt constAdversary false n))
      (ProbComp.eval
        (Encryption.gameOn validMessages (keyGen gen) encrypt constAdversary true n)) :=
  DCR.indcpaOn_paillier hsize hDCR constAdversary constAdversary_isPPT

/-! ### Axiom guards for headline results -/

/--
info: 'Cslib.Crypto.Paillier.coprime_totient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms coprime_totient

/--
info: 'Cslib.Crypto.Paillier.unitsEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unitsEquiv

/--
info: 'Cslib.Crypto.Paillier.one_add_pow_mul_pow_pow_totient' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms one_add_pow_mul_pow_pow_totient

/--
info: 'Cslib.Crypto.Paillier.isPPTOn_keyGen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isPPTOn_keyGen

/--
info: 'Cslib.Crypto.Paillier.isPPTOn_encrypt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isPPTOn_encrypt

/--
info: 'Cslib.Crypto.Paillier.computableInPolyTime_decrypt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms computableInPolyTime_decrypt

/--
info: 'Cslib.Crypto.Paillier.decrypt_encrypt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms decrypt_encrypt

/--
info: 'Cslib.Crypto.Paillier.decrypt_addCiphertexts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms decrypt_addCiphertexts

end ComplexityTests.Crypto.Paillier
