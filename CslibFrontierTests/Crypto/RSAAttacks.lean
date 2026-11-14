/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

import CslibFrontier.Crypto.Computational.RSAAttacks
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the attacks on plain RSA
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RSAAttacks

open Cslib Cslib.Crypto

/-- Toy RSA instance `N = 3 * 11 = 33`, `e = 3`, `d = 7` (`3 * 7 ≡ 1 [MOD 20]`). -/
def rsa33 : RSADesc :=
  { p := 3, q := 11, e := 3, d := 7, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-! ### Malleability -/

example : rsaEval 33 3 (4 * 5) = rsaEval 33 3 4 * rsaEval 33 3 5 % 33 := by decide

example : rsaInvert 33 7 (rsaEval 33 3 4 * rsaEval 33 3 5 % 33) = 20 := by decide

example : rsaInvert rsa33.modulus rsa33.d
    (rsaEval rsa33.modulus rsa33.e 4 * rsaEval rsa33.modulus rsa33.e 5 % rsa33.modulus) = 20 :=
  rsaInvert_rsaEval_mul rsa33 4 5

/-! ### Common modulus -/

/-- Encryptions of `5` under `N = 33` with the coprime exponents `3` and `7` reveal `5`. -/
example : commonModulusAttack 33 3 7 (rsaEval 33 3 5) (rsaEval 33 7 5) = 5 :=
  commonModulusAttack_rsaEval (by decide) (by decide)

example : rsaEval 33 3 5 = 26 ∧ rsaEval 33 7 5 = 14 := by decide

/-! ### Small messages and the broadcast attack -/

/-- `4 ^ 3 = 64 < 77`, so the ciphertext of `4` under `(77, 3)` is `64` over the integers. -/
example : rsaEval 77 3 4 = 64 := rsaEval_eq_pow_of_pow_lt (by decide)

example {m' : ℕ} (h : m' ^ 3 = rsaEval 77 3 4) : m' = 4 :=
  eq_of_pow_eq_rsaEval (by decide) (by decide) h

/-- The moduli `5, 7, 11` of three receivers. -/
def moduli : Fin 3 → ℕ := ![5, 7, 11]

theorem moduli_pairwise : [0, 1, 2].Pairwise (Function.onFun Nat.Coprime moduli) := by
  decide

/-- Broadcasting `4` with `e = 3` to the moduli `5, 7, 11`: `4 ^ 3 = 64 < 385`, so the Chinese
remainder combination of the three ciphertexts is `64`. -/
example : (Nat.chineseRemainderOfList (fun i => rsaEval (moduli i) 3 4) moduli [0, 1, 2]
    moduli_pairwise : ℕ) = 64 :=
  chineseRemainderOfList_rsaEval_eq_pow _ moduli_pairwise (by decide) (by decide)

/-! ### Factoring from secret data -/

example : factorOfTotient 33 20 = (11, 3) := by
  rw [factorOfTotient, show (33 + 1 - 20) ^ 2 - 4 * 33 = 8 * 8 from rfl, Nat.sqrt_eq]

example : factorOfTotient rsa33.modulus rsa33.totient = (11, 3) := by
  rw [RSADesc.factorOfTotient_eq]
  decide

example : 2 ^ (rsa33.e * rsa33.d - 1) ≡ 1 [MOD rsa33.modulus] :=
  rsa33.pow_mul_sub_one_modEq_one (by decide)

/-- `10 ^ 2 ≡ 1 [MOD 33]` and `10 ≢ ±1`, so `gcd(9, 33) = 3` and `gcd(11, 33) = 11` are proper
factors. -/
example : 1 < Nat.gcd (10 - 1) rsa33.modulus ∧ Nat.gcd (10 - 1) rsa33.modulus < rsa33.modulus :=
  rsa33.gcd_sub_one_proper (by decide) (by decide) (by decide)

example : 1 < Nat.gcd (10 + 1) rsa33.modulus ∧ Nat.gcd (10 + 1) rsa33.modulus < rsa33.modulus :=
  rsa33.gcd_add_one_proper (by decide) (by decide) (by decide)

/-- The general factoring lemma `gcd_sub_one_proper_of_sq_modEq_one` also applies to non-RSA
composite moduli such as `N = 8` (`3 ^ 2 ≡ 1 [MOD 8]` and `3 ≢ ±1 [MOD 8]`) and `N = 45`
(`19 ^ 2 ≡ 1 [MOD 45]`). -/
example : 1 < Nat.gcd (3 - 1) 8 ∧ Nat.gcd (3 - 1) 8 < 8 :=
  gcd_sub_one_proper_of_sq_modEq_one (by decide) (by decide) (by decide)

example : 1 < Nat.gcd (19 - 1) 45 ∧ Nat.gcd (19 - 1) 45 < 45 ∧
    1 < Nat.gcd (19 + 1) 45 ∧ Nat.gcd (19 + 1) 45 < 45 :=
  ⟨(gcd_sub_one_proper_of_sq_modEq_one (by decide) (by decide) (by decide)).1,
   (gcd_sub_one_proper_of_sq_modEq_one (by decide) (by decide) (by decide)).2,
   (gcd_add_one_proper_of_sq_modEq_one (by decide) (by decide) (by decide)).1,
   (gcd_add_one_proper_of_sq_modEq_one (by decide) (by decide) (by decide)).2⟩

example : Nat.gcd (10 - 1) 33 = 3 := by decide

end CslibFrontierTests.Crypto.RSAAttacks
