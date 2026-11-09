/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.NumberTheory.AKS.Criterion

/-! The AKS identity on a prime and a composite, the binomial divisibility, the AKS tests on a
prime, and `Passes` as `PassesUpTo` at the paper's bound. -/

namespace ComplexityTests.AKSCriterion

open Polynomial Cslib.AKS

-- The identity holds for the prime `7`, fails for the composite `4` with unit `1`, `4 ∤ C(4, 2)`,
-- the prime `7` passes the AKS tests for every `r`, and `8 = 2³` fails step 1.
example (r : ℕ) :
    (X + C (1 : ZMod 7)) ^ 7 = X ^ 7 + C 1 ∧
      (X + C (1 : ZMod 4)) ^ 4 ≠ X ^ 4 + C 1 ∧
      ¬ 4 ∣ Nat.choose 4 2 ∧
      Passes 7 r ∧
      ¬ Passes 8 3 :=
  ⟨add_pow_eq_of_prime (by decide) 1,
    fun h => absurd ((prime_iff_add_pow_eq (by norm_num) isUnit_one).mpr h) (by decide),
    not_dvd_choose_of_prime_dvd Nat.prime_two (by norm_num) (by norm_num),
    passes_of_prime (by decide) r,
    fun h => h.1 ⟨2, 3, by norm_num, by norm_num⟩⟩

-- `Passes` is `PassesUpTo` at the paper's bound `⌊√φ(r) log₂ n⌋`, and the prime `7` passes the
-- tests up to every bound.
example (n r A : ℕ) : (Passes n r ↔ PassesUpTo n r (numTests n r)) ∧ PassesUpTo 7 r A :=
  ⟨Iff.rfl, passesUpTo_of_prime (by decide) r A⟩

end ComplexityTests.AKSCriterion
