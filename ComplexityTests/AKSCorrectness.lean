/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.NumberTheory.AKS.Correctness

/-! Correctness of the AKS tests: a satisfiable instance of the order hypothesis. -/

namespace ComplexityTests.AKSCorrectness

open Cslib.AKS

/-- `31 ≡ 2 (mod 29)` has multiplicative order `28` modulo `29`. -/
theorem orderOf_thirtyOne : orderOf (31 : ZMod 29) = 28 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

/-- `log₂² 31 < 25 < 28`, so `r = 29` satisfies the order hypothesis for `n = 31`. -/
theorem logb_sq_lt : Real.logb 2 (31 : ℕ) ^ 2 < orderOf ((31 : ℕ) : ZMod 29) := by
  have h31 : Real.logb 2 (31 : ℕ) < 5 := by
    rw [Real.logb_lt_iff_lt_rpow one_lt_two (by norm_num)]
    norm_num
  have h0 : 0 ≤ Real.logb 2 (31 : ℕ) := Real.logb_nonneg one_lt_two (by norm_num)
  rw [show ((31 : ℕ) : ZMod 29) = 31 from rfl, orderOf_thirtyOne]
  push_cast at h31 h0 ⊢
  nlinarith

-- The hypotheses of `prime_of_passes` hold together: `31` passes for `r = 29`.
example : Passes 31 29 ∧ (Nat.Prime 31 ↔ Passes 31 29) :=
  ⟨passes_of_prime (by decide) 29, prime_iff_passes (by norm_num) logb_sq_lt⟩

end ComplexityTests.AKSCorrectness
