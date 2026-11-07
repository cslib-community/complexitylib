/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.NumberTheory.AKS.Criterion
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import Mathlib.Data.Nat.Log

/-!
# Deciding perfect powers

Step 1 of the AKS algorithm [Agrawal, Kayal, Saxena, Section 4][AKS2004] asks whether `n = a ^ b`
for some `b > 1`. For `n ≥ 2` such an `a` is at least `2`, so `b ≤ log₂ n`, and `n` is a `b`-th
power exactly when it is the `b`-th power of its integer `b`-th root `Nat.nthRoot b n`. This makes
`Cslib.AKS.IsPerfectPower` decidable by a bounded search.

## Main results

* `Cslib.AKS.isPerfectPower_iff_nthRoot`: perfect powers through integer roots.
* `Cslib.AKS.decidablePredIsPerfectPower`: the resulting decision procedure.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.AKS

/-- For `n ≥ 2`, `n` is a perfect power exactly when it is the `b`-th power of its integer `b`-th
root for some `2 ≤ b ≤ log₂ n`. -/
theorem isPerfectPower_iff_nthRoot {n : ℕ} (hn : 2 ≤ n) :
    IsPerfectPower n ↔ ∃ b < Nat.log 2 n + 1, 2 ≤ b ∧ Nat.nthRoot b n ^ b = n := by
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    have ha : 2 ≤ a := by
      rcases a with _ | _ | a
      · simp [zero_pow (by omega : b ≠ 0)] at hn
      · simp at hn
      · omega
    refine ⟨b, Nat.lt_succ_of_le (Nat.le_log_of_pow_le one_lt_two (Nat.pow_le_pow_left ha b)),
      hb, ?_⟩
    rw [Nat.nthRoot_pow (by omega)]
  · rintro ⟨b, -, hb, h⟩
    exact ⟨_, b, hb, h⟩

/-- `0` and `1` are perfect powers: `0 = 0 ^ 2` and `1 = 1 ^ 2`. -/
theorem isPerfectPower_of_lt_two {n : ℕ} (hn : n < 2) : IsPerfectPower n := by
  interval_cases n
  · exact ⟨0, 2, one_lt_two, rfl⟩
  · exact ⟨1, 2, one_lt_two, rfl⟩

/-- Perfect powers are decidable, by the bounded search of `isPerfectPower_iff_nthRoot`. -/
instance decidablePredIsPerfectPower : DecidablePred IsPerfectPower := fun n =>
  if hn : 2 ≤ n then decidable_of_iff _ (isPerfectPower_iff_nthRoot hn).symm
  else isTrue (isPerfectPower_of_lt_two (by omega))

end Cslib.AKS
