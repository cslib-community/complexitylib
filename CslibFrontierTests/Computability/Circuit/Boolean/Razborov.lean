/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.ACC0
public import CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice
public import CslibFrontier.Computability.Circuit.Boolean.Razborov.Natural

/-!
# Tests for Razborov's rank property against AC⁰[2]

Non-vacuity witnesses for the rank test of
`CslibFrontier.Computability.Circuit.Boolean.Razborov.RankProperty`, concrete values of the middle
slice of `CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice`, the constructive and
large half of `CslibFrontier.Computability.Circuit.Boolean.Razborov.Natural` along the middle level,
and the separation `P ⊄ AC⁰[p]` for every prime `p`, combining the middle slice with parity for odd
primes.
-/

public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.Razborov

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Razborov Cslib.Complexity
  Turing.MultiTapeTM BitString

/-! ### The rank test -/

-- The identity witness passes the rank test.
example : exactWeight 2 ∈ rankTest 3 1 := exactWeight_mem_rankTest 1

-- The constant-false function has zero matrix, so it fails the rank test at level `1` on three
-- inputs: the test is not trivially true.
example : (fun _ => false : BooleanFunction 3) ∉ rankTest 3 1 := by
  rw [mem_rankTest]
  have h : (zeroSumMatrix 1 fun x => bitVal (ZMod 2) ((fun _ => false : BooleanFunction 3) x)) =
      0 := by
    ext I J
    simp only [zeroSumMatrix_apply, bitVal_false, Finset.sum_const_zero, Matrix.zero_apply]
  rw [h, Matrix.rank_zero]
  decide

-- Largeness at a concrete size: at least half of the `2 ^ 2 ^ 3` functions pass.
example : 2 ^ 2 ^ 3 ≤ 2 * (rankTest 3 1).ncard := two_pow_two_pow_le_two_mul_ncard_rankTest 3 1

/-! ### The middle slice -/

-- At length `3` the gap is `0`: the slice is the strings with exactly two zeros.
example : middleSlice 3 ![true, false, false] = true := by
  rw [middleSlice_eq_true_iff, sliceLevel_eq, show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, Nat.sqrt_eq']
  decide

example : middleSlice 3 ![true, true, false] = false := by
  rw [Bool.eq_false_iff, ne_eq, middleSlice_eq_true_iff, sliceLevel_eq,
    show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, Nat.sqrt_eq']
  decide

-- `99` is the first length with a positive gap: the level is `50 - 1`.
example : sliceLevel 99 = 49 := by
  rw [sliceLevel_eq, show (99 + 1 : ℕ) = 10 ^ 2 by norm_num, Nat.sqrt_eq']
  norm_num

/-! ### Constructivity and naturalness -/

-- The rank test on three inputs at level `1`, from its truth table of length `8`, within
-- `173 · 8 ^ 3` gates.
example : complexity interpretation (single (truthTableTest (rankTest 3 1))) ≤ 173 * 8 ^ 3 :=
  complexity_truthTableTest_rankTest_le 3 1

-- The identity witness has the rank property along the middle level.
example (n : ℕ) : exactWeight (n - sliceLevel n) ∈ rankProperty sliceLevel n := by
  rw [rankProperty_apply]
  exact exactWeight_mem_rankTest _

-- Along the middle level the rank property is `P/poly`-natural.
example : NaturalProof.IsNatural PPoly (rankProperty sliceLevel) :=
  isNatural_PPoly_rankProperty sliceLevel

/-! ### `P ⊄ AC⁰[p]` for every prime `p` -/

example {p : ℕ} [Fact p.Prime] :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0Mod p := by
  rcases eq_or_ne p 2 with rfl | hp2
  · exact exists_mem_P_notMem_AC0Mod_two
  · exact exists_mem_P_notMem_AC0Mod hp2

end CslibFrontierTests.Computability.Circuit.Boolean.Razborov
