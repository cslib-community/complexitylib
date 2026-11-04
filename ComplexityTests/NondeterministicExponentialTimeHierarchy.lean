/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.Hierarchy.NondeterministicExponentialTime

/-! The coarse nondeterministic exponential time hierarchy on concrete exponents. The exponential
lazy diagonal for `k = 2` is in nondeterministic time `O(2 ^ (32 * n))` and not in nondeterministic
time `O(2 ^ (2 * n))`, the separation that Williams's witness-circuit argument for `E^NP` lower
bounds consumes (#1539); `k = 0` separates constant from `O(2 ^ (16 * n))` nondeterministic time.
The verifier rejects inputs without a short description, such as the empty input. -/

public section

namespace ComplexityTests.NondeterministicExponentialTimeHierarchy

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-- The exponential lazy diagonal for `k = 2` separates nondeterministic time `O(2 ^ (2 * n))` from
nondeterministic time `O(2 ^ (32 * n))`, at the separating problem itself. -/
example : expLazyDiagonal 2 ∈ NTIME encBits (fun n => 2 ^ (32 * n)) ∧
    expLazyDiagonal 2 ∉ NTIME encBits (fun n => 2 ^ (2 * n)) :=
  ⟨expLazyDiagonal_mem_NTIME 2, expLazyDiagonal_notMem_NTIME 2⟩

/-- Nondeterministic time `O(2 ^ (2 * n))` is strictly inside nondeterministic time
`O(2 ^ (32 * n))`. -/
example : NTIME encBits (fun n => 2 ^ (2 * n)) ⊂ NTIME encBits fun n => 2 ^ (32 * n) :=
  NTIME_two_pow_ssubset_NTIME_two_pow_of_le le_rfl

/-- Nondeterministic constant time is strictly inside nondeterministic time `O(2 ^ (16 * n))`. -/
example : NTIME encBits (fun _ => 1) ⊂ NTIME encBits fun n => 2 ^ (16 * n) := by
  simpa using NTIME_two_pow_ssubset_NTIME_two_pow_of_le (k := 0) (e := 16) le_rfl

/-- `NE` is not contained in nondeterministic time `O(2 ^ (2 * n))`. -/
example : ¬NE encBits ⊆ NTIME encBits fun n => 2 ^ (2 * n) := fun h =>
  let ⟨_, hH, hH'⟩ := exists_mem_NE_notMem_NTIME_two_pow 2
  hH' (h hH)

/-- The empty input carries no short description, so the verifier rejects it with every
certificate, and the empty input is not in the exponential lazy diagonal. -/
example (k : ℕ) (v : List Bool) : ExpLazyDiagonal.verifier k ([], v) = false := by
  simp [ExpLazyDiagonal.verifier, Diagonal.shortDesc, unframe]

example (k : ℕ) : [] ∉ expLazyDiagonal k := by
  simp [expLazyDiagonal, ExpLazyDiagonal.verifier, Diagonal.shortDesc, unframe]

end ComplexityTests.NondeterministicExponentialTimeHierarchy
