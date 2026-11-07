/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.Hierarchy.NondeterministicPolynomial

/-! The nondeterministic hierarchy at concrete integer degrees. Linear and quadratic
nondeterministic time differ, so some language separates them; the padding transfer applies to a
satisfiable collapse; and the shifted and conventional length conventions can be mixed. -/

public section

namespace ComplexityTests.NondeterministicPolynomialHierarchy

open Cslib.Complexity Turing.MultiTapeTM

/-- Nondeterministic linear time is strictly inside nondeterministic quadratic time, including
the linear lower boundary of the hierarchy. -/
example : NTIME encBits (fun n => n) ⊂ NTIME encBits (fun n => n ^ 2) := by
  simpa only [pow_one] using NTIME_pow_ssubset_NTIME_pow (a := 1) (b := 2) (by omega) (by omega)

/-- A language decidable in nondeterministic quadratic time but not in nondeterministic linear
time exists: the strict inclusion is witnessed by an actual separating language. -/
example : ∃ L : Set (List Bool),
    L ∈ NTIME encBits (fun n => n ^ 2) ∧ L ∉ NTIME encBits (fun n => n) := by
  obtain ⟨L, hL, hnot⟩ := Set.exists_of_ssubset
    (NTIME_pow_ssubset_NTIME_pow (a := 1) (b := 2) (by omega) (by omega))
  exact ⟨L, hL, by simpa only [pow_one] using hnot⟩

/-- The padding transfer applies to the satisfiable collapse at equal degrees, where it gives
`NTIME ((n + 1) ^ 2) ⊆ NTIME ((n + 1) ^ 5)`. -/
example : NTIME encBits (fun n => (n + 1) ^ 2) ⊆ NTIME encBits (fun n => (n + 1) ^ 5) := by
  simpa using NTIME_pow_mul_subset_of_subset (a := 2) (b := 2) (k := 1) (by omega) le_rfl le_rfl
    subset_rfl

/-- Ordinary and shifted input-length conventions can be mixed in hierarchy statements. -/
example : NTIME encBits (fun n => (n + 1) ^ 2) ⊂ NTIME encBits (fun n => n ^ 3) := by
  rw [NTIME_succ_pow_eq]
  exact NTIME_pow_ssubset_NTIME_pow (by omega) (by omega)

end ComplexityTests.NondeterministicPolynomialHierarchy
