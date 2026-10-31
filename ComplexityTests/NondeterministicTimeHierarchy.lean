/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.Hierarchy.NondeterministicTime

/-! The coarse nondeterministic time hierarchy on concrete degrees. The lazy diagonal for degree
`1` is in nondeterministic time `O((n + 1) ^ 20)` and not in nondeterministic linear time, so the
two classes differ; degree `0` separates constant from `O((n + 1) ^ 14)` nondeterministic time.
The verifier rejects inputs without a short description, such as the empty input. -/

public section

namespace ComplexityTests.NondeterministicTimeHierarchy

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-- The lazy diagonal for degree `1` separates nondeterministic linear time from nondeterministic
time `O((n + 1) ^ 20)`, at the separating problem itself. -/
example : lazyDiagonal 1 ∈ NTIME encBits (fun n => (n + 1) ^ 20) ∧
    lazyDiagonal 1 ∉ NTIME encBits (fun n => (n + 1) ^ 1) :=
  ⟨lazyDiagonal_mem_NTIME 1, lazyDiagonal_notMem_NTIME 1⟩

/-- Nondeterministic linear time is strictly inside nondeterministic time `O((n + 1) ^ 20)`. -/
example : NTIME encBits (fun n => n + 1) ⊂ NTIME encBits fun n => (n + 1) ^ 20 := by
  simpa using NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le (d := 1) (e := 20) le_rfl

/-- Nondeterministic constant time is strictly inside nondeterministic time `O((n + 1) ^ 14)`. -/
example : NTIME encBits (fun _ => 1) ⊂ NTIME encBits fun n => (n + 1) ^ 14 := by
  simpa using NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le (d := 0) (e := 14) le_rfl

/-- The empty input carries no short description, so the verifier rejects it with every
certificate, and the empty input is not in the lazy diagonal. -/
example (d : ℕ) (v : List Bool) : LazyDiagonal.verifier d ([], v) = false := by
  simp [LazyDiagonal.verifier, Diagonal.shortDesc, unframe]

example (d : ℕ) : [] ∉ lazyDiagonal d := by
  simp [lazyDiagonal, LazyDiagonal.verifier, Diagonal.shortDesc, unframe]

end ComplexityTests.NondeterministicTimeHierarchy
