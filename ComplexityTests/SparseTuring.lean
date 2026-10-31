/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Complexity.Classes.Oracle.ListOracle
import Complexity.Computability.Complexity.Classes.Sparse.Turing

/-! # Finite-list oracles and sparse Turing-hard sets -/

namespace ComplexityTests.SparseTuring

open Cslib Cslib.BitString Cslib.Complexity Cslib.Circuits.Boolean Cslib.Logic.PL Turing.MultiTapeTM

/-- The words consisting only of `true`s, a sparse language. -/
private def unary : Set (List Bool) := {w | ∀ b ∈ w, b = true}

private theorem unary_mem_SPARSE : unary ∈ SPARSE encBits := mem_SPARSE_of_unary fun _ h => h

-- The short members of `unary` are exactly the all-`true` words of bounded length.
example : [true, true] ∈ shortMembers unary 2 := by
  simp [unary]

example : [true, true] ∉ shortMembers unary 1 := by
  simp

example : [true, false] ∉ shortMembers unary 5 := by
  simp [unary]

-- Their encoded listing has polynomial length.
example : ∃ c d : ℕ, ∀ n, (encList encBits (shortMembers unary n)).length ≤ c * (n + 1) ^ d :=
  exists_length_encList_shortMembers_le unary_mem_SPARSE

-- A finite list replaces the oracle of the one-request decider of `unary`: a list agreeing with
-- `unary` on short words gives the right answer on every input.
open Classical in
example : ∃ (F : List Bool × List (List Bool) → Bool) (q : Polynomial ℕ),
    ComputableInPolyTime F (encPair encBits (encList encBits)) encBool ∧
      ∀ w, F (w, shortMembers unary (q.eval w.length)) = decide (w ∈ unary) := by
  obtain ⟨F, q, hF, hFS⟩ := (computableInPolyTimeWithOracle_mem unary).exists_listOracle_bool
  refine ⟨F, q, hF, fun w => hFS w _ fun v hv => ?_⟩
  rw [encBits_apply] at hv
  simp [hv]

-- `P` relative to the sparse oracle `unary` is in `P/poly`; in particular `unary` itself is.
example : unary ∈ PPolyOn encBits :=
  PWithOracle_subset_PPolyOn unary_mem_SPARSE encBits (mem_PWithOracle_self unary)

-- The collapse applies to every sparse oracle to which `SAT` is Turing reducible.
example (hSAT : SAT ∈ PWithOracle unary encCNF) :
    PH encBits = SigmaP 2 encBits :=
  PH_eq_SigmaP_two_of_SAT_mem_PWithOracle unary_mem_SPARSE hSAT encBits

end ComplexityTests.SparseTuring
