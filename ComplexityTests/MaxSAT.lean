/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.MaxSAT.PolyTime

/-! # Exact MAX-SAT compilation: checked examples

The sample has opposing unit clauses, a tautological clause, an empty clause, and a nontrivial
last clause. It checks threshold multiplicities and free declared variables, including zero
clauses, zero variables, an impossible cutoff, and an invalid reference's documented default.
-/

namespace ComplexityTests.MaxSAT

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.Complexity.MaxSAT
  Turing.MultiTapeTM

/-- Every assignment satisfies the first pair's exactly one clause and the tautology; the last
clause contributes one more unless `x₀` is false and `x₂` is true. -/
def sample : Instance :=
  (3, [[(0, true)], [(0, false)], [(1, true), (1, false)], [], [(2, false), (0, true)]])

example : score sample ![false, false, true] = 2 ∧
    score sample ![true, false, true] = 3 := by decide

example : thresholdCount sample 0 = 8 ∧ thresholdCount sample 2 = 8 ∧
    thresholdCount sample 3 = 6 ∧ thresholdCount sample 4 = 0 := by decide

example : (thresholdCircuit sample 3).satCount interpretation = 6 := by
  rw [satCount_thresholdCircuit]
  decide

-- An unused declared variable doubles every threshold count.
example : thresholdCount (4, sample.2) 3 = 12 := by decide

-- Empty formulas still count all declared assignments at cutoff zero.
example : thresholdCount (2, []) 0 = 4 ∧ thresholdCount (2, []) 1 = 0 := by decide
example : thresholdCount (0, []) 0 = 1 ∧ thresholdCount (0, [[]]) 1 = 0 := by decide

-- Repeated clauses carry multiplicity in the objective.
example : score (1, [[(0, true)], [(0, true)]]) ![true] = 2 ∧
    thresholdCount (1, [[(0, true)], [(0, true)]]) 2 = 1 := by decide

-- A reference outside the declared range reads false, preserving the specified total semantics.
example : thresholdCount (1, [[(7, false)]]) 1 = 2 ∧
    thresholdCount (1, [[(7, true)]]) 1 = 0 := by decide

-- The whole native counter, specialized to the checked nontrivial count.
example : ∃ (count : Query → ℕ) (A e b : ℕ), count (sample, 3) = 6 ∧
    ComputableInO count encQuery encNat
      (fun p => 2 ^ (A * (workSize p.1 + 1) / Nat.sqrt (Nat.log 2 (workSize p.1 + 2))) *
        ((encQuery p).length + 1) ^ e)
      (fun p => ((encQuery p).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ := exists_thresholdCounter
  refine ⟨count, A, e, b, ?_, hinO⟩
  rw [hspec]
  decide

end ComplexityTests.MaxSAT
