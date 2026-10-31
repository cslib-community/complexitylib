/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.Promise
import ComplexityTests.PromisePP

/-! The conditional counting simulation on a genuinely partial promise.

The completion contains `[true]` and excludes `[false]`; its one machine retains both resource
bounds. The verifier's exact tie on the empty word is checked in `ComplexityTests.PromisePP`.
-/

namespace ComplexityTests.PromiseCountingSimulation

open Cslib.Complexity Cslib.Complexity.CountingSimulation Turing.MultiTapeTM
  Cslib.Circuits.Frontier.ExplicitTensorNetwork ComplexityTests.PromiseProbabilistic
  ComplexityTests.PromisePP

/-- A concrete partial promise gets a total deterministic completion with the joint bounds.
The contraction algorithm is the only unproved interface assumed by this client. -/
example (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
    ExplicitAdmissible) :
    ∃ (L : Set (List Bool)) (k C d : ℕ), [true] ∈ L ∧ [false] ∉ L ∧
      DecidableInTimeAndSpace L encBits
        (fun a => 2 ^ (C * ((a.length + 1) ^ (k + 2) + 1) /
          Nat.sqrt (Nat.log 2 ((a.length + 1) ^ (k + 2) + 1))))
        (fun a => ((a.length + 1) ^ (k + 2) + 1) ^ d) := by
  have hQ : partialSingletonBit ∈ PromiseBPP encBits :=
    ⟨1, partialVerifier, partialVerifier_polyTime,
      solvesWithBoundedError_partialSingletonBit⟩
  obtain ⟨L, k, C, d, hyes, hno, h⟩ :=
    exists_completion_of_mem_PromiseBPP_of_contractionAlgorithm A hQ
  refine ⟨L, k, C, d, hyes rfl, ?_, h⟩
  exact Set.disjoint_right.mp hno rfl

end ComplexityTests.PromiseCountingSimulation
