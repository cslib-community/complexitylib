/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import Complexity.Computability.Complexity.Problems.Primes

/-!
# Bridge for the PRIMES formal abstract

Connects the plain native-machine class `P` of `PrimesAbstract.lean`, over the shared binary
encoding of naturals, to `Cslib.Complexity.primes_mem_P`. The decider behind that theorem is the
AKS algorithm on the word RAM (`Cslib.Algorithms.WordRAM.AKS.program`, correct by
`Cslib.Algorithms.WordRAM.AKS.answers`), simulated by a multi-tape Turing machine through
`Cslib.WordRAM.Program.DecidesInTime.mem_P_of_width`.
-/

namespace ComplexityAbstracts.PrimesBridge

open ComplexityTests.Abstracts

/-- The primes are decided by a polynomial-time function on binary naturals, stated over the
shared foundations. -/
theorem primes_mem_P : ∃ f : ℕ → Bool,
    Computation.PolyTime f Encoding.encNat Encoding.encBool ∧ ∀ n, n.Prime ↔ f n = true :=
  Cslib.Complexity.primes_mem_P

end ComplexityAbstracts.PrimesBridge
