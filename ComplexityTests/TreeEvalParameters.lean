/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of uniform packed parameter initialization)

public import Complexity.Computability.TreeEval.Ary.Packed.ParametersSpace

/-!
# Native packed parameter initialization

Prime testing includes zero, one, a prime and a prime square. Concrete parameter choices compare
the actual counter search with the least-prime definition used by the packed algebra, including
zero widths and a padded chunk. The native certificate is uniform in both runtime inputs.
-/

public section

namespace ComplexityTests.TreeEvalParameters

open Turing MultiTapeTM ComputableInSpace Cslib.TreeEval.Ary.Packed

example : PrimeSearch.isPrime 0 = false := rfl
example : PrimeSearch.isPrime 1 = false := rfl
example : PrimeSearch.isPrime 2 = true := rfl
example : PrimeSearch.isPrime 49 = false := rfl
example : PrimeSearch.isPrime 97 = true := rfl

example : fieldModulus 1 1 = 3 := by
  rw [fieldModulus_eq_boundedFirstPrime]
  rfl

example : fieldModulus 2 3 = 17 := by
  rw [fieldModulus_eq_boundedFirstPrime]
  rfl

example : fieldModulus 0 0 = 2 := by
  rw [fieldModulus_eq_boundedFirstPrime]
  rfl

example : chunkWidth 2 5 = 4 ∧ chunkCount 2 5 = 2 := by decide

example : PrimeSearch.boundedFirstPrime 8 11 = 11 := rfl

-- The second argument bounds counter iterations, not the returned candidate's value.
example : PrimeSearch.boundedFirstPrime 100 1 = 101 := rfl

example : parameters 0 0 = (0, 0, 1, 2) := by
  rw [parameters, fieldModulus_eq_boundedFirstPrime]
  rfl

example : ComputableInSpace (fun q : ℕ × ℕ => parameters q.1 q.2)
    (encPair encNat encNat) encParameters (fun q => (encPair encNat encNat q).length) :=
  parameters_inSpace

end ComplexityTests.TreeEvalParameters
