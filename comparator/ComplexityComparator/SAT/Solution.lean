/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

module
-- upstream: local-only (comparator proofs from the library)

public import ComplexityComparator.SAT.Statements
import Complexity.Computability.Complexity.FineGrained.CountingNativeEndpoint
import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount

/-!
# Library proofs of the independently stated SAT contracts

The endpoint's existing proofs must match the independently supplied encodings, CNF semantics,
machine and resource conventions, and ETH statement by definitional equality.
-/

public section

namespace ComplexityComparator.SAT

/-- Reuse the exact native model-counting theorem at every fixed width. -/
theorem exact_count : ExactCount := fun k =>
  Cslib.Complexity.CountingNativeEndpoint.exists_modelCounter k

/-- Reuse the library's ETH consequence with the independently stated definition. -/
theorem not_eth : NotETH := Cslib.Complexity.CountingNativeEndpoint.not_ETH

end ComplexityComparator.SAT
