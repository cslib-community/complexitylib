/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

module
-- upstream: local-only (comparator proofs from the library)

public import ComplexityComparator.Automation.Statements
import Complexity.Crypto.Computational.GoldreichLevin.HardCore

/-!
# Library proofs of the independent bitstring contracts

The two source theorems in `GoldreichLevin.HardCore` unfold their algorithms and finish with
`polytime`. These wrappers require their machine contracts to agree with the independently
written statements by definitional equality.
-/

public section

namespace ComplexityComparator.Automation

/-- Reuse the existing `polytime`-generated proof for half-word function padding. -/
theorem padded_function : PaddedFunction := by
  intro f hf
  exact Cslib.Crypto.GoldreichLevin.polyTime_paddedFunction hf

/-- Reuse the existing `polytime`-generated proof for the inner product of two halves. -/
theorem dot_product_halves : DotProductHalves := by
  exact Cslib.Crypto.GoldreichLevin.polyTime_paddedPredicate

end ComplexityComparator.Automation
