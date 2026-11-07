/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

module
-- upstream: local-only (comparator proofs from the library)

public import ComplexityComparator.Basic.Statements
import Complexity.Computability.Reduction.ManyOne
import Complexity.Computability.Circuit.Complexity

/-! # Library proofs of the independent basic contracts -/

public section

namespace ComplexityComparator.Basic

universe u v w s

/-- The library's reduction composition proves the expanded membership-preservation contract. -/
theorem manyOneTrans : ManyOneTrans.{u, v, w} := by
  intro α β γ Good₁ Good₂ Good₃ A B C hcomp hAB hBC
  exact Cslib.Complexity.ManyOneReducibleBy.trans hcomp hAB hBC

/-- The library's gate lower bound proves the upstream circuit-complexity contract. -/
theorem nonprojectionNeedsGate : NonprojectionNeedsGate.{u, s} := by
  intro σ U I _ n f hf
  exact Cslib.Circuits.one_le_complexity_single (I := I) hf

end ComplexityComparator.Basic
