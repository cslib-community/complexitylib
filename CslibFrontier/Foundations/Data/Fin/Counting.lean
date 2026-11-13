/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, Mathlib.Data.Fintype.Fin)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Counting tuples by their first coordinate

`Fin.card_filter_zero_tail` counts a predicate on a nonempty-length tuple by fixing its first
coordinate and counting the remaining tails. Extracted from the multilinearity-testing proof
so that cube-cardinality arguments can reuse it without importing a coding-theory application.
-/

public section

namespace Fin

open Finset

variable {F : Type*} [Fintype F] {n : ℕ}

/-- Counting the points of `F ^ (n + 1)` by their first coordinate and their tail. -/
theorem card_filter_zero_tail (P : F → (Fin n → F) → Prop) [∀ t, DecidablePred (P t)] :
    #{x : Fin (n + 1) → F | P (x 0) (Fin.tail x)} = ∑ t, #{y : Fin n → F | P t y} := by
  simp only [card_filter]
  rw [← (Fin.consEquiv fun _ => F).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]

end Fin
