/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/BigOperators/Fin.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin

/-!
# Counting in an appended tuple

The number of entries of `Fin.append x y` satisfying a predicate is the number for `x` plus the
number for `y`.

## Main results

* `Fin.card_filter_append`: counting entries satisfying a predicate across `Fin.append`.
-/

public section

namespace Fin

open Finset

/-- The entries of `Fin.append x y` satisfying `P` are those of `x` and those of `y`. -/
theorem card_filter_append {α : Type*} {m p : ℕ} (P : α → Prop) [DecidablePred P] (x : Fin m → α)
    (y : Fin p → α) :
    #{i | P (Fin.append x y i)} = #{i | P (x i)} + #{j | P (y j)} := by
  simp only [card_filter]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

end Fin
