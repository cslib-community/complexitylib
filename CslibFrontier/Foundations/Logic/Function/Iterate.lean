/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Logic/Function/Iterate.lean`)

public import CslibFrontier.Init
public import Mathlib.Logic.Function.Iterate

/-!
# Transitivity of iterated function application

Iterated applications of a function compose across step counts (`Function.iterate_trans`).

## Main results

* `Function.iterate_trans`: if `f^[m] a = b` and `f^[n] b = c`, then `f^[n + m] a = c`.
-/

public section

namespace Function

variable {α : Type*}

/-- Iterated function applications compose across step counts. -/
theorem iterate_trans {f : α → α} {a b c : α} {m n : ℕ}
    (h₁ : f^[m] a = b) (h₂ : f^[n] b = c) : f^[n + m] a = c := by
  rw [Function.iterate_add_apply, h₁, h₂]

end Function
