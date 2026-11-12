/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/Primrec/List.lean`)

public import CslibFrontier.Init
public import Mathlib.Computability.Primrec.List

/-!
# Primitive recursiveness of list relations

## Main results

* `Primrec.list_isPrefix`: the list prefix relation `<+:` is primitive recursive.
-/

public section

namespace Primrec

/-- The list prefix relation `<+:` is primitive recursive. -/
theorem list_isPrefix {α : Type*} [Primcodable α] :
    PrimrecRel (fun l₁ l₂ : List α => l₁ <+: l₂) := by
  have H : PrimrecRel (fun l₁ l₂ : List α => l₂.take l₁.length = l₁) :=
    Primrec.eq.comp (list_take.comp (list_length.comp fst) snd) fst
  exact H.of_eq fun _ => by simp [List.prefix_iff_eq_take, eq_comm]

end Primrec
