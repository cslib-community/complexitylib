/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Embedding.Basic

/-! # The single-symbol encoding of Booleans -/

namespace Turing.MultiTapeTM

/-- The encoding `b ↦ [b]` of `Bool`. -/
@[expose] public def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], fun _ _ h => List.head_eq_of_cons_eq h⟩

@[simp]
public lemma encBool_apply (b : Bool) : encBool b = [b] := rfl

end Turing.MultiTapeTM
