/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPPpath
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime

/-! # BPPpath: explicit path counts for concrete languages -/

@[expose] public section

namespace Cslib.Complexity.Tests.BPPpath

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- The empty language: one rejecting path and no accepting path on every input. -/
example : (∅ : Set α) ∈ BPPpath enc :=
  ⟨0, SharpP.zero_mem, 1, SharpP.one_mem, fun _ => by simp⟩

/-- A language decided by a polynomial-time predicate `p`: a single path, accepting exactly when
`p` holds. The ratio conditions hold with one path against none. -/
example (p : α → Bool) (hp : ComputableInPolyTime p enc encBool) :
    {a | p a = true} ∈ BPPpath enc := by
  refine ⟨fun a => if p a then 1 else 0, SharpP.ite_mem hp SharpP.one_mem SharpP.zero_mem,
    fun a => if p a then 0 else 1, SharpP.ite_mem hp SharpP.zero_mem SharpP.one_mem,
    fun a => ?_⟩
  cases h : p a <;> simp [h]

end Cslib.Complexity.Tests.BPPpath
