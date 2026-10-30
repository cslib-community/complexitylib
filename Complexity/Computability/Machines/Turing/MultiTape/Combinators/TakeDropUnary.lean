/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Taking and dropping list elements in linear time

STUB: interface for the linear-time unary take/drop primitives. To be replaced by the native
machine and its proofs.
-/

public section

namespace Turing.MultiTapeTM.ComputableTidilyInDegree

variable {α : Type}

/-- Taking the first `n` elements, with `n` in unary, in linear time. -/
theorem takeUnary (enc : α ↪ List Bool) :
    ComputableTidilyInDegree (fun p : List α × ℕ => p.1.take p.2)
      (encPair (encList enc) encUnary) (encList enc) 1 1 :=
  sorry

/-- Dropping the first `n` elements, with `n` in unary, in linear time. -/
theorem dropUnaryLin (enc : α ↪ List Bool) :
    ComputableTidilyInDegree (fun p : List α × ℕ => p.1.drop p.2)
      (encPair (encList enc) encUnary) (encList enc) 1 1 :=
  sorry

end Turing.MultiTapeTM.ComputableTidilyInDegree
