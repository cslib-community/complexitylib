/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Tactic.Degree

/-! Tests of `degree`: option matches, `Option.elim` and list heads at degree one. -/

namespace ComplexityTests.DegreeTactic

open Turing.MultiTapeTM

/-- A definition by `match` on an option. -/
def bumpOr (o : Option ℕ) (l : List ℕ) : List ℕ :=
  match o with
  | none => l
  | some n => n :: l

-- The `match` is rewritten to `Option.elim`; the handler sees the input and the value.
example : ComputableInDegree (fun p : Option ℕ × List ℕ => bumpOr p.1 p.2)
    (encPair (encOption encUnary) (encList encUnary)) (encList encUnary) 1 1 := by
  unfold bumpOr
  degree

-- The head of a list, as an option, and a default.
example : ComputableInDegree (fun l : List ℕ => (l.head?).getD 0)
    (encList encUnary) encUnary 1 1 := by
  degree

end ComplexityTests.DegreeTactic
