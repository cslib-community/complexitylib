/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the divide-and-conquer combinator)

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.DivConq

/-!
# Divide and conquer

A smoke test of `Turing.MultiTapeTM.ComputableInO.divConq`: a recursion in which every problem is a
base problem, solved by the identity on unary numbers, so that all hypotheses are discharged and the
conclusion is reached. The windowed simulation
(`Turing.MultiTapeTM.Universal.computableInO_universal_nlogn`) is a nontrivial instance.
-/

@[expose] public section

namespace ComplexityTests.DivConq

open Turing.MultiTapeTM

/-- A recursion in which every problem is a base problem, solved by the identity. -/
def trivialDC : DivConq ℕ ℕ ℕ where
  isBase _ := true
  base := id
  left := id
  mid p := p
  join q := q.2

/-- Every problem of `trivialDC` is solved by itself. -/
example : ComputableInO (fun n : ℕ => n) encUnary encUnary
    (fun n => (encUnary n).length + (encUnary n).length + (encUnary n).length +
      ((encUnary n).length + (encUnary n).length + (encUnary n).length + (encUnary n).length +
        (encUnary n).length + (encUnary n).length + 1))
    (fun n => (encUnary n).length + (encUnary n).length + (encUnary n).length +
      ((encUnary n).length + (encUnary n).length + (encUnary n).length + (encUnary n).length +
        (encUnary n).length + (encUnary n).length + 1)) :=
  ComputableInO.divConq trivialDC (init := id) (F := fun n => n) (cn := fun _ _ _ => 0)
    (ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)).computableInO
    (ComputableTidilyInO.const (encMid := encBool) true).computableInO
    (ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)).computableInO
    (ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)).computableInO
    (ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)).computableInO
    (ComputableTidilyInO.snd encUnary encUnary).computableInO
    (fun _ _ => le_rfl) (fun _ _ _ h => absurd h (by simp [trivialDC]))
    (fun _ => .base rfl)

end ComplexityTests.DivConq
