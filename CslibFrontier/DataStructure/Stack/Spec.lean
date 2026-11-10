/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Defs
public import CslibFrontier.DataStructure.Queue.Spec

/-!
# The bounded word stack

`Stack.spec w C` restricts the mathematical stack `Queue.stack ℕ` to at most `C` items, each
fitting a `w`-bit word. A push needs spare capacity and a fitting value; pop and size are always
admissible, and a pop from an empty stack returns `none`. `Stack.Memory` implements it over the
memory oracle, and `Stack.Native` runs that implementation on the word RAM.

## Main definitions

* `spec`: the bounded stack.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 10.1][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.Stack

open Cslib.WordRAM Cslib.DataStructure.Queue

/-- The stack restricted to `C` items that fit a `w`-bit word. -/
abbrev spec (w C : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (stack ℕ).stepFn fun vs o => match o with
    | .push v => vs.length < C ∧ Fits w v
    | .pop | .size => True

end Cslib.DataStructure.Stack
