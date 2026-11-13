/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Reductions that edit the word of an instance–word pair

Quantifier and certificate arguments work with problems on pairs `(a, w)` of an instance and a
bit string, encoded by `encPair enc encBits`. Cutting the word to a prefix or suffix whose length is
computed from `a`, or appending a second word to it, is polynomial-time, so each operation reduces
the edited problem to the original one.

## Main results

* `Cslib.Complexity.polyTimeReducible_take`, `Cslib.Complexity.polyTimeReducible_drop`: keeping or
  dropping the first `N a` bits of the word, for `N` computable in polynomial time in unary.
* `Cslib.Complexity.polyTimeReducible_append`: appending a second word to the word.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-- Keeping the first `N a` bits of the word of `(a, w)` is a polynomial-time reduction, for `N`
computable in polynomial time in unary. -/
theorem polyTimeReducible_take {N : α → ℕ} (hN : ComputableInPolyTime N enc encUnary)
    (C : Set (α × List Bool)) :
    PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
      {x | (x.1, x.2.take (N x.1)) ∈ C} C :=
  ⟨fun x => (x.1, x.2.take (N x.1)),
    (fst _ _).prod (bitsTakeWithInput (snd _ _) (hN.comp (fst _ _))), fun _ => Iff.rfl⟩

/-- Dropping the first `N a` bits of the word of `(a, w)` is a polynomial-time reduction, for `N`
computable in polynomial time in unary. -/
theorem polyTimeReducible_drop {N : α → ℕ} (hN : ComputableInPolyTime N enc encUnary)
    (C : Set (α × List Bool)) :
    PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
      {x | (x.1, x.2.drop (N x.1)) ∈ C} C :=
  ⟨fun x => (x.1, x.2.drop (N x.1)),
    (fst _ _).prod (bitsDropWithInput (snd _ _) (hN.comp (fst _ _))), fun _ => Iff.rfl⟩

/-- Appending a word `u` to the word of `(a, s)` is a polynomial-time reduction. -/
theorem polyTimeReducible_append (C : Set (α × List Bool)) :
    PolyTimeReducible (encPair (encPair enc encBits) encBits) (encPair enc encBits)
      {((a, s), u) : (α × List Bool) × List Bool | (a, s ++ u) ∈ C} C :=
  ⟨fun x => (x.1.1, x.1.2 ++ x.2), (fst _ _).fst'.prod (bitsAppend (fst _ _).snd' (snd _ _)),
    fun _ => Iff.rfl⟩

end Cslib.Complexity
