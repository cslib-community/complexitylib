/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.OrderedSet
public import Complexity.Foundations.Semantics.Stateful.Basic

/-!
# A representation-independent stateful ordered set

The abstract state is a finite set over any linear order. Membership, insertion, deletion, minimum
and strict successor have operation-dependent result types. All operations are admissible,
including empty queries, duplicate insertion and deletion of absent keys. A bounded-key
implementation can specialize `spec.valid` for insertion while preserving arbitrary membership
and successor queries. This module does not
choose a representation or charge a computational cost.

## Main definitions

* `Cslib.OrderedSet.Op`, `Cslib.OrderedSet.spec`: shared typed ordered-set interface and semantics.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 12][CLRS2009]

The adaptive client syntax uses Quang Dao's upstream free monad via `Cslib.Stateful.Spec`.
-/

@[expose] public section

namespace Cslib.OrderedSet

open Cslib.Stateful

variable {α : Type} [LinearOrder α]

/-- Typed finite-set operations, independent of any representation. -/
inductive Op (α : Type) where
  | contains (key : α)
  | insert (key : α)
  | erase (key : α)
  | minimum
  | successor (key : α)
  deriving DecidableEq

/-- Mathematical ordered-set semantics. All operations are admissible, including empty queries. -/
abbrev spec (α : Type) [LinearOrder α] : Spec where
  State := Finset α
  Op := Op α
  Result
    | .contains _ => Bool
    | .insert _ => Unit
    | .erase _ => Unit
    | .minimum => Option α
    | .successor _ => Option α
  step s
    | .contains x => (s, decide (x ∈ s))
    | .insert x => (Insert.insert x s, ())
    | .erase x => (s.erase x, ())
    | .minimum => (s, least s)
    | .successor x => (s, least (s.filter (x < ·)))

end Cslib.OrderedSet
