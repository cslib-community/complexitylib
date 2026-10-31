/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Foundations.Data.OrderedSet.ExtractMin

/-!
# Representation-independent ordered-set clients

This driver imports only the neutral interface, with no search-tree implementation or cost
module. Finite keys demonstrate that the interface is not restricted to natural-number storage.
A validity specialization shows the intended bounded-key contract without assuming a vEB
implementation or any cost theorem.
-/

@[expose] public section

namespace Cslib.OrderedSet

open Cslib.Stateful

variable {α : Type} [LinearOrder α]

/-- Insert a list in order, leaving representation and resource behavior to a realization. -/
def insertAll : List α → (spec α).Client Unit
  | [] => .pure ()
  | x :: xs => .liftBind (.insert x) fun _ => insertAll xs

/-- Batch insertion adds each key to the state, retaining every insertion in its original order. -/
theorem insertAll_run (s : Finset α) (xs : List α) :
    (spec α).runClient s (insertAll xs) = ((), s ∪ xs.toFinset, xs.map Op.insert) := by
  induction xs generalizing s with
  | nil =>
    change ((), s, []) = ((), s ∪ ∅, [])
    rw [Finset.union_empty]
  | cons x xs ih =>
    simp only [insertAll, Spec.runClient_liftBind, spec, ih, List.toFinset_cons, List.map_cons]
    simp [Finset.insert_union, Finset.union_insert]

/-- Read the two smallest distinct keys. The successor argument comes from the minimum answer. -/
def firstTwo : (spec α).Client (Option α × Option α) :=
  .liftBind .minimum fun
    | none => .pure (none, none)
    | some x => .liftBind (.successor x) fun next => .pure (some x, next)

/-- The chosen operation history visibly depends on whether the minimum query succeeded. -/
theorem firstTwo_run (s : Finset α) :
    (spec α).runClient s firstTwo =
      match least s with
      | none => ((none, none), s, [.minimum])
      | some x => ((some x, least (s.filter (x < ·))), s, [.minimum, .successor x]) := by
  simp only [firstTwo, Spec.runClient_liftBind, spec]
  cases least s <;> rfl

end Cslib.OrderedSet

namespace ComplexityTests.OrderedSet

open Cslib.OrderedSet Cslib.Stateful

-- The absence contract is complete, including exhaustion above the largest key.
example : LeastResult (∅ : Finset (Fin 3)) none := rfl
example : ¬ LeastResult ({1} : Finset (Fin 3)) none := by
  simp [LeastResult]
example : least ({0, 2} : Finset (Fin 3)) = some 0 := by decide
example (s : Finset (Fin 3)) : (least s : WithTop (Fin 3)) = s.min := least_eq_min s
example : (spec (Fin 3)).step {0, 2} (.successor 1) = ({0, 2}, some 2) := by decide
example : (spec (Fin 3)).step {0, 2} (.successor 2) = ({0, 2}, none) := by decide

-- Deletion is total: present, absent, and empty-set cases have the same typed interface.
example : (spec (Fin 3)).step {0, 2} (.erase 0) = ({2}, ()) := by decide
example : (spec (Fin 3)).step {0, 2} (.erase 1) = ({0, 2}, ()) := by decide
example : (spec (Fin 3)).step ∅ (.erase 0) = (∅, ()) := by decide

-- The erased key comes from the minimum answer; an empty query performs no deletion.
example : (spec (Fin 3)).runClient {0, 2} extractMin =
    (some 0, {2}, [.minimum, .erase 0]) := by decide
example : (spec (Fin 3)).runClient ∅ extractMin = (none, ∅, [.minimum]) := by decide

private def extractThree :
    (spec (Fin 3)).Client (Option (Fin 3) × Option (Fin 3) × Option (Fin 3)) := do
  let first ← extractMin
  let second ← extractMin
  let third ← extractMin
  pure (first, second, third)

-- Sequential composition sees the updated set, including exhaustion after the last key.
example : (spec (Fin 3)).runClient {0, 2} extractThree =
    ((some 0, some 2, none), ∅, [.minimum, .erase 0, .minimum, .erase 2, .minimum]) := by decide

-- The same adaptive client can be interpreted without choosing a data structure.
example : (spec (Fin 3)).runClient ∅ firstTwo = ((none, none), ∅, [.minimum]) := by decide
example : (spec (Fin 3)).runClient {0, 2} firstTwo =
    ((some 0, some 2), {0, 2}, [.minimum, .successor 0]) := by decide
example : ((spec (Fin 3)).runClient ∅ (insertAll [2, 0, 2])).2.1 = {0, 2} := by decide

-- The general theorem keeps pre-existing keys and repeated operations in their original order.
example (s : Finset (Fin 3)) : (spec (Fin 3)).runClient s (insertAll []) = ((), s, []) := by
  simpa using insertAll_run s []
example : (spec (Fin 3)).runClient {1} (insertAll [2, 0, 2]) =
    ((), {0, 1, 2}, [.insert 2, .insert 0, .insert 2]) := by
  rw [insertAll_run]
  decide
example (s : Finset (Fin 3)) (xs ys : List (Fin 3)) :
    ((spec (Fin 3)).runClient s (insertAll (xs ++ ys))).2.2 =
      xs.map Op.insert ++ ys.map Op.insert := by
  simp only [insertAll_run, List.map_append]

/-- A later bounded-key realization can restrict insertion while leaving all queries admissible. -/
abbrev bounded (bound : Nat) : Spec :=
  { spec Nat with valid := fun _ o => match o with
      | .insert x => x < bound
      | _ => True }

example : ¬ (bounded 4).valid ∅ (.insert 4) := by decide
example : (bounded 4).valid ∅ (.contains 99) := trivial
example : (bounded 4).valid ∅ (.successor 99) := trivial
example : (bounded 4).valid ∅ (.erase 99) := trivial
example : (spec Nat).valid ∅ (.insert 99) := trivial

end ComplexityTests.OrderedSet
