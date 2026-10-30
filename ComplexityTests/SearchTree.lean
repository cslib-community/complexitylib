/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.SearchTree.Stateful
public import ComplexityTests.OrderedSet

/-!
# Worked search-tree examples

Insert the same seven keys in two orders. The median-first order happens to produce height three;
sorted insertion produces a right spine of height seven. This implementation does not rebalance.
The exact node-visit counts expose that difference without claiming machine instruction costs.

The final examples execute `firstTwo`: its successor argument comes from the minimum it observed,
so the query history differs between an empty and a nonempty set. All computation is checked by
the kernel, with no `native_decide`.
-/

@[expose] public section

namespace ComplexityTests.SearchTree

open Cslib.Algorithms.Lean.SearchTree Cslib.OrderedSet Cslib.Stateful

def build (xs : List Nat) : BinaryTree Nat := (run .nil (insertAll xs)).2.1

private def medianFirst : BinaryTree Nat := build [4, 2, 6, 1, 3, 5, 7]
private def sortedFirst : BinaryTree Nat := build [1, 2, 3, 4, 5, 6, 7]

theorem ordered_build (xs : List Nat) : Ordered (build xs) :=
  (run_correct (insertAll xs) rep_empty).2.1.1

-- The neutral client theorem transfers arbitrary-list contents to the concrete realization.
theorem elements_build (xs : List Nat) : elements (build xs) = xs.toFinset := by
  have h := (run_correct (insertAll xs) rep_empty).2.1.2
  simpa only [build, insertAll_run, Finset.empty_union] using h

-- These shapes represent exactly the same set, with satisfiable strict ordering invariants.
example :
    Ordered medianFirst ∧
      Ordered sortedFirst ∧
      elements medianFirst = elements sortedFirst ∧
      (elements medianFirst).card = 7 ∧
      medianFirst.height = 3 ∧
      sortedFirst.height = 7 :=
  ⟨ordered_build _, ordered_build _, by decide, by decide, rfl, rfl⟩

-- Searching for the maximum or for a missing larger key traverses three versus seven nodes, and
-- duplicate insertion preserves shape as well as contents.
example :
    contains 7 medianFirst = true ∧
      contains 8 medianFirst = false ∧
      searchVisits 7 medianFirst = 3 ∧
      searchVisits 7 sortedFirst = 7 ∧
      searchVisits 8 medianFirst = 3 ∧
      searchVisits 8 sortedFirst = 7 ∧
      (insert 8 sortedFirst).height = 8 ∧
      insert 4 medianFirst = medianFirst :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, insert_eq_self (ordered_build _) (by decide)⟩

-- Successor is strict, can start from an absent key, and reports exhaustion.
example :
    minimum medianFirst = some 1 ∧
      successor 0 medianFirst = some 1 ∧
      successor 4 medianFirst = some 5 ∧
      successor 7 medianFirst = none ∧
      successor 100 medianFirst = none ∧
      successor 3 (build [2, 4, 6]) = some 4 ∧
      successor 4 (build [2, 4, 6]) = some 6 ∧
      successorVisits 7 sortedFirst = 7 ∧
      minimumVisits sortedFirst = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Empty queries and singleton boundaries are total.
example :
    minimum (.nil : BinaryTree Nat) = none ∧
      successor 0 (.nil : BinaryTree Nat) = none ∧
      searchVisits 0 (.nil : BinaryTree Nat) = 0 ∧
      run (.nil : BinaryTree Nat) (.liftBind (.insert 5) .pure) =
        ((), BinaryTree.node 5 .nil .nil, [0]) ∧
      successor 5 (build [5]) = none ∧
      successor 4 (build [5]) = some 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- The shared deletion operation uses successor splicing at a root with two children and retains
-- the exact charge, including for missing keys and an empty initial tree.
example :
    run medianFirst (.liftBind (.erase 4) .pure) = ((), erase 4 medianFirst, [3]) ∧
      run sortedFirst (.liftBind (.erase 4) .pure) = ((), erase 4 sortedFirst, [5]) ∧
      run medianFirst (.liftBind (.erase 8) .pure) = ((), medianFirst, [3]) ∧
      run (.nil : BinaryTree Nat) (.liftBind (.erase 0) .pure) = ((), .nil, [0]) :=
  ⟨rfl, rfl, rfl, rfl⟩

private def eraseTwiceAndCheck (x : Nat) : (spec Nat).Client Bool := do
  PFunctor.FreeM.lift (P := (spec Nat).signature) (.erase x)
  PFunctor.FreeM.lift (P := (spec Nat).signature) (.erase x)
  PFunctor.FreeM.lift (P := (spec Nat).signature) (.contains x)

-- A repeated deletion is still charged for its unsuccessful search, and later queries see the
-- updated state through the same interpreter and representation-independent correctness theorem.
example :
    (run medianFirst (eraseTwiceAndCheck 4)).1 = false ∧
      (run medianFirst (eraseTwiceAndCheck 4)).2.1 = erase 4 medianFirst ∧
      (run medianFirst (eraseTwiceAndCheck 4)).2.2 = [3, 3, 3] ∧
      (run medianFirst (eraseTwiceAndCheck 4)).1 =
        ((spec Nat).runClient (elements medianFirst) (eraseTwiceAndCheck 4)).1 :=
  ⟨rfl, rfl, rfl, (run_correct _ ⟨ordered_build _, rfl⟩).1⟩

-- Minimum extraction charges the query and the answer-dependent deletion separately. Their
-- costs differ on the two shapes even though both implement the same finite-set client.
example :
    run medianFirst extractMin = (some 1, erase 1 medianFirst, [3, 3]) ∧
      run sortedFirst extractMin = (some 1, erase 1 sortedFirst, [1, 2]) ∧
      run (build [5]) extractMin = (some 5, .nil, [1, 1]) ∧
      run (.nil : BinaryTree Nat) extractMin = (none, .nil, [0]) :=
  ⟨rfl, rfl, rfl, rfl⟩

-- The generic resource certificate applies to the new adaptive deleting client unchanged.
example :
    total id (run medianFirst extractMin).2.2 ≤
      (spec Nat).totalCost (fun s _ => s.card) (elements medianFirst)
        ((spec Nat).runClient (elements medianFirst) extractMin).2.2 :=
  (run_correct extractMin ⟨ordered_build _, rfl⟩).2.2

-- The exact native trace counts minimum and the answer-dependent successor separately, and agrees
-- with finite-set semantics through the shared realization theorem.
example :
    (run medianFirst firstTwo).1 = (some 1, some 2) ∧
      (run medianFirst firstTwo).2.2 = [3, 3] ∧
      (run sortedFirst firstTwo).1 = (some 1, some 2) ∧
      (run sortedFirst firstTwo).2.2 = [1, 2] ∧
      (run (.nil : BinaryTree Nat) firstTwo).1 = (none, none) ∧
      (run (.nil : BinaryTree Nat) firstTwo).2.2 = [0] ∧
      (run (build [5]) firstTwo).1 = (some 5, none) ∧
      (run medianFirst firstTwo).1 = ((spec Nat).runClient (elements medianFirst) firstTwo).1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, (run_correct firstTwo ⟨ordered_build _, rfl⟩).1⟩

example :
    ∃ t ns, Executes Exec ((insertAll [4, 2, 6]).bind fun _ => firstTwo) .nil
        ((spec Nat).runClient ∅ ((insertAll [4, 2, 6]).bind fun _ => firstTwo)).1 t ns ∧
      Rep ((spec Nat).runClient ∅ ((insertAll [4, 2, 6]).bind fun _ => firstTwo)).2.1 t ∧
      total id ns ≤ (spec Nat).totalCost (fun s _ => s.card) ∅
        ((spec Nat).runClient ∅ ((insertAll [4, 2, 6]).bind fun _ => firstTwo)).2.2 :=
  realized_client _ rep_empty

-- A malformed tree demonstrates why query correctness requires Ordered, and a finite-set
-- cardinality bound does not imply a logarithmic-height bound.
private def malformed : BinaryTree Nat := .node 0 (.node 1 .nil .nil) .nil

example :
    1 ∈ elements malformed ∧
      contains 1 malformed = false ∧
      ¬ Ordered malformed ∧
      ¬ sortedFirst.height ≤ 3 :=
  ⟨by decide, rfl, by simp [malformed, Ordered, elements], by decide⟩

end ComplexityTests.SearchTree
