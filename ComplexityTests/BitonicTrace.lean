/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Sort.Bitonic.Trace
import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Data.List.Sort

/-!
# Saved sorting decisions

Check arbitrary traces, repeated keys, descending ties, and restoring transformed payloads
with their original positions. Compiled tests compare the traced algorithm with the existing
sort and independent list sorting. No uniqueness or stability premise is supplied.
-/

namespace ComplexityTests.BitonicTrace

open Cslib BitonicSort

example : sortTraceSize 0 = 0 := rfl
example : mergeTraceSize 3 = 12 := by decide +kernel
example : sortTraceSize 3 = 24 := by decide +kernel

example {α : Type*} (x : Fin 1 → α) : unrouteSort 0 Fin.elim0 x = x := rfl

example : routeLayer Fin.elim0 (Fin.elim0 : Fin 0 → ℕ) = Fin.elim0 := by
  funext i
  exact i.elim0

-- This trace is supplied directly, with no comparison-origin assumption.
example : List.ofFn (routeSort 2 ![true, false, true, true, false, true]
    (![0, 1, 2, 3] : Fin 4 → ℕ)) = [2, 3, 0, 1] := by decide +kernel

-- The descending child swaps ties; the other five comparisons retain them.
example : List.ofFn (sortTrace (fun _ : ℕ => 0) 2 true ![10, 11, 12, 13]) =
    [false, true, false, false, false, false] := by decide +kernel

-- Changed payloads follow the saved positions, even though all keys were identical.
example : List.ofFn (unrouteSort 2
    (sortTrace (fun _ : ℕ => 0) 2 true ![10, 11, 12, 13]) ![100, 110, 130, 120]) =
    [100, 110, 120, 130] := by decide +kernel

-- A client can replace sorted records with answers of an entirely different type.
example {κ α β : Type*} [LinearOrder κ] (depth : ℕ) (ascending : Bool)
    (records : Fin (arity depth) → κ × α) (answer : κ → β) :
    unrouteSort depth (sortTrace Prod.fst depth ascending records)
      (fun i => answer (sort Prod.fst depth ascending records i).1) =
        fun i => answer (records i).1 :=
  unrouteSort_comp_sort Prod.fst depth ascending (answer ∘ Prod.fst) records

private def checkArbitrary (depth : ℕ) : Bool :=
  let input := fun i : Fin (arity depth) => 10 + i.val
  let mergeChecks := (List.finRange (2 ^ mergeTraceSize depth)).all fun raw =>
    let flags := (BitString.equivFin (mergeTraceSize depth)).symm raw
    List.ofFn (unrouteMerge depth flags (routeMerge depth flags input)) == List.ofFn input &&
      List.ofFn (routeMerge depth flags (unrouteMerge depth flags input)) == List.ofFn input
  let sortChecks := (List.finRange (2 ^ sortTraceSize depth)).all fun raw =>
    let flags := (BitString.equivFin (sortTraceSize depth)).symm raw
    List.ofFn (unrouteSort depth flags (routeSort depth flags input)) == List.ofFn input &&
      List.ofFn (routeSort depth flags (unrouteSort depth flags input)) == List.ofFn input
  mergeChecks && sortChecks

private def checkTrace (depth : ℕ) : Bool :=
  (List.finRange (2 ^ (arity depth * 2))).all fun raw =>
    let bits := (BitString.equivFin (arity depth * 2)).symm raw
    let input := fun i : Fin (arity depth) =>
      let key := BitString.equivFin 2 (fun j => bits (finProdFinEquiv (i, j)))
      (key.val, i.val)
    [false, true].all fun ascending =>
      let flags := sortTrace Prod.fst depth ascending input
      let sorted := sort Prod.fst depth ascending input
      let payload := fun record : ℕ × ℕ => 7 * record.1 + record.2 + 10
      let expectedKeys := (List.ofFn (Prod.fst ∘ input)).mergeSort
      List.ofFn (routeSort depth flags input) == List.ofFn sorted &&
        List.ofFn (unrouteSort depth flags sorted) == List.ofFn input &&
        List.ofFn (unrouteSort depth flags (payload ∘ sorted)) ==
          List.ofFn (payload ∘ input) &&
        List.ofFn (Prod.fst ∘ sorted) ==
          (if ascending then expectedKeys else expectedKeys.reverse)

-- 86 arbitrary merge/sort traces and 552 key-array/direction combinations.
/-- info: true -/
#guard_msgs in
#eval [0, 1, 2].all fun depth => checkArbitrary depth && checkTrace depth

-- Another recursion level, with repeated keys and distinct payloads.
/-- info: [100, 200, 300, 400, 500, 600, 700, 800] -/
#guard_msgs in
#eval
  let input : Fin 8 → ℕ × ℕ := ![(3, 1), (0, 2), (3, 3), (1, 4),
    (2, 5), (0, 6), (1, 7), (2, 8)]
  let flags := sortTrace Prod.fst 3 false input
  let sorted := sort Prod.fst 3 false input
  List.ofFn (unrouteSort 3 flags (fun i => 100 * (sorted i).2))

end ComplexityTests.BitonicTrace
