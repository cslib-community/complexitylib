/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.SortingTrace
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Saved-control sorting circuit clients

Check exact costs, arbitrary saved decisions, repeated and empty keys, zero-width records,
and restoration after changing payload width. Compiled tests exercise the actual circuits;
the public correctness and cost theorems are also instantiated below.
-/

namespace CslibFrontierTests.SortingTrace

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open bitonicSortTraceCircuit

example {k r v : ℕ} (key : Fin k → Fin r) (d : ℕ) (ascending : Bool)
    (f : BitString r → BitString v) (x : BitString (BitonicSort.arity d * r)) :
    let output := (bitonicSortTraceCircuit key d ascending).eval interpretation x
    directProductInput ((bitonicUnsortCircuit v d).eval interpretation
      (pack (controls output) (f ∘ records output))) = f ∘ directProductInput x :=
  eval_bitonicUnsortCircuit_sort key d ascending f x

example {k r : ℕ} (key : Fin k → Fin r) (d : ℕ) (ascending : Bool)
    (hr : r ≠ 0) (cost : signature.Op → ℕ) :
    (bitonicSortTraceCircuit key d ascending).program.cost cost =
      (bitonicSortCircuit key d ascending).program.cost cost :=
  cost_program_bitonicSortTraceCircuit_eq key d ascending hr cost

example : (bitonicSortTraceCircuit (![0] : Fin 1 → Fin 2) 2 true).size = 120 := by
  rw [size_bitonicSortTraceCircuit]
  rfl

example : (bitonicUnsortCircuit 3 2).size = 108 := by
  rw [size_bitonicUnsortCircuit]
  rfl

-- Empty-width traced sorting still produces controls, unlike the ordinary sorter.
example : (bitonicSortTraceCircuit (Fin.elim0 : Fin 0 → Fin 0) 3 false).size = 48 := by
  rw [size_bitonicSortTraceCircuit]
  rfl

example (d : ℕ) : (bitonicUnsortCircuit 0 d).size = 0 := by
  simp [size_bitonicUnsortCircuit]

-- Invalid control pairs need not be permutations, and are outside the reversal contract.
/-- info: (#[false, false], #[true, true]) -/
#guard_msgs in
#eval
  (((compareSwapCircuit.switch 1).evalVector interpretation
      ![false, false, true, false]).toArray,
    ((compareSwapCircuit.switch 1).evalVector interpretation
      ![true, true, true, false]).toArray)

-- Independent weighted counts include constant gates, shared negations, ANDs and ORs.
/-- info: (360, 252) -/
#guard_msgs in
#eval
  let cost : signature.Op → ℕ := fun
    | .const _ => 7
    | .not => 5
    | .and => 2
    | .or => 3
  ((bitonicSortTraceCircuit (![0] : Fin 1 → Fin 2) 2 true).program.cost cost,
    (bitonicUnsortCircuit 3 2).program.cost cost)

-- All 256 four-record inputs, four selectors (including repeated coordinates), and both
-- directions: 2048 exact trace checks and restorations after changing record width from 2 to 3.
/-- info: true -/
#guard_msgs in
#eval
  (List.finRange 2).all fun a => (List.finRange 2).all fun b =>
    [false, true].all fun ascending =>
      let key : Fin 2 → Fin 2 := ![a, b]
      let c := bitonicSortTraceCircuit key 2 ascending
      let undo := bitonicUnsortCircuit 3 2
      let transform : BitString 2 → BitString 3 := fun row => ![row 0, row 1, !row 0]
      let keyValue : BitString 2 → ℕ := fun row =>
        (List.ofFn (row ∘ key)).foldl (fun n bit => 2 * n + if bit then 1 else 0) 0
      (List.finRange 256).all fun raw =>
        let input := (BitString.equivFin 8).symm raw
        let inputRows : Fin 4 → BitString 2 := directProductInput input
        let output := (c.evalVector interpretation input).get
        let flags := BitonicSort.sortTrace keyValue 2 ascending inputRows
        let restored := (undo.evalVector interpretation
          (pack (controls output) (transform ∘ records output))).get
        List.ofFn (fun j => List.ofFn (controls output j)) ==
            List.ofFn (fun j => List.ofFn (pairs flags j)) &&
          List.ofFn restored == List.ofFn (flatten (transform ∘ inputRows))

-- Every arbitrary trace through depth 2, and four trace patterns at depth 3. No sorting
-- provenance is assumed, and the payload consists of distinct original-position tags.
/-- info: true -/
#guard_msgs in
#eval
  [0, 1, 2, 3].all fun d =>
    let t := BitonicSort.sortTraceSize d
    let traces := if d < 3 then List.range (2 ^ t) else [0, 1, 0xaaaaaa, 0xffffff]
    let undo := bitonicUnsortCircuit 3 d
    let payload : Fin (BitonicSort.arity d) → BitString 3 :=
      fun j => (BitString.equivFin 3).symm ⟨j.val % 8, Nat.mod_lt _ (by decide)⟩
    traces.all fun raw =>
      let flags : BitString t := fun i => raw.testBit i.val
      let routed := BitonicSort.routeSort d flags payload
      List.ofFn ((undo.evalVector interpretation (pack (pairs flags) routed)).get) ==
        List.ofFn (flatten payload)

-- Empty keys keep the exact descending-tie convention, with nonempty payloads and controls.
/-- info: true -/
#guard_msgs in
#eval
  [false, true].all fun ascending =>
    let input : BitString 8 := ![false, false, false, true, true, false, true, true]
    let output := ((bitonicSortTraceCircuit (Fin.elim0 : Fin 0 → Fin 2) 2 ascending).evalVector
      interpretation input).get
    let flags := BitonicSort.sortTrace (fun _ : BitString 2 => (0 : ℕ)) 2 ascending
      (directProductInput input)
    List.ofFn (fun j => List.ofFn (controls output j)) ==
        List.ofFn (fun j => List.ofFn (pairs flags j)) &&
      List.ofFn ((bitonicUnsortCircuit 2 2).evalVector interpretation output).get == List.ofFn input

-- With no payload bits, control pairs remain present and complementary.
/-- info: true -/
#guard_msgs in
#eval
  [false, true].all fun ascending =>
    let output := ((bitonicSortTraceCircuit (Fin.elim0 : Fin 0 → Fin 0) 3 ascending).evalVector
      interpretation Fin.elim0).get
    (List.finRange 24).all (fun i => controls output i 1 == !(controls output i 0)) &&
      ((bitonicUnsortCircuit 0 3).evalVector interpretation output).toArray.isEmpty

end CslibFrontierTests.SortingTrace
