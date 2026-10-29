/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Sorting
import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Data.List.Sort

/-!
# Batcher sorting clients

Check the functional algorithm, complete-record circuit sorting, arbitrary and repeated key
coordinates, duplicates, empty keys, empty records, and depth zero. Compiled checks compare
sorted keys and record multisets against independent list sorting.
-/

namespace ComplexityTests.BitonicSort

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

example : List.ofFn (BitonicSort.sort id 2 true (![3, 1, 2, 0] : Fin 4 → ℕ)) =
    [0, 1, 2, 3] := by
  decide +kernel

example : List.ofFn (BitonicSort.sort id 2 false (![3, 1, 2, 0] : Fin 4 → ℕ)) =
    [3, 2, 1, 0] := by
  decide +kernel

-- The full algorithm is deliberately not claimed stable: descending intermediate ties swap.
example : List.ofFn (BitonicSort.sort (fun _ : ℕ => 0) 2 true ![10, 11, 12, 13]) =
    [10, 11, 13, 12] := by
  decide +kernel

example {α κ : Type*} [LinearOrder κ] (key : α → κ) (x : Fin 1 → α) (ascending : Bool) :
    BitonicSort.sort key 0 ascending x = x := rfl

example {k r : ℕ} (key : Fin k → Fin r) (ascending : Bool) (x : BitString (1 * r)) :
    (bitonicSortCircuit key 0 ascending).eval interpretation x = x := by
  change BitString (BitonicSort.arity 0 * r) at x
  simpa only [BitonicSort.sort, bitonicSortTraceCircuit.flatten_directProductInput] using
    congrArg bitonicSortTraceCircuit.flatten (eval_bitonicSortCircuit key 0 ascending x)

example : (bitonicSortCircuit (fun _ : Fin 1 => (0 : Fin 2)) 2 true).size = 120 := by
  have h := four_mul_size_bitonicSortCircuit (fun _ : Fin 1 => (0 : Fin 2)) 2 true
  norm_num at h
  lia

example : (bitonicSortCircuit (![1, 0, 1] : Fin 3 → Fin 2) 2 false).size = 192 := by
  have h := four_mul_size_bitonicSortCircuit (![1, 0, 1] : Fin 3 → Fin 2) 2 false
  norm_num at h
  lia

example (depth : ℕ) (ascending : Bool) :
    (bitonicSortCircuit (Fin.elim0 : Fin 0 → Fin 0) depth ascending).size = 0 := by
  have h := four_mul_size_bitonicSortCircuit (Fin.elim0 : Fin 0 → Fin 0) depth ascending
  simpa using h

example {k r : ℕ} (key : Fin k → Fin r) (depth : ℕ) (x : BitString (BitonicSort.arity depth * r)) :
    Monotone (fun j => toLex (directProductInput
      ((bitonicSortCircuit key depth true).eval interpretation x) j ∘ key)) :=
  monotone_bitonicSortCircuit key depth x

/-- info: #[] -/
#guard_msgs in
#eval ((bitonicSortCircuit (Fin.elim0 : Fin 0 → Fin 0) 3 true).evalVector
  interpretation Fin.elim0).toArray

-- Empty records bypass the traced recursion, even at depths with enormous comparison counts.
/-- info: (0, 0, 0) -/
#guard_msgs in
#eval
  ((bitonicLayerCircuit (Fin.elim0 : Fin 0 → Fin 0) 1000000 false).size,
    (bitonicMergeCircuit (Fin.elim0 : Fin 0 → Fin 0) 30 false).size,
    (bitonicSortCircuit (Fin.elim0 : Fin 0 → Fin 0) 30 false).size)

-- Four whole records are retained even when the key is empty.
/-- info: #[false, false, false, true, true, true, true, false] -/
#guard_msgs in
#eval ((bitonicSortCircuit (Fin.elim0 : Fin 0 → Fin 2) 2 true).evalVector interpretation
  ![false, false, false, true, true, false, true, true]).toArray

-- Eight distinct three-bit records exercise another recursion level. Lexicographic order
-- treats coordinate zero as most significant, whereas equivFin uses little-endian bits.
/-- info: [0, 4, 2, 6, 1, 5, 3, 7] -/
#guard_msgs in
#eval
  let records : Fin 8 → Fin 8 := ![7, 2, 6, 1, 5, 0, 4, 3]
  let input : BitString (8 * 3) := fun i =>
    let jb := finProdFinEquiv.symm i
    (BitString.equivFin 3).symm (records jb.1) jb.2
  let output := ((bitonicSortCircuit (id : Fin 3 → Fin 3) 3 true).evalVector
    interpretation input).get
  List.ofFn fun j : Fin 8 => (BitString.equivFin 3 (directProductInput output j)).val

-- All 256 four-record inputs, four two-coordinate selectors (including repetitions), and both
-- directions: 2048 checks of sorted keys and preservation of the complete record multiset.
/-- info: true -/
#guard_msgs in
#eval
  (List.finRange 2).all fun a => (List.finRange 2).all fun b =>
    [false, true].all fun ascending =>
      let key : Fin 2 → Fin 2 := ![a, b]
      let c := bitonicSortCircuit key 2 ascending
      (List.finRange 256).all fun raw =>
        let input := (BitString.equivFin 8).symm raw
        let output := (c.evalVector interpretation input).get
        let records := fun x : BitString 8 => List.ofFn (directProductInput (k := 4) (n := 2) x)
        let values := fun x => (records x).map fun row => (BitString.equivFin 2 row).val
        let keys := fun x => (records x).map fun row =>
          (List.ofFn (row ∘ key)).foldl (fun n bit => 2 * n + if bit then 1 else 0) 0
        let sortedKeys := (keys input).mergeSort
        keys output == (if ascending then sortedKeys else sortedKeys.reverse) &&
          (values output).mergeSort == (values input).mergeSort

end ComplexityTests.BitonicSort
