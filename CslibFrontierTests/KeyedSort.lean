/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.KeyedSort
import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Data.List.Sort
import CslibFrontierTests.CircuitMaterialize

/-!
# Computed-key sorting clients

A parity key is computed from two bits; the third bit is unrelated payload. Exhaustive
checks compare recomputed keys and complete records against independent list sorting.
Boundary cases include empty keys, empty records, zero sorting depth and nonuniform gate costs.
The exhaustive check evaluates the materialized circuit, which `materialize_eq` proves equal to
the original.
-/

namespace CslibFrontierTests.KeyedSort

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CslibFrontierTests.CircuitMaterialize

private def parityKey : Circuit signature 3 1 :=
  ((Formula.input (0 : Fin 3)).xor (Formula.input 1)).toCircuit

example (x : BitString 12) :
    Monotone (fun j => toLex (parityKey.eval interpretation
      (directProductInput ((keyedSortCircuit parityKey 2 true).eval interpretation x) j))) :=
  monotone_keyedSortCircuit parityKey 2 x

example : (keyedSortCircuit parityKey 2 true).size = 212 := by
  have h := four_mul_size_keyedSortCircuit parityKey 2 true
  unfold parityKey
  norm_num [parityKey, Formula.xor] at h
  unfold Formula.xor
  lia

example : ∀ ascending : Bool, ∀ x : BitString 3,
    (keyedSortCircuit parityKey 0 ascending).eval interpretation x = x := by
  dsimp only [BitonicSort.arity]
  decide +kernel

example (depth : ℕ) (ascending : Bool) :
    (keyedSortCircuit (Circuit.wiring signature (Fin.elim0 : Fin 0 → Fin 0))
      depth ascending).size = 0 := by
  have h := four_mul_size_keyedSortCircuit
    (Circuit.wiring signature (Fin.elim0 : Fin 0 → Fin 0)) depth ascending
  simpa using h

-- Empty record bodies still incur the cost of their nonempty temporary keys and comparisons.
example : (keyedSortCircuit (Circuit.oneGate (.const true) (Fin.elim0 : Fin 0 → Fin 0))
    1 true).size = 16 := by
  decide +kernel

example : (keyedSortCircuit (Circuit.oneGate (.const true) (Fin.elim0 : Fin 0 → Fin 0))
    1 true).evalVector interpretation Fin.elim0 = #v[] := rfl

-- The constructor computes keys even at depth zero, when their outputs are then discarded.
/-- info: 5 -/
#guard_msgs in
#eval (keyedSortCircuit parityKey 0 false).size

-- Empty keys preserve all records but need not preserve their original order.
/-- info: #[false, false, false, true, true, true, true, false] -/
#guard_msgs in
#eval
  let c := keyedSortCircuit (Circuit.wiring signature (Fin.elim0 : Fin 0 → Fin 2)) 2 true
  (c.evalVector interpretation ![false, false, false, true, true, false, true, true]).toArray

-- Constant, NOT, AND and OR gates have distinct prices; key computation is charged four times.
/-- info: 916 -/
#guard_msgs in
#eval (keyedSortCircuit parityKey 2 false).program.cost fun
  | .const false => 11
  | .const true => 13
  | .not => 7
  | .and => 3
  | .or => 5

-- All 4096 inputs of four three-bit records, in both directions: 8192 checks.
-- The reference key uses Boolean XOR directly, independently of the compiled key circuit.
/-- info: true -/
#guard_msgs in
#eval
  [false, true].all fun ascending =>
    let c := materialize (keyedSortCircuit parityKey 2 ascending)
    (List.finRange 4096).all fun raw =>
      let input := (BitString.equivFin 12).symm raw
      let output := (c.evalVector interpretation input).get
      let records := fun x : BitString 12 => List.ofFn (directProductInput (k := 4) (n := 3) x)
      let values := fun x => (records x).map fun row => (BitString.equivFin 3 row).val
      let keys := fun x => (records x).map fun row => row 0 ^^ row 1
      let sortedKeys := (keys input).mergeSort
      keys output == (if ascending then sortedKeys else sortedKeys.reverse) &&
        (values output).mergeSort == (values input).mergeSort

end CslibFrontierTests.KeyedSort
