/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.DuplicateFlags
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontierTests.CircuitMaterialize

/-!
# Duplicate detection clients

Compare the circuit with a direct search through the original input, including unsorted keys,
repeated complete records, arbitrary key selectors, empty keys and singleton arrays. The
exhaustive check evaluates the materialized circuit, which `materialize_eq` proves equal to the
original.
-/

namespace CslibFrontierTests.DuplicateFlags

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CslibFrontierTests.CircuitMaterialize

example {r k : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (x : BitString (BitonicSort.arity d * r)) (i : Fin (BitonicSort.arity d)) :
    (duplicateFlagsCircuit key d).eval interpretation x i = true ↔
      ∃ j, j ≠ i ∧ BitString.block x j ∘ key = BitString.block x i ∘ key :=
  eval_duplicateFlagsCircuit_iff key d x i

-- Every four-record input with three bits per record. The key reads positions 2 then 0;
-- the unselected payload bit must not affect which original positions receive true.
/-- info: true -/
#guard_msgs in
#eval
  let c := materialize (duplicateFlagsCircuit (![2, 0] : Fin 2 → Fin 3) 2)
  (List.finRange 4096).all fun raw =>
    let x := (BitString.equivFin 12).symm raw
    let rows : Fin 4 → BitString 3 := BitString.block x
    let out := (c.evalVector interpretation x).get
    (List.finRange 4).all fun i =>
      out i == (List.finRange 4).any fun j =>
        j != i && rows j 2 == rows i 2 && rows j 0 == rows i 0

-- Repeated selectors are allowed; the same one-bit keys still determine the duplicates.
/-- info: true -/
#guard_msgs in
#eval
  let c := duplicateFlagsCircuit (fun _ : Fin 2 => (0 : Fin 1)) 2
  (List.finRange 16).all fun raw =>
    let x := (BitString.equivFin 4).symm raw
    let out := (c.evalVector interpretation x).get
    (List.finRange 4).all fun i =>
      out i == (List.finRange 4).any fun j => j != i && x j == x i

-- Empty keys all agree, including on zero-width records; singleton arrays have no duplicates.
/-- info: (#[true, true, true, true], #[false], true) -/
#guard_msgs in
#eval
  let emptyKey : Fin 0 → Fin 0 := Fin.elim0
  (((duplicateFlagsCircuit emptyKey 2).evalVector interpretation Fin.elim0).toArray,
    ((duplicateFlagsCircuit emptyKey 0).evalVector interpretation Fin.elim0).toArray,
    (List.finRange 8).all fun raw =>
      !((duplicateFlagsCircuit (![2, 0] : Fin 2 → Fin 3) 0).evalVector interpretation
        ((BitString.equivFin 3).symm raw)).get ⟨0, by decide⟩)

-- The already-sorted detector also admits the empty array, with no gates.
example : (adjacentDuplicateCircuit (Fin.elim0 : Fin 0 → Fin 2 → Fin 0)).size = 0 := by
  simp [adjacentDuplicateCircuit, adjacentEqualityCircuit, Circuit.size_comp, Circuit.size_pi]

-- The exact formula charges constants even when there are no comparisons or key bits.
example : (duplicateFlagsCircuit (Fin.elim0 : Fin 0 → Fin 0) 0).size = 2 := by
  rw [size_duplicateFlagsCircuit]
  rfl

example : (duplicateFlagsCircuit (![2, 0] : Fin 2 → Fin 3) 2).size = 272 := by
  rw [size_duplicateFlagsCircuit]
  rfl

-- Nonuniform weights distinguish the two constants, negations, AND gates and OR gates.
/-- info: (272, 814) -/
#guard_msgs in
#eval
  let cost : signature.Op → ℕ := fun
    | .const false => 7
    | .const true => 11
    | .not => 5
    | .and => 2
    | .or => 3
  let c := duplicateFlagsCircuit (![2, 0] : Fin 2 → Fin 3) 2
  (c.size, c.program.cost cost)

end CslibFrontierTests.DuplicateFlags
