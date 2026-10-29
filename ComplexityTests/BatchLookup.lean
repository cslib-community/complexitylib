/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.BatchLookup
import ComplexityTests.CircuitMaterialize

/-!
# Batched lookup clients

Exercise the actual circuits on repeated queries, all small tables, duplicate sources, extra
padding, and empty dimensions. These compiled regression cases supplement the general proofs;
they do not introduce trusted computational axioms. Exhaustive checks evaluate the materialized
circuit, which `materialize_eq` proves equal to the original.
-/

namespace ComplexityTests.BatchLookup

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open bitonicSortTraceCircuit ComplexityTests.CircuitMaterialize

example {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ)
    (x : BitString (requests * k)) :
    (batchLookupCircuit table requests).eval interpretation x = blockMap table requests x := by
  simp

example {k v : ℕ} (table : BitString k → BitString v) (requests : ℕ) :
    complexity interpretation (blockMap table requests) ≤
      48 * (requests + 2 ^ k) * (Nat.clog 2 (requests + 2 ^ k) + 1) ^ 2 * (k + v + 1) :=
  complexity_blockMap_le_lookup table requests

example {k v requests padding d : ℕ} (table : BitString k → BitString v)
    (h : requests + (2 ^ k + padding) = BitonicSort.arity d) (cost : signature.Op → ℕ) :
    (batchLookupCircuit.withPadding table h).program.cost cost =
      (routeValuesCircuit Fin.castSucc (Fin.last k) d v).program.cost cost +
        cost (.const false) + cost (.const true) :=
  batchLookupCircuit.cost_program_withPadding table h cost

-- The substitution uses two constant gates even for an empty output.
example : (substituteCircuit (Fin.elim0 : Fin 0 → Fin 0 ⊕ Bool)).size = 2 := by
  simp

example (table : BitString 2 → BitString 1) : (batchLookupCircuit table 3).size = 1327 := by
  rw [batchLookupCircuit, batchLookupCircuit.size_withPadding]
  rfl

example (table : BitString 0 → BitString 0) : (batchLookupCircuit table 0).size = 3 := by
  rw [batchLookupCircuit, batchLookupCircuit.size_withPadding]
  rfl

-- All 16 Boolean tables on two-bit keys and all 64 triples of queries: 1024 cases.
/-- info: true -/
#guard_msgs in
#eval
  (List.finRange 16).all fun tableBits =>
    let table : BitString 2 → BitString 1 := fun key _ =>
      ((BitString.equivFin 4).symm tableBits) ((BitString.equivFin 2) key)
    let c := materialize (batchLookupCircuit table 3)
    (List.finRange 64).all fun raw =>
      let x := (BitString.equivFin 6).symm raw
      List.ofFn ((c.evalVector interpretation x).get) == List.ofFn (blockMap table 3 x)

-- All 16 two-bit-valued tables on a one-bit key and all query triples: 128 cases.
/-- info: true -/
#guard_msgs in
#eval
  (List.finRange 16).all fun rawTable =>
    let table : BitString 1 → BitString 2 := fun key bit =>
      ((BitString.equivFin 4).symm rawTable) (finProdFinEquiv ((BitString.equivFin 1) key, bit))
    let c := materialize (batchLookupCircuit table 3)
    (List.finRange 8).all fun raw =>
      let x := (BitString.equivFin 3).symm raw
      List.ofFn ((c.evalVector interpretation x).get) == List.ofFn (blockMap table 3 x)

-- Uniqueness is needed only to copy one source; destinations with several sources get their OR.
-- Check all 4096 four-record inputs against a direct search through the original rows.
/-- info: true -/
#guard_msgs in
#eval
  let c := materialize (routeValuesCircuit (Fin.castSucc : Fin 1 → Fin 2) (Fin.last 1) 2 1)
  (List.finRange 4096).all fun raw =>
    let x := (BitString.equivFin 12).symm raw
    let rows : Fin 4 → BitString 3 := directProductInput x
    let out := (c.evalVector interpretation x).get
    (List.finRange 4).all fun j =>
      !rows j 1 || (out j == (List.finRange 4).any fun i =>
        rows i 0 == rows j 0 && !rows i 1 && rows i 2)

-- Extra padding must not introduce another source, even for the all-zero address.
/-- info: true -/
#guard_msgs in
#eval
  let table : BitString 2 → BitString 2 := fun x => ![x 1, !x 0]
  let c := materialize (batchLookupCircuit.withPadding table
    (by decide : 3 + (2 ^ 2 + 9) = BitonicSort.arity 4))
  (List.finRange 64).all fun raw =>
    let x := (BitString.equivFin 6).symm raw
    List.ofFn ((c.evalVector interpretation x).get) == List.ofFn (blockMap table 3 x)

-- The one-address table (empty keys) supports arbitrary repetitions and zero requests.
/-- info: true -/
#guard_msgs in
#eval
  (List.finRange 4).all fun raw =>
    [0, 1, 3].all fun requests =>
      let table : BitString 0 → BitString 2 := fun _ => (BitString.equivFin 2).symm raw
      let c := batchLookupCircuit table requests
      let x : BitString (requests * 0) := fun i => False.elim (by simpa using i.isLt)
      List.ofFn ((c.evalVector interpretation x).get) == List.ofFn (blockMap table requests x)

-- Empty value fields and zero requests still produce the correct empty output.
/-- info: (true, true) -/
#guard_msgs in
#eval
  (((batchLookupCircuit (fun _ : BitString 2 => (Fin.elim0 : BitString 0)) 3).evalVector
      interpretation (fun _ => false)).toArray.isEmpty,
    ((batchLookupCircuit (fun x : BitString 2 => x) 0).evalVector
      interpretation Fin.elim0).toArray.isEmpty)

-- Actual gate counts agree with the exact formula; constants of different values have different
-- weights here, so accidentally duplicating or dropping one is visible.
/-- info: (1327, 18, #[true, false, true]) -/
#guard_msgs in
#eval
  let cost : signature.Op → ℕ := fun
    | .const false => 7
    | .const true => 11
    | .not => 5
    | .and => 2
    | .or => 3
  let ρ : Fin 3 → Fin 1 ⊕ Bool := ![.inr true, .inr false, .inr true]
  ((batchLookupCircuit (fun x : BitString 2 => fun _ : Fin 1 => x 0) 3).size,
    (substituteCircuit ρ).program.cost cost,
    ((substituteCircuit ρ).evalVector interpretation (fun _ => false)).toArray)

end ComplexityTests.BatchLookup
