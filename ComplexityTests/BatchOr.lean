/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.BatchOr
import Complexity.Foundations.Data.BitString.Basic
import ComplexityTests.CircuitMaterialize

/-!
# Dynamic shared OR lookup clients

Check repeated and missing keys, independent value bits, empty arrays and extra padding on the
actual circuits. Exhaustive compiled examples supplement the general correctness proofs; the
512-input check evaluates the materialized circuit, which `materialize_eq` proves equal to the
original.
-/

namespace ComplexityTests.BatchOr

open Cslib Cslib.Circuits Cslib.Circuits.Boolean ComplexityTests.CircuitMaterialize

-- Two one-bit source keys, two two-bit values, and three one-bit queries: all 512 inputs.
/-- info: true -/
#guard_msgs in
#eval
  let sourceKeys : Fin 2 → Fin 1 → Fin 9 ⊕ Bool := fun i _ => .inl ⟨i.val, by lia⟩
  let sourceValues : Fin 2 → Fin 2 → Fin 9 ⊕ Bool := fun i bit =>
    .inl ⟨2 + 2 * i.val + bit.val, by lia⟩
  let queryKeys : Fin 3 → Fin 1 → Fin 9 ⊕ Bool := fun i _ => .inl ⟨6 + i.val, by lia⟩
  let c := materialize (batchOrCircuit sourceKeys sourceValues queryKeys)
  (List.finRange 512).all fun raw =>
    let x := (BitString.equivFin 9).symm raw
    let out := (c.evalVector interpretation x).get
    (List.finRange 3).all fun j => (List.finRange 2).all fun bit =>
      out (finProdFinEquiv (j, bit)) == (List.finRange 2).any fun i =>
        x ⟨i.val, by lia⟩ == x ⟨6 + j.val, by lia⟩ && x ⟨2 + 2 * i.val + bit.val, by lia⟩

-- Empty source arrays return false; padding destinations never become sources.
/-- info: true -/
#guard_msgs in
#eval
  let queryKeys : Fin 3 → Fin 1 → Fin 3 ⊕ Bool := fun i _ => .inl i
  let c := batchOrCircuit.withPadding
    (Fin.elim0 : Fin 0 → Fin 1 → Fin 3 ⊕ Bool)
    (Fin.elim0 : Fin 0 → Fin 2 → Fin 3 ⊕ Bool) queryKeys
    (by decide : 3 + (0 + 5) = BitonicSort.arity 3)
  (List.finRange 8).all fun raw =>
    ((c.evalVector interpretation ((BitString.equivFin 3).symm raw)).toArray).all (!·)

-- Empty keys match every source. All value assignments remain independent across bits.
/-- info: true -/
#guard_msgs in
#eval
  let sourceValues : Fin 2 → Fin 2 → Fin 4 ⊕ Bool := fun i bit =>
    .inl (finProdFinEquiv (i, bit))
  let c := batchOrCircuit (fun _ : Fin 2 => (Fin.elim0 : Fin 0 → Fin 4 ⊕ Bool))
    sourceValues (fun _ : Fin 3 => (Fin.elim0 : Fin 0 → Fin 4 ⊕ Bool))
  (List.finRange 16).all fun raw =>
    let x := (BitString.equivFin 4).symm raw
    let out := (c.evalVector interpretation x).get
    (List.finRange 3).all fun j => (List.finRange 2).all fun bit =>
      out (finProdFinEquiv (j, bit)) == (x (finProdFinEquiv ((0 : Fin 2), bit)) ||
        x (finProdFinEquiv ((1 : Fin 2), bit)))

-- Empty outputs and the entirely empty layout still have their charged preparation gates.
/-- info: (true, true, 3) -/
#guard_msgs in
#eval
  let noRequests := batchOrCircuit (fun _ : Fin 2 => (fun _ : Fin 1 => Sum.inr false))
    (fun _ : Fin 2 => (fun _ : Fin 1 => Sum.inr true))
    (Fin.elim0 : Fin 0 → Fin 1 → Fin 0 ⊕ Bool)
  let noValues := batchOrCircuit (fun _ : Fin 2 => (fun _ : Fin 1 => Sum.inr false))
    (fun _ : Fin 2 => (Fin.elim0 : Fin 0 → Fin 0 ⊕ Bool))
    (fun _ : Fin 3 => (fun _ : Fin 1 => Sum.inr false))
  let empty := batchOrCircuit (Fin.elim0 : Fin 0 → Fin 0 → Fin 0 ⊕ Bool)
    (Fin.elim0 : Fin 0 → Fin 0 → Fin 0 ⊕ Bool)
    (Fin.elim0 : Fin 0 → Fin 0 → Fin 0 ⊕ Bool)
  ((noRequests.evalVector interpretation Fin.elim0).toArray.isEmpty,
    (noValues.evalVector interpretation Fin.elim0).toArray.isEmpty, empty.size)

end ComplexityTests.BatchOr
