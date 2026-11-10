/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.CompareSwap
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Compare-exchange clients

Exercise stable ties, empty records and keys, and arbitrary selected coordinates. Compiled
checks use the stored evaluator; kernel checks and the public semantics cover the same API.
-/

namespace CslibFrontierTests.CompareSwap

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

-- Prefix keys use the ordinary inclusion, without a special comparator constructor.
example {k r : ℕ} (h : k ≤ r) (hr : r ≠ 0) :
    (compareSwapCircuit (Fin.castLE h)).size = 6 * k + 6 * r + 2 := by
  simp [hr]

example {k r : ℕ} (h : k ≤ r) (x y : BitString r) :
    let output := (compareSwapCircuit (Fin.castLE h)).eval interpretation (Fin.append x y)
    toLex (fun i => output (Fin.castAdd r (Fin.castLE h i))) ≤
      toLex (fun i => output (Fin.natAdd r (Fin.castLE h i))) :=
  compareSwapCircuit_keys_ordered (Fin.castLE h) x y

-- Empty keys leave every payload unchanged, even when records are nonempty.
example {r : ℕ} (x y : BitString r) :
    (compareSwapCircuit (Fin.elim0 : Fin 0 → Fin r)).eval interpretation (Fin.append x y) =
      Fin.append x y := by
  apply eval_compareSwapCircuit_of_key_eq
  funext i
  exact i.elim0

example : (compareSwapCircuit (Fin.elim0 : Fin 0 → Fin 3)).size = 20 := by
  simp

-- No gates or input values are needed for empty records.
example : (compareSwapCircuit (Fin.elim0 : Fin 0 → Fin 0)).size = 0 := by
  simp

/-- info: #[] -/
#guard_msgs in
#eval ((compareSwapCircuit (Fin.elim0 : Fin 0 → Fin 0)).evalVector
  interpretation Fin.elim0).toArray

-- A one-bit kernel computation also checks the circuit independently of compiler replacements.
example : (compareSwapCircuit (id : Fin 1 → Fin 1)).eval interpretation ![true, false] =
    ![false, true] := by
  decide +kernel

example : (Formula.lexLt ![0, 1] ![2, 3]).eval interpretation ![false, true, true, false] =
    true := by
  decide +kernel

-- Coordinate zero is most significant for comparison, unlike the numeric bit-string encoding.
example : BitString.equivFin 2 ![true, false] < BitString.equivFin 2 ![false, true] := by
  decide +kernel

/-- info: #[false, true, true, false] -/
#guard_msgs in
#eval ((compareSwapCircuit (id : Fin 2 → Fin 2)).evalVector interpretation
  (Fin.append ![true, false] ![false, true])).toArray

-- Equal keys retain different payloads in their original order.
/-- info: #[true, false, true, true] -/
#guard_msgs in
#eval ((compareSwapCircuit (fun _ : Fin 1 => (0 : Fin 2))).evalVector interpretation
  (Fin.append ![true, false] ![true, true])).toArray

-- A non-prefix, repeated selector is legal and compares in the selected order.
/-- info: #[true, true, false, false, false, true] -/
#guard_msgs in
#eval ((compareSwapCircuit (![2, 0, 2] : Fin 3 → Fin 3)).evalVector interpretation
  (Fin.append ![false, false, true] ![true, true, false])).toArray

example : (compareSwapCircuit (![2, 0, 2] : Fin 3 → Fin 3)).size = 38 := by
  simp

-- All nine two-coordinate selectors, including repetitions, on all 64 pairs of three-bit
-- records. The reference uses the executable list comparator and preserves ties.
/-- info: true -/
#guard_msgs in
#eval
  (List.finRange 3).all fun a => (List.finRange 3).all fun b =>
    let key : Fin 2 → Fin 3 := ![a, b]
    let c := compareSwapCircuit key
    (List.finRange 8).all fun i => (List.finRange 8).all fun j =>
      let x := (BitString.equivFin 3).symm i
      let y := (BitString.equivFin 3).symm j
      let swap := (List.ofFn (y ∘ key)).lex (List.ofFn (x ∘ key)) (fun u v => !u && v)
      let expected := if swap then Fin.append y x else Fin.append x y
      (c.evalVector interpretation (Fin.append x y)).toArray == (Vector.ofFn expected).toArray

end CslibFrontierTests.CompareSwap
