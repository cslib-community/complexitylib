/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Routing
import CslibFrontier.Computability.Circuit.Evaluation
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontierTests.CircuitMaterialize

/-!
# Two-sort routing clients

Check computed restoration keys, repeated requests, fixed output positions, empty fields,
aliased selectors, and exact weighted costs. Exhaustive checks test destination semantics,
header preservation and restoration-key ordering against the original input. They evaluate the
materialized circuit, which `materialize_eq` proves equal to the original.
-/

namespace CslibFrontierTests.Routing

open Cslib Cslib.Circuits Cslib.Circuits.Boolean broadcastCircuit Finset
open CslibFrontierTests.CircuitMaterialize

private def key : Fin 1 → Fin 3 := ![0]
private def order : Circuit signature 3 2 :=
  (Formula.input 1).not.toCircuit.append (Circuit.wiring signature ![2])
private def input : BitString (4 * (3 + 1)) :=
  ![false, false, false, true, false, true, true, false,
    false, true, false, false, true, false, false, false]

private theorem order_lt (i j : Fin 4) :
    toLex (order.eval interpretation (header input i)) <
      toLex (order.eval interpretation (header input j)) ↔
      (![2, 1, 0, 2] : Fin 4 → ℕ) i < (![2, 1, 0, 2] : Fin 4 → ℕ) j := by
  revert i j
  change ∀ i j : Fin 4, Pi.Lex (· < ·) (· < ·)
    (order.eval interpretation (header input i)) (order.eval interpretation (header input j)) ↔ _
  unfold Pi.Lex
  decide +kernel

private def weights : signature.Op → ℕ
  | .const false => 11
  | .const true => 13
  | .not => 7
  | .and => 3
  | .or => 5

-- The computed ordering key negates the tag once for every record.
example : order.size = 1 := by decide +kernel
example : (routeCircuit key 1 order 2 1).size = 643 := by decide +kernel
example : (routeCircuit key 1 order 0 1).size = 7 := by decide +kernel

example : (routeCircuit key 1 order 2 1).program.cost weights = 2765 := by decide +kernel
example : (routeCircuit key 1 order 2 0).program.cost weights = 2418 := by decide +kernel
example : (routeCircuit key 1 order 0 0).program.cost weights = 18 := by decide +kernel
example : (routeCircuit key 1 order 2 0).size = 554 := by decide +kernel

-- Both destinations request the same source, but their identifiers restore distinct positions.
private def destination : Fin 2 → Fin 4 := ![2, 1]

example (request : Fin 2) :
    value ((routeCircuit key 1 order 2 1).eval interpretation input) (Fin.castAdd 2 request) =
      value input 0 := by
  apply eval_routeCircuit_value_of_unique_source (depth := 2) (width := 1)
    key 1 order input (0 : Fin 4) (destination request) (Fin.castAdd 2 request)
  · change ∀ i : Fin 4, order.eval interpretation (header input i) =
      order.eval interpretation (header input (destination request)) → i = destination request
    revert request
    decide +kernel
  · classical
    change #{i : Fin 4 | toLex (order.eval interpretation (header input i)) <
      toLex (order.eval interpretation (header input (destination request)))} = request.val
    simp only [order_lt]
    revert request
    decide +kernel
  · revert request
    decide +kernel
  · rfl
  · revert request
    decide +kernel
  · change ∀ i : Fin 4, header input i ∘ key = header input (0 : Fin 4) ∘ key →
      header input i 1 = false → i = 0
    decide +kernel

private def destinationFirst {h k : ℕ} (tag : Fin h) (id : Fin k → Fin h) :
    Circuit signature h (1 + k) :=
  (Formula.input tag).not.toCircuit.append (Circuit.wiring signature id)

-- Empty ordering keys do not imply unique restoration positions when there are several records.
example : ¬ ∃ i : Fin 2, ∀ j : Fin 2,
    (Fin.elim0 : BitString 0) = Fin.elim0 → j = i := by decide +kernel

example : (routeCircuit (Fin.elim0 : Fin 0 → Fin 1) 0
    (Circuit.wiring signature Fin.elim0 : Circuit signature 1 0) 1 0).size = 30 := by
  decide +kernel

-- Check preserved headers, sorted restoration keys, every destination bit, and every
-- uniquely keyed header's literal output rank. Sources retain prefix accumulation.
private def checkAll {h k o : ℕ} (key : Fin k → Fin h) (tag : Fin h)
    (order : Circuit signature h o) (depth width : ℕ) : Bool :=
  let count := BitonicSort.arity depth
  let circuit := materialize (routeCircuit key tag order depth width)
  let records := List.finRange count
  (List.finRange (2 ^ (count * (h + width)))).all fun raw =>
    let x := (BitString.equivFin (count * (h + width))).symm raw
    let y := (circuit.evalVector interpretation x).get
    let head := fun (z : BitString (count * (h + width))) (i : Fin count) =>
      fun bit : Fin h => z (finProdFinEquiv (i, Fin.castAdd width bit))
    let payload := fun (z : BitString (count * (h + width))) (i : Fin count) (bit : Fin width) =>
      z (finProdFinEquiv (i, Fin.natAdd h bit))
    let orderKey := fun z i => List.ofFn ((order.evalVector interpretation (head z i)).get)
    let retained := decide ((records.map (fun i => List.ofFn (head y i))).Perm
      (records.map (fun i => List.ofFn (head x i))))
    let ordered := records.all fun a => records.all fun b =>
      !decide (a ≤ b) || compare (orderKey y a) (orderKey y b) != .gt
    let values := records.all fun destination => !head y destination tag ||
      (List.finRange width).all fun bit =>
        let expected := records.any fun source =>
          !head x source tag && payload x source bit &&
            (List.finRange k).all (fun i => head x source (key i) == head y destination (key i))
        payload y destination bit == expected
    let restored := records.all fun destination =>
      let code := orderKey x destination
      if records.countP (fun i => orderKey x i == code) = 1 then
        let rank := records.countP (fun i => compare (orderKey x i) code == .lt)
        if hi : rank < count then
          List.ofFn (head y ⟨rank, hi⟩) == List.ofFn (head x destination)
        else false
      else true
    retained && ordered && values && restored

-- 4096 general four-record inputs and 516 smaller boundary cases.
/-- info: true -/
#guard_msgs in
#eval checkAll (![0] : Fin 1 → Fin 2) 1 (destinationFirst 1 ![0]) 2 1 &&
  checkAll key 1 order 1 1 &&
  checkAll key 1 order 1 0 &&
  checkAll (Fin.elim0 : Fin 0 → Fin 2) 1 (destinationFirst 1 ![0]) 1 1 &&
  checkAll (![1, 1] : Fin 2 → Fin 2) 1 (destinationFirst 1 ![0]) 1 1 &&
  checkAll (![0] : Fin 1 → Fin 2) 1
    (Circuit.wiring signature Fin.elim0 : Circuit signature 2 0) 1 1 &&
  checkAll (Fin.elim0 : Fin 0 → Fin 1) 0
    (Circuit.wiring signature Fin.elim0 : Circuit signature 1 0) 0 1

end CslibFrontierTests.Routing

