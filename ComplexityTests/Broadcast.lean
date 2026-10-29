/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Broadcast
import Complexity.Computability.Circuit.Boolean.KeyedSort
import Complexity.Computability.Circuit.Evaluation
import Complexity.Foundations.Data.BitString.Basic

/-!
# Record broadcast clients

Check duplicate sources, repeated destinations, missing sources, ignored destination values,
metadata preservation, alternative selectors, empty dimensions and distinct gate weights.
Exhaustive checks compare every output with an independent interval-based reference.
-/

namespace ComplexityTests.Broadcast

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open broadcastCircuit (header value)

private def weights : signature.Op → ℕ
  | .const false => 11
  | .const true => 13
  | .not => 7
  | .and => 3
  | .or => 5

-- Overlapping, repeated, and empty selectors for `Formula.equalBits`, and their weighted gate
-- costs.
example (x₀ : BitString 0) :
    (∀ x : BitString 3,
      (Formula.equalBits ![2, 0, 2] ![0, 0, 0]).eval interpretation x = true ↔ x 2 = x 0) ∧
    (Formula.equalBits (Fin.elim0 : Fin 0 → Fin 0) Fin.elim0).eval interpretation x₀ = true ∧
    (Formula.equalBits (![2, 0, 2] : Fin 3 → Fin 3) ![0, 0, 0]).cost weights = 97 ∧
    (Formula.equalBits (Fin.elim0 : Fin 0 → Fin 0) Fin.elim0).cost weights = 13 :=
  ⟨by decide +kernel, rfl, by decide +kernel, rfl⟩

private def key : Fin 1 → Fin 2 := fun _ => 0

-- A source sees only the preceding prefix; both destinations see the OR of both source values.
/-- info: #[false, false, true, false, false, false, true, true, false, true, true, true, false, true, true, true] -/
#guard_msgs in
#eval ((broadcastCircuit key 1 4 2).evalVector interpretation
  ![false, false, true, false, false, false, false, true,
    false, true, false, false, false, true, false, true]).toArray

-- Destination payloads do not seed the scan, even when every input value is true.
/-- info: #[false, true, false, false, true, true, false, false] -/
#guard_msgs in
#eval ((broadcastCircuit key 1 2 2).evalVector interpretation
  ![false, true, true, true, true, true, true, true]).toArray

-- Metadata is first, tag second, key third; the missing key has no source.
private def metadataInput : BitString 15 :=
  ![true, false, false, true, false,
    false, true, false, false, true,
    true, true, true, true, true]

private def metadataKey : Fin 1 → Fin 3 := fun _ => 2

/-- info: #[true, false, false, true, false, false, true, false, true, false, true, true, true, false, false] -/
#guard_msgs in
#eval ((broadcastCircuit metadataKey 1 3 2).evalVector interpretation metadataInput).toArray

-- The source-copy theorem applies to a concrete satisfiable sorted/unique-source contract.
example : value ((broadcastCircuit metadataKey 1 3 2).eval interpretation metadataInput)
    (1 : Fin 3) = value (headerWidth := 3) metadataInput (0 : Fin 3) := by
  apply eval_broadcastCircuit_value_of_unique_source (count := 3) (width := 2)
    metadataKey 1 metadataInput
    (source := 0) (destination := 1)
  · intro a b hab
    apply Pi.toLex_monotone
    revert a b
    decide +kernel
  all_goals decide +kernel

-- Empty keys give one segment, ordered only by tag.
/-- info: #[false, true, true, true, true, true] -/
#guard_msgs in
#eval ((broadcastCircuit (Fin.elim0 : Fin 0 → Fin 1) 0 3 1).evalVector interpretation
  ![false, true, true, false, true, false]).toArray

-- Empty value fields preserve every input bit while retaining shared key-test costs; weighted
-- costs and sizes match across empty/non-empty counts, widths, and keys.
example :
    (∀ x : BitString 8, (broadcastCircuit key 1 4 0).eval interpretation x = x) ∧
      (broadcastCircuit key 1 4 0).program.cost weights = 134 ∧
      (broadcastCircuit key 1 0 3).program.cost weights = 33 ∧
      (broadcastCircuit key 1 0 0).program.cost weights = 0 ∧
      (broadcastCircuit key 1 4 2).program.cost weights = 300 ∧
      (broadcastCircuit key 1 4 2).size = 56 ∧
      (broadcastCircuit (Fin.elim0 : Fin 0 → Fin 1) 0 3 2).program.cost weights = 167 := by
  refine ⟨?_, by decide +kernel, by decide +kernel, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
  intro x
  funext i
  obtain ⟨⟨record, bit⟩, rfl⟩ := (finProdFinEquiv (m := 4) (n := 2)).surjective i
  simpa only [header, directProductInput, Function.comp_apply, Fin.castAdd_zero,
    Fin.cast_refl, id_eq] using
    congrFun (eval_broadcastCircuit_header (width := 0) key 1 x record) bit

/-- info: #[] -/
#guard_msgs in
#eval ((broadcastCircuit key 1 0 3).evalVector interpretation Fin.elim0).toArray

-- A header key/tag projection is an ordinary wiring circuit; no new sorting wrapper is needed.
private def sortKey {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (width : ℕ) :
    Circuit signature (h + width) (k + 1) :=
  Circuit.wiring signature (Fin.snoc (α := fun _ => Fin (h + width))
    (Fin.castAdd width ∘ key) (Fin.castAdd width tag))

example {h k width depth : ℕ} (key : Fin k → Fin h) (tag : Fin h)
    (x : BitString (BitonicSort.arity depth * (h + width)))
    (destination : Fin (BitonicSort.arity depth))
    (htag : header ((keyedSortCircuit (sortKey key tag width) depth true).eval interpretation x)
      destination tag = true) (bit : Fin width) :
    let sorted := (keyedSortCircuit (sortKey key tag width) depth true).eval interpretation x
    value ((broadcastCircuit key tag (BitonicSort.arity depth) width).eval interpretation sorted)
      destination bit = true ↔
      ∃ source, header sorted source ∘ key = header sorted destination ∘ key ∧
        header sorted source tag = false ∧ value sorted source bit = true := by
  dsimp only
  apply eval_broadcastCircuit_value_eq_true_iff key tag _ _ destination htag bit
  simpa only [sortKey, Circuit.eval_wiring, Fin.comp_snoc, Function.comp_assoc,
    Function.comp_apply, header] using
    monotone_keyedSortCircuit (sortKey key tag width) depth x

-- Compare the whole unsorted scan with a direct existential over constant-key intervals.
-- Also check the all-source OR specification whenever the input is sorted and tagged destination.
private def checkAll {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (count width : ℕ) : Bool :=
  let circuit := broadcastCircuit key tag count width
  (List.finRange (2 ^ (count * (h + width)))).all fun raw =>
    let input := (BitString.equivFin (count * (h + width))).symm raw
    let output := (circuit.evalVector interpretation input).get
    let head := fun (record : Fin count) (bit : Fin h) =>
      input (finProdFinEquiv (record, Fin.castAdd width bit))
    let data := fun (record : Fin count) (bit : Fin width) =>
      input (finProdFinEquiv (record, Fin.natAdd h bit))
    let sameKey := fun a b => (List.finRange k).all fun i => head a (key i) == head b (key i)
    let ordered := (List.finRange count).all fun a => (List.finRange count).all fun b =>
      !decide (a ≤ b) ||
        compare (List.ofFn (Fin.snoc (α := fun _ => Bool) (head a ∘ key) (head a tag)))
          (List.ofFn (Fin.snoc (α := fun _ => Bool) (head b ∘ key) (head b tag))) != .gt
    (List.finRange count).all fun record =>
      ((List.finRange h).all fun bit =>
        output (finProdFinEquiv (record, Fin.castAdd width bit)) == head record bit) &&
      ((List.finRange width).all fun bit =>
        let expected := (List.finRange count).any fun source =>
          decide (source ≤ record) && !head source tag && data source bit &&
            ((List.finRange count).all fun i =>
              !decide (source ≤ i ∧ i ≤ record) || sameKey i record)
        let allSources := (List.finRange count).any fun source =>
          sameKey source record && !head source tag && data source bit
        output (finProdFinEquiv (record, Fin.natAdd h bit)) == expected &&
          (!(ordered && head record tag) || expected == allSources))

-- Three 4096-input families plus 64 empty-key inputs: 12,352 circuit evaluations.
/-- info: true -/
#guard_msgs in
#eval checkAll key 1 3 2 && checkAll key 1 4 1 &&
  checkAll (![2, 2] : Fin 2 → Fin 3) 1 3 1 &&
  checkAll (Fin.elim0 : Fin 0 → Fin 1) 0 3 1

end ComplexityTests.Broadcast
