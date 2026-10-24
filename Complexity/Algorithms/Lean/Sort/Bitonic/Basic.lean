/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.MinMax
import Mathlib.Data.List.FinRange

/-!
# Batcher sorting on finite tuples

The algorithm sorts a power-of-two tuple of records by a separate key. Each layer compares
corresponding records in two halves and moves whole records. Ascending comparisons retain ties;
descending comparisons reverse the ascending result, including ties. The complete sorter is
not a stable sorting algorithm.

## Main definitions

* `Cslib.BitonicSort.arity`: the power-of-two number of records, with a definitional split.
* `Cslib.BitonicSort.IsBitonic`: the four-point lattice invariant used by bitonic merge.
* `Cslib.BitonicSort.compareLayer`: one layer of independent comparisons.
* `Cslib.BitonicSort.merge`: recursively merge a bitonic tuple.
* `Cslib.BitonicSort.sort`: Batcher's recursive sorter.

## Main results

* `Cslib.BitonicSort.compareLayer_perm`, `Cslib.BitonicSort.merge_perm`, and
  `Cslib.BitonicSort.sort_perm`: each stage preserves the multiset of complete records.

## References

* [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
* Adapted from MassProduction/SortingSemantics/Defs.lean and
  MassProduction/SortingSemantics/Internal.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.BitonicSort

variable {α κ : Type*}

/-- The number of records at a given depth, with a definitional split into two equal halves. -/
def arity : ℕ → ℕ
  | 0 => 1
  | depth + 1 => arity depth + arity depth

/-- The arity at `depth` is `2 ^ depth`. -/
@[simp] theorem arity_eq_two_pow (depth : ℕ) : arity depth = 2 ^ depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [arity, ih, Nat.pow_succ, Nat.mul_two]

/-- Four-point lattice invariant for bitonic merge. The four indices are in cyclic order;
the two inequalities exclude alternating high and low values. -/
def IsBitonic [LinearOrder κ] {n : ℕ} (input : Fin n → κ) : Prop :=
  ∀ i j k l, i < j → j < k → k < l →
    min (input i) (input k) ≤ max (input j) (input l) ∧
      min (input j) (input l) ≤ max (input i) (input k)

/-- Compare corresponding records in the two halves. Descending order reverses the ascending
comparison, so descending ties are exchanged. -/
def compareLayer [LinearOrder κ] (key : α → κ) {n : ℕ} (ascending : Bool)
    (input : Fin (n + n) → α) : Fin (n + n) → α :=
  input ∘ source key ascending input
where
  /-- The source position selected by a layer; corresponding positions are exchanged together. -/
  source (key : α → κ) {n : ℕ} (ascending : Bool)
      (input : Fin (n + n) → α) :
      Fin (n + n) → Fin (n + n) :=
    let exchange (i : Fin n) :=
      let outOfOrder := key (input (Fin.natAdd n i)) < key (input (Fin.castAdd n i))
      if ascending then outOfOrder else ¬outOfOrder
    Fin.addCases
      (fun i => if exchange i then Fin.natAdd n i else Fin.castAdd n i)
      (fun i => if exchange i then Fin.castAdd n i else Fin.natAdd n i)

/-- Merge a bitonic tuple by comparing corresponding halves and recursively merging each half. -/
def merge [LinearOrder κ] (key : α → κ) : (depth : ℕ) → Bool →
    (Fin (arity depth) → α) → Fin (arity depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
    let compared := compareLayer key (n := arity depth) ascending input
    Fin.append
      (merge key depth ascending (compared ∘ Fin.castAdd (arity depth)))
      (merge key depth ascending (compared ∘ Fin.natAdd (arity depth)))

/-- Sort each half in opposite directions, then merge the resulting bitonic tuple. -/
def sort [LinearOrder κ] (key : α → κ) : (depth : ℕ) → Bool →
    (Fin (arity depth) → α) → Fin (arity depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
    merge key (depth + 1) ascending (Fin.append
      (sort key depth true (input ∘ Fin.castAdd (arity depth)))
      (sort key depth false (input ∘ Fin.natAdd (arity depth))))

private theorem source_involutive [LinearOrder κ] (key : α → κ) {n : ℕ}
    (ascending : Bool) (input : Fin (n + n) → α) :
    Function.Involutive (compareLayer.source key ascending input) := by
  intro index
  cases index using Fin.addCases <;>
    simp only [compareLayer.source, Fin.addCases_left, Fin.addCases_right] <;>
    split_ifs <;> simp_all [-Fin.natAdd_eq_addNat]

/-- A layer preserves the multiset of complete records, even when some keys agree. -/
theorem compareLayer_perm [LinearOrder κ] (key : α → κ) {n : ℕ}
    (ascending : Bool) (input : Fin (n + n) → α) :
    (List.ofFn (compareLayer key ascending input)).Perm (List.ofFn input) :=
  (Function.Involutive.toPerm _ (source_involutive key ascending input)).ofFn_comp_perm input

/-- Bitonic merge preserves the multiset of complete records on every input. -/
theorem merge_perm [LinearOrder κ] (key : α → κ) (depth : ℕ)
    (ascending : Bool) (input : Fin (arity depth) → α) :
    (List.ofFn (merge key depth ascending input)).Perm (List.ofFn input) := by
  induction depth generalizing ascending with
  | zero => exact List.Perm.refl _
  | succ depth ih =>
    let compared := compareLayer key (n := arity depth) ascending input
    have h := (ih ascending (compared ∘ Fin.castAdd (arity depth))).append
      (ih ascending (compared ∘ Fin.natAdd (arity depth)))
    have hsplit : Fin.append (compared ∘ Fin.castAdd (arity depth))
        (compared ∘ Fin.natAdd (arity depth)) = compared := Fin.append_castAdd_natAdd
    rw [← List.ofFn_fin_append, ← List.ofFn_fin_append, hsplit] at h
    exact h.trans (compareLayer_perm key ascending input)

/-- Batcher sorting preserves complete records, not merely their projected keys. -/
theorem sort_perm [LinearOrder κ] (key : α → κ) (depth : ℕ)
    (ascending : Bool) (input : Fin (arity depth) → α) :
    (List.ofFn (sort key depth ascending input)).Perm (List.ofFn input) := by
  induction depth generalizing ascending with
  | zero => exact List.Perm.refl _
  | succ depth ih =>
    have h := (ih true (input ∘ Fin.castAdd (arity depth))).append
      (ih false (input ∘ Fin.natAdd (arity depth)))
    have hsplit : Fin.append (input ∘ Fin.castAdd (arity depth))
        (input ∘ Fin.natAdd (arity depth)) = input := Fin.append_castAdd_natAdd
    rw [← List.ofFn_fin_append, ← List.ofFn_fin_append, hsplit] at h
    exact (merge_perm key (depth + 1) ascending _).trans h

end Cslib.BitonicSort
