/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Equality
public import Complexity.Computability.Circuit.Boolean.SortingTrace
import Complexity.Algorithms.Lean.Sort.Bitonic.Correctness
import Complexity.Foundations.Data.Fin.Order
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring

/-!
# Duplicate flags with shared comparisons and saved swaps

A sorted array has a repeated key at a position exactly when that key equals a neighbor.
`adjacentDuplicateCircuit` computes each adjacent equality once and shares it between the
neighbors. It adds one OR gate per record; the last record reuses the first equality output,
which is false, for its missing successor. The empty array uses no gates.

`duplicateFlagsCircuit` accepts an arbitrary array of `2 ^ d` records. It sorts by selected key
coordinates, computes the flags, then reverses the saved swaps on the flags alone. Outputs refer
to the original positions, including when complete records repeat. No record identifiers or
second sort are needed. Header and payload bits can be retained by free input wiring.

Costs include constants and negations. Gate counts do not certify construction runtime.

## Main definitions

* `Cslib.Circuits.Boolean.adjacentDuplicateCircuit`: share adjacent-key equality tests.
* `Cslib.Circuits.Boolean.duplicateFlagsCircuit`: duplicate flags in original input order.

## Main results

* `Cslib.Circuits.Boolean.eval_adjacentDuplicateCircuit_iff`: exact detection on sorted keys.
* `Cslib.Circuits.Boolean.eval_duplicateFlagsCircuit_iff`: exact detection on arbitrary inputs.
* `Cslib.Circuits.Boolean.cost_program_duplicateFlagsCircuit`: exact weighted gate cost.
* `Cslib.Circuits.Boolean.size_duplicateFlagsCircuit`: exact total gate count.

## References

Simplifies MassProduction/Nonuniform/AdjacentDuplicates.lean and the conflict-detection
construction in
[S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
using the saved decisions of
[K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open bitonicSortTraceCircuit

/-- Test both neighbors, sharing each adjacent equality once. -/
def adjacentDuplicateCircuit {input count k : ℕ} (key : Fin count → Fin k → Fin input) :
    Circuit signature input count :=
  (Circuit.pi fun i : Fin count =>
    ((Formula.input i).or (Formula.input (if h : i.val + 1 < count then ⟨i.val + 1, h⟩
      else ⟨0, by lia⟩))).toCircuit).comp (adjacentEqualityCircuit key)

/-- On sorted keys, adjacent equality detects every repeated key. -/
theorem eval_adjacentDuplicateCircuit_iff {input count k : ℕ}
    (key : Fin count → Fin k → Fin input) (x : BitString input)
    (ordered : Monotone (fun i => toLex (x ∘ key i))) (i : Fin count) :
    (adjacentDuplicateCircuit key).eval interpretation x i = true ↔
      ∃ j, j ≠ i ∧ x ∘ key j = x ∘ key i := by
  rw [show (∃ j, j ≠ i ∧ x ∘ key j = x ∘ key i) ↔
    ∃ j, j ≠ i ∧ toLex (x ∘ key j) = toLex (x ∘ key i) by simp only [toLex_inj],
    Fin.exists_ne_apply_eq_iff_adjacent _ ordered]
  simp only [toLex_inj, adjacentDuplicateCircuit, Circuit.eval_comp, Circuit.eval_pi,
    Formula.eval_toCircuit, Formula.eval_or, Formula.eval_input, Bool.or_eq_true]
  by_cases h : i.val + 1 < count
  · simp only [h, ↓reduceDIte, eval_adjacentEqualityCircuit_iff,
      Nat.zero_lt_succ, Nat.add_sub_cancel, exists_true_left]
    exact or_congr Iff.rfl eq_comm
  · simp only [h, ↓reduceDIte, eval_adjacentEqualityCircuit_iff, Nat.lt_irrefl]
    tauto

/-- Sharing the equality outputs adds exactly one OR gate per record. -/
private theorem cost_program_adjacentDuplicateCircuit {input count k : ℕ}
    (key : Fin count → Fin k → Fin input) (cost : signature.Op → ℕ) :
    (adjacentDuplicateCircuit key).program.cost cost =
      (adjacentEqualityCircuit key).program.cost cost + count * cost .or := by
  unfold adjacentDuplicateCircuit
  rw [Circuit.cost_program_comp]
  congr 1
  erw [Circuit.cost_program_pi]
  simp [Formula.cost_toCircuit, Formula.or, Formula.cost_gate, Fin.sum_univ_two]

private theorem duplicate_iff_not_unique {α β : Type*} (f : α → β) (i : α) :
    (∃ j, j ≠ i ∧ f j = f i) ↔ ¬ ∃! j, f j = f i := by
  classical
  constructor
  · rintro ⟨j, hn, hj⟩ ⟨w, hw, hu⟩
    exact hn ((hu j hj).trans (hu i rfl).symm)
  · intro hn
    by_contra h
    exact hn ⟨i, rfl, fun j hj => by
      by_contra hji
      exact h ⟨j, hji, hj⟩⟩

namespace duplicateFlagsCircuit

/-- Regard a vector of flags as an array of one-bit records. -/
def rows (count : ℕ) : Circuit signature count (count * 1) :=
  Circuit.wiring signature fun i => (finProdFinEquiv.symm i).1

/-- Select the flag from each one-bit record. -/
def outputs (count : ℕ) : Circuit signature (count * 1) count :=
  Circuit.wiring signature fun i => finProdFinEquiv (i, 0)

private theorem eval_outputs (count : ℕ) (x : BitString (count * 1)) (i : Fin count) :
    (outputs count).eval interpretation x i = directProductInput x i 0 := by
  rw [outputs, Circuit.eval_wiring]
  rfl

private theorem eval_rows (count : ℕ) (x : BitString count) :
    directProductInput ((rows count).eval interpretation x) = fun i _ => x i := by
  funext i bit
  simp only [rows, Circuit.eval_wiring, directProductInput, Function.comp_apply,
    Equiv.symm_apply_apply]

end duplicateFlagsCircuit

/-- Sort once, flag repeated selected keys, and return flags to original positions. -/
def duplicateFlagsCircuit {r k : ℕ} (key : Fin k → Fin r) (d : ℕ) :
    Circuit signature (BitonicSort.arity d * r) (BitonicSort.arity d) :=
  (duplicateFlagsCircuit.outputs (BitonicSort.arity d)).comp
    ((bitonicUnsortCircuit 1 d).comp
      (((Circuit.id signature (BitonicSort.sortTraceSize d * 2)).parallel
        ((duplicateFlagsCircuit.rows (BitonicSort.arity d)).comp
          (adjacentDuplicateCircuit fun row bit => finProdFinEquiv (row, key bit)))).comp
        (bitonicSortTraceCircuit key d true)))

private theorem eval_duplicateFlagsCircuit {r k : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (x : BitString (BitonicSort.arity d * r)) (i : Fin (BitonicSort.arity d)) :
    let order := fun row : BitString r => toLex (row ∘ key)
    let sorted := BitonicSort.sort order d true (directProductInput x)
    (duplicateFlagsCircuit key d).eval interpretation x i =
      BitonicSort.unrouteSort d (BitonicSort.sortTrace order d true (directProductInput x))
        (fun j (_ : Fin 1) => (adjacentDuplicateCircuit fun row bit =>
          finProdFinEquiv (row, key bit)).eval interpretation (flatten sorted) j) i 0 := by
  dsimp only
  unfold duplicateFlagsCircuit
  rw [Circuit.eval_comp, duplicateFlagsCircuit.eval_outputs,
    Circuit.eval_comp, Circuit.eval_comp, eval_bitonicSortTraceCircuit,
    eval_parallel_pack, eval_bitonicUnsortCircuit, Circuit.eval_comp,
    duplicateFlagsCircuit.eval_rows]

/-- A flag is true exactly when another original record has the same selected key. -/
theorem eval_duplicateFlagsCircuit_iff {r k : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (x : BitString (BitonicSort.arity d * r)) (i : Fin (BitonicSort.arity d)) :
    (duplicateFlagsCircuit key d).eval interpretation x i = true ↔
      ∃ j, j ≠ i ∧ directProductInput x j ∘ key = directProductInput x i ∘ key := by
  let order := fun row : BitString r => toLex (row ∘ key)
  let rows := directProductInput x
  let sorted := BitonicSort.sort order d true rows
  let answers := fun j (_ : Fin 1) => (adjacentDuplicateCircuit fun row bit =>
    finProdFinEquiv (row, key bit)).eval interpretation (flatten sorted) j
  let R := fun (row : BitString r) (answer : BitString 1) =>
    answer 0 = true ↔ ¬ ∃! j, rows j ∘ key = row ∘ key
  have hr : ∀ j, R (sorted j) (answers j) := by
    intro j
    change (adjacentDuplicateCircuit _).eval interpretation (flatten sorted) j = true ↔ _
    rw [eval_adjacentDuplicateCircuit_iff]
    · simp only [flatten, Function.comp_def, Equiv.symm_apply_apply]
      rw [duplicate_iff_not_unique]
      exact not_congr (List.Perm.existsUnique_ofFn_iff (BitonicSort.sort_perm order d true rows)
        (fun row => row ∘ key = sorted j ∘ key))
    · intro a b hab
      simpa only [flatten, order, sorted, Function.comp_def, Equiv.symm_apply_apply,
        le_iff_lt_or_eq] using
        BitonicSort.monotone_sort order d rows hab
  rw [eval_duplicateFlagsCircuit, duplicate_iff_not_unique]
  exact BitonicSort.unrouteSort_rel_sort order d true rows answers R hr i

/-- Exact weighted cost of one sort, shared adjacent tests, OR gates, and flag restoration. -/
theorem cost_program_duplicateFlagsCircuit {r k : ℕ} (key : Fin k → Fin r) (d : ℕ)
    (cost : signature.Op → ℕ) :
    (duplicateFlagsCircuit key d).program.cost cost =
      (bitonicSortTraceCircuit key d true).program.cost cost +
      (adjacentEqualityCircuit fun (row : Fin (BitonicSort.arity d)) bit =>
        finProdFinEquiv (row, key bit)).program.cost cost +
      BitonicSort.arity d * cost .or +
      BitonicSort.sortTraceSize d * (2 * (2 * cost .and + cost .or)) := by
  simp only [duplicateFlagsCircuit, Circuit.cost_program_comp, Circuit.cost_program_parallel,
    Circuit.id, duplicateFlagsCircuit.outputs, duplicateFlagsCircuit.rows,
    Circuit.cost_program_wiring, Nat.zero_add, Nat.add_zero,
    cost_program_adjacentDuplicateCircuit, cost_program_bitonicUnsortCircuit, Nat.mul_one,
    Nat.add_assoc]

/-- Exact total gate count, including empty keys and zero-width records. -/
theorem size_duplicateFlagsCircuit {r k : ℕ} (key : Fin k → Fin r) (d : ℕ) :
    (duplicateFlagsCircuit key d).size =
      BitonicSort.sortTraceSize d * (6 * k + 6 * r + 8) +
      (1 + (BitonicSort.arity d - 1) * (6 * k + 1)) + BitonicSort.arity d := by
  have hc := cost_program_duplicateFlagsCircuit key d (fun _ => 1)
  rw [cost_program_adjacentEqualityCircuit] at hc
  simp only [Program.cost_const, one_mul,
    size_bitonicSortTraceCircuit] at hc
  rw [hc]
  rw [ite_eq_right (by simp [BitonicSort.arity_eq_two_pow])]
  ring

end Cslib.Circuits.Boolean
