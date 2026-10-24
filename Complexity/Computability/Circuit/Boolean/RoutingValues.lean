/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Broadcast
public import Complexity.Computability.Circuit.Boolean.SortingTrace
import Complexity.Algorithms.Lean.Sort.Bitonic.Correctness
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Batched routing with one sort and saved swaps

Sort by matching key and source/destination tag, broadcast source values along equal-key runs,
then reverse the saved swaps on the values alone. Every destination receives its answer at its
original input position. Neither request identifiers nor unique restoration keys are needed.
False tags designate sources; true tags designate destinations. Multiple matching sources
contribute their bitwise OR. A unique matching source is copied exactly.

The circuit returns value fields only. Header bits can be retained directly from the input by
free wiring; they need not travel through the reverse circuit. Source-position outputs retain
the broadcast's prefix accumulations, so destination correctness is a relational invariant,
not a pointwise description of the entire broadcast.

All gate costs are charged, including constants and negations. Saved controls include their
complements. Gate counts do not certify construction runtime or retained storage.

## Main definitions

* `Cslib.Circuits.Boolean.routeValuesCircuit.answerWiring`,
  `Cslib.Circuits.Boolean.routeValuesCircuit.matchingSelector`: value extraction wiring and sort
  key selector for batched routing.
* `Cslib.Circuits.Boolean.routeValuesCircuit`: one sort, shared broadcast, and reverse routing.

## Main results

* `Cslib.Circuits.Boolean.eval_routeValuesCircuit_value_eq_true_iff`: destination OR semantics at
  the original input position.
* `Cslib.Circuits.Boolean.eval_routeValuesCircuit_of_unique_source`: exact source copying.
* `Cslib.Circuits.Boolean.cost_program_routeValuesCircuit`: exact arbitrary weighted gate cost.
* `Cslib.Circuits.Boolean.size_routeValuesCircuit`: exact total gate count.

## References

Simplifies the batched routing construction in
[S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
using the saved decisions of
[K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open bitonicSortTraceCircuit broadcastCircuit

namespace routeValuesCircuit

/-- Select the value field of each record, retaining row-major order. -/
def answerWiring (n h width : ℕ) :
    Circuit signature (n * (h + width)) (n * width) :=
  Circuit.wiring signature fun i =>
    let jb := finProdFinEquiv.symm i
    finProdFinEquiv (jb.1, Fin.natAdd h jb.2)

private theorem eval_answerWiring (n h width : ℕ) (x : BitString (n * (h + width))) :
    directProductInput ((answerWiring n h width).eval interpretation x) = value x := by
  funext j bit
  simp only [answerWiring, Circuit.eval_wiring, directProductInput, Function.comp_apply,
    Equiv.symm_apply_apply, value]

/-- Select matching keys followed by their source/destination tag. -/
def matchingSelector {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (width : ℕ) :
    Fin (k + 1) → Fin (h + width) :=
  Fin.snoc (Fin.castAdd width ∘ key) (Fin.castAdd width tag)

end routeValuesCircuit

open routeValuesCircuit

/-- Sort once, broadcast matching source values, and undo saved swaps on the value fields. -/
def routeValuesCircuit {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (d width : ℕ) :
    Circuit signature (BitonicSort.arity d * (h + width)) (BitonicSort.arity d * width) :=
  (bitonicUnsortCircuit width d).comp
    (((Circuit.id signature (BitonicSort.sortTraceSize d * 2)).parallel
      ((answerWiring (BitonicSort.arity d) h width).comp
        (broadcastCircuit key tag (BitonicSort.arity d) width))).comp
      (bitonicSortTraceCircuit (matchingSelector key tag width) d true))

private theorem eval_routeValuesCircuit {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (d width : ℕ)
    (x : BitString (BitonicSort.arity d * (h + width))) :
    let order := fun row : BitString (h + width) => toLex (row ∘ matchingSelector key tag width)
    let sorted := BitonicSort.sort order d true (directProductInput x)
    directProductInput ((routeValuesCircuit key tag d width).eval interpretation x) =
      BitonicSort.unrouteSort d (BitonicSort.sortTrace order d true (directProductInput x))
        (value ((broadcastCircuit key tag (BitonicSort.arity d) width).eval interpretation
          (flatten sorted))) := by
  dsimp only
  rw [routeValuesCircuit, Circuit.eval_comp, Circuit.eval_comp, eval_bitonicSortTraceCircuit,
    eval_parallel_pack, eval_bitonicUnsortCircuit, Circuit.eval_comp, eval_answerWiring]

/-- Exact weighted cost: one traced sort, shared broadcast, and reversal of the values only. -/
theorem cost_program_routeValuesCircuit {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (d width : ℕ)
    (cost : signature.Op → ℕ) :
    (routeValuesCircuit key tag d width).program.cost cost =
      (bitonicSortTraceCircuit (matchingSelector key tag width) d true).program.cost cost +
      (broadcastCircuit key tag (BitonicSort.arity d) width).program.cost cost +
      BitonicSort.sortTraceSize d * (2 * width * (2 * cost .and + cost .or)) := by
  simp only [routeValuesCircuit, Circuit.cost_program_comp, Circuit.cost_program_parallel,
    Circuit.id, answerWiring, Circuit.cost_program_wiring, Nat.zero_add, Nat.add_zero,
    cost_program_bitonicUnsortCircuit]

/-- Each original destination receives the OR of matching original sources. Requests may repeat;
no restoration keys, identifiers, rank calculations or source uniqueness are needed. -/
theorem eval_routeValuesCircuit_value_eq_true_iff {h k d width : ℕ}
    (key : Fin k → Fin h) (tag : Fin h)
    (x : BitString (BitonicSort.arity d * (h + width)))
    (destination : Fin (BitonicSort.arity d)) (hdestination : header x destination tag = true)
    (bit : Fin width) :
    directProductInput ((routeValuesCircuit key tag d width).eval interpretation x)
      destination bit = true ↔ ∃ source, header x source ∘ key = header x destination ∘ key ∧
        header x source tag = false ∧ value x source bit = true := by
  classical
  let order := fun row : BitString (h + width) => toLex (row ∘ matchingSelector key tag width)
  let rows := directProductInput x
  let sorted := BitonicSort.sort order d true rows
  let y := flatten sorted
  let answers := value
    ((broadcastCircuit key tag (BitonicSort.arity d) width).eval interpretation y)
  let R := fun (row : BitString (h + width)) (answer : BitString width) =>
    row (Fin.castAdd width tag) = true → (answer bit = true ↔
      ∃ source, header x source ∘ key = (row ∘ Fin.castAdd width) ∘ key ∧
        header x source tag = false ∧ value x source bit = true)
  have hs : Monotone (fun record =>
      toLex (Fin.snoc (α := fun _ => Bool) (header y record ∘ key) (header y record tag))) := by
    have he (i : Fin (BitonicSort.arity d)) :
        toLex (Fin.snoc (α := fun _ => Bool) (header y i ∘ key) (header y i tag)) =
          order (sorted i) := by
      simp only [header, y, directProductInput_flatten, order, matchingSelector,
        Fin.comp_snoc, Function.comp_assoc, Function.comp_apply]
    intro a b hab
    calc
      _ = order (sorted a) := he a
      _ ≤ order (sorted b) := BitonicSort.monotone_sort order d rows hab
      _ = _ := (he b).symm
  have hr : ∀ i, R (sorted i) (answers i) := by
    intro i hi
    have ht : header y i tag = true := by
      simpa only [header, y, directProductInput_flatten, Function.comp_apply] using hi
    change answers i bit = true ↔ _
    rw [show answers i bit =
      value ((broadcastCircuit key tag (BitonicSort.arity d) width).eval interpretation y) i bit
        from rfl,
      eval_broadcastCircuit_value_eq_true_iff key tag y hs i ht bit]
    simpa only [header, value, y, directProductInput_flatten, Function.comp_apply] using
      List.Perm.exists_ofFn_iff (BitonicSort.sort_perm order d true rows)
        (fun row : BitString (h + width) =>
          (row ∘ Fin.castAdd width) ∘ key = (sorted i ∘ Fin.castAdd width) ∘ key ∧
            row (Fin.castAdd width tag) = false ∧ row (Fin.natAdd h bit) = true)
  rw [eval_routeValuesCircuit]
  exact BitonicSort.unrouteSort_rel_sort order d true rows answers R hr destination hdestination

/-- Exact gate count for routing values back to the original record positions. -/
theorem size_routeValuesCircuit {h k : ℕ} (key : Fin k → Fin h) (tag : Fin h) (d width : ℕ) :
    (routeValuesCircuit key tag d width).size =
      BitonicSort.sortTraceSize d * (6 * (k + 1) + 6 * h + 12 * width + 2) +
      (broadcastCircuit key tag (BitonicSort.arity d) width).size := by
  have hc := cost_program_routeValuesCircuit key tag d width (fun _ => 1)
  simp only [Program.cost_const, one_mul, size_bitonicSortTraceCircuit] at hc
  rw [hc]
  ring

/-- A destination receives its unique matching source at its literal original input position. -/
theorem eval_routeValuesCircuit_of_unique_source {h k d width : ℕ}
    (key : Fin k → Fin h) (tag : Fin h)
    (x : BitString (BitonicSort.arity d * (h + width)))
    (source destination : Fin (BitonicSort.arity d))
    (hkey : header x source ∘ key = header x destination ∘ key)
    (hsource : header x source tag = false) (hdestination : header x destination tag = true)
    (unique : ∀ i, header x i ∘ key = header x source ∘ key → header x i tag = false → i = source) :
    directProductInput ((routeValuesCircuit key tag d width).eval interpretation x) destination =
      value x source := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  rw [eval_routeValuesCircuit_value_eq_true_iff key tag x destination hdestination bit]
  constructor
  · rintro ⟨i, hi, ht, hv⟩
    exact unique i (hi.trans hkey.symm) ht ▸ hv
  · intro hv
    exact ⟨source, hkey, hsource, hv⟩

end Cslib.Circuits.Boolean
