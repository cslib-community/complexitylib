/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Sort.Bitonic.Basic
import Cslib.Foundations.Data.Fin.Tuple
import Mathlib.Tactic.Ring

/-!
# Replaying and reversing bitonic sorting decisions

Record one Boolean for each comparison in the existing bitonic algorithm. These decisions
route arbitrary payloads and can be replayed in reverse to recover their original positions.
In particular, a pointwise transformation of sorted records can be restored without sorting
again or attaching unique identifiers. Equal keys need no special hypothesis: the trace records
this sorter's actual choices, including the reversal of descending ties.

The trace definitions specify the decisions; they are not an optimized implementation of
sorting with a trace. Circuit realizations must share comparisons and account for retained
controls separately. The exact trace lengths below count Boolean decisions, not execution time.

## Main definitions

* `Cslib.BitonicSort.mergeTrace`, `Cslib.BitonicSort.sortTrace`: record comparison decisions.
* `Cslib.BitonicSort.routeSort`: replay saved decisions on arbitrary payloads.
* `Cslib.BitonicSort.unrouteSort`: reverse those decisions.

## Main results

* `Cslib.BitonicSort.unrouteSort_routeSort`, `Cslib.BitonicSort.routeSort_unrouteSort`:
  replay and reversal are mutually inverse for every trace, even one not obtained by sorting.
* `Cslib.BitonicSort.routeSort_sortTrace`: replay agrees with the existing bitonic algorithm.
* `Cslib.BitonicSort.unrouteSort_comp_sort`: restore pointwise transformed sorted records.
* `Cslib.BitonicSort.four_mul_sortTraceSize`: exact number of retained comparison decisions.

## References

* [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.BitonicSort

variable {α β κ : Type*}

/-- Exchange corresponding entries between two halves according to saved flags. -/
def routeLayer {n : ℕ} (flags : Fin n → Bool) (x : Fin (n + n) → α) : Fin (n + n) → α :=
  Fin.append
    (fun i => if flags i then x (Fin.natAdd n i) else x (Fin.castAdd n i))
    (fun i => if flags i then x (Fin.castAdd n i) else x (Fin.natAdd n i))

/-- A layer's flags route any payload back when applied twice. -/
@[simp] theorem routeLayer_routeLayer {n : ℕ} (flags : Fin n → Bool)
    (x : Fin (n + n) → α) : routeLayer flags (routeLayer flags x) = x := by
  funext i
  cases i using Fin.addCases <;> simp only [routeLayer, Fin.append_left, Fin.append_right] <;>
    split_ifs <;> rfl

/-- The comparison flags used by the existing ascending or descending layer. -/
def layerFlags [LinearOrder κ] (key : α → κ) {n : ℕ} (ascending : Bool)
    (x : Fin (n + n) → α) : Fin n → Bool :=
  fun i => decide (if ascending then key (x (Fin.natAdd n i)) < key (x (Fin.castAdd n i))
    else ¬key (x (Fin.natAdd n i)) < key (x (Fin.castAdd n i)))

private theorem routeLayer_layerFlags [LinearOrder κ] (key : α → κ) {n : ℕ}
    (ascending : Bool) (x : Fin (n + n) → α) :
    routeLayer (layerFlags key ascending x) x = compareLayer key ascending x := by
  funext i
  cases i using Fin.addCases <;>
    simp only [routeLayer, layerFlags, compareLayer, compareLayer.source, Function.comp_apply,
      Fin.append_left, Fin.append_right, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq]
  all_goals split_ifs <;> rfl

/-- Number of decisions retained by bitonic merge. -/
def mergeTraceSize : ℕ → ℕ
  | 0 => 0
  | d + 1 => arity d + (mergeTraceSize d + mergeTraceSize d)

/-- Number of decisions retained by bitonic sorting. -/
def sortTraceSize : ℕ → ℕ
  | 0 => 0
  | d + 1 => (sortTraceSize d + sortTraceSize d) + mergeTraceSize (d + 1)

/-- Extract merge controls in the order: current layer, left child, right child. -/
def mergeTrace [LinearOrder κ] (key : α → κ) : (d : ℕ) → Bool →
    (Fin (arity d) → α) → Fin (mergeTraceSize d) → Bool
  | 0, _, _ => Fin.elim0
  | d + 1, ascending, x =>
    let compared := compareLayer key ascending x
    Fin.append (layerFlags key ascending x) (Fin.append
      (mergeTrace key d ascending (compared ∘ Fin.castAdd (arity d)))
      (mergeTrace key d ascending (compared ∘ Fin.natAdd (arity d))))

/-- Extract sort controls in the order: left sort, right sort, final merge. -/
def sortTrace [LinearOrder κ] (key : α → κ) : (d : ℕ) → Bool →
    (Fin (arity d) → α) → Fin (sortTraceSize d) → Bool
  | 0, _, _ => Fin.elim0
  | d + 1, ascending, x =>
    let left := x ∘ Fin.castAdd (arity d)
    let right := x ∘ Fin.natAdd (arity d)
    Fin.append (Fin.append (sortTrace key d true left) (sortTrace key d false right))
      (mergeTrace key (d + 1) ascending
        (Fin.append (sort key d true left) (sort key d false right)))

/-- Route payloads through a merge using its saved decisions, without comparing them. -/
def routeMerge : (d : ℕ) → (Fin (mergeTraceSize d) → Bool) →
    (Fin (arity d) → α) → Fin (arity d) → α
  | 0, _, x => x
  | d + 1, flags, x =>
    let compared := routeLayer (flags ∘ Fin.castAdd (mergeTraceSize d + mergeTraceSize d)) x
    let children := flags ∘ Fin.natAdd (arity d)
    Fin.append
      (routeMerge d (children ∘ Fin.castAdd (mergeTraceSize d)) (compared ∘ Fin.castAdd (arity d)))
      (routeMerge d (children ∘ Fin.natAdd (mergeTraceSize d)) (compared ∘ Fin.natAdd (arity d)))

/-- Reverse a merge by undoing its children before its current layer. -/
def unrouteMerge : (d : ℕ) → (Fin (mergeTraceSize d) → Bool) →
    (Fin (arity d) → α) → Fin (arity d) → α
  | 0, _, x => x
  | d + 1, flags, x =>
    let children := flags ∘ Fin.natAdd (arity d)
    routeLayer (flags ∘ Fin.castAdd (mergeTraceSize d + mergeTraceSize d)) (Fin.append
      (unrouteMerge d (children ∘ Fin.castAdd (mergeTraceSize d)) (x ∘ Fin.castAdd (arity d)))
      (unrouteMerge d (children ∘ Fin.natAdd (mergeTraceSize d)) (x ∘ Fin.natAdd (arity d))))

/-- Route payloads through a sort using its saved decisions. -/
def routeSort : (d : ℕ) → (Fin (sortTraceSize d) → Bool) →
    (Fin (arity d) → α) → Fin (arity d) → α
  | 0, _, x => x
  | d + 1, flags, x =>
    let children := flags ∘ Fin.castAdd (mergeTraceSize (d + 1))
    routeMerge (d + 1) (flags ∘ Fin.natAdd (sortTraceSize d + sortTraceSize d)) (Fin.append
      (routeSort d (children ∘ Fin.castAdd (sortTraceSize d)) (x ∘ Fin.castAdd (arity d)))
      (routeSort d (children ∘ Fin.natAdd (sortTraceSize d)) (x ∘ Fin.natAdd (arity d))))

/-- Reverse the final merge before undoing the two child sorts. -/
def unrouteSort : (d : ℕ) → (Fin (sortTraceSize d) → Bool) →
    (Fin (arity d) → α) → Fin (arity d) → α
  | 0, _, x => x
  | d + 1, flags, x =>
    let merged := unrouteMerge (d + 1) (flags ∘ Fin.natAdd (sortTraceSize d + sortTraceSize d)) x
    let children := flags ∘ Fin.castAdd (mergeTraceSize (d + 1))
    Fin.append
      (unrouteSort d (children ∘ Fin.castAdd (sortTraceSize d)) (merged ∘ Fin.castAdd (arity d)))
      (unrouteSort d (children ∘ Fin.natAdd (sortTraceSize d)) (merged ∘ Fin.natAdd (arity d)))

@[simp] theorem unrouteMerge_routeMerge (d : ℕ) (flags : Fin (mergeTraceSize d) → Bool)
    (x : Fin (arity d) → α) : unrouteMerge d flags (routeMerge d flags x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [mergeTraceSize, arity] at flags x
    simp only [routeMerge, unrouteMerge, arity, mergeTraceSize]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    rw [Fin.append_castAdd_natAdd]
    exact routeLayer_routeLayer _ x

@[simp] theorem routeMerge_unrouteMerge (d : ℕ) (flags : Fin (mergeTraceSize d) → Bool)
    (x : Fin (arity d) → α) : routeMerge d flags (unrouteMerge d flags x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [mergeTraceSize, arity] at flags x
    simp only [routeMerge, unrouteMerge, arity, mergeTraceSize, routeLayer_routeLayer]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    exact Fin.append_castAdd_natAdd

@[simp] theorem unrouteSort_routeSort (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) : unrouteSort d flags (routeSort d flags x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [sortTraceSize, arity] at flags x
    simp only [routeSort, unrouteSort, arity, sortTraceSize]
    erw [unrouteMerge_routeMerge]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    exact Fin.append_castAdd_natAdd

@[simp] theorem routeSort_unrouteSort (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) : routeSort d flags (unrouteSort d flags x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [sortTraceSize, arity] at flags x
    simp only [routeSort, unrouteSort, arity, sortTraceSize]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    erw [Fin.append_castAdd_natAdd, routeMerge_unrouteMerge]

private theorem routeMerge_mergeTrace [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (x : Fin (arity d) → α) :
    routeMerge d (mergeTrace key d ascending x) x = merge key d ascending x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [arity] at x
    simp only [routeMerge, mergeTrace, arity, mergeTraceSize, merge]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right]
    rw [routeLayer_layerFlags]
    simp only [ih]

theorem routeSort_sortTrace [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (x : Fin (arity d) → α) :
    routeSort d (sortTrace key d ascending x) x = sort key d ascending x := by
  induction d generalizing ascending with
  | zero => rfl
  | succ d ih =>
    dsimp only [arity] at x
    simp only [routeSort, sortTrace, arity, sortTraceSize, sort]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    exact routeMerge_mergeTrace _ _ _ _

private theorem unrouteSort_sort [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (x : Fin (arity d) → α) :
    unrouteSort d (sortTrace key d ascending x) (sort key d ascending x) = x := by
  rw [← routeSort_sortTrace, unrouteSort_routeSort]

/-- Moving a payload and then transforming it is the same as transforming before moving. -/
private theorem routeLayer_comp {n : ℕ} (flags : Fin n → Bool) (f : α → β)
    (x : Fin (n + n) → α) : routeLayer flags (f ∘ x) = f ∘ routeLayer flags x := by
  funext i
  cases i using Fin.addCases <;>
    simp only [routeLayer, Function.comp_apply, Fin.append_left, Fin.append_right] <;>
    split_ifs <;> rfl

/-- Saved merge decisions do not inspect the payload. -/
private theorem routeMerge_comp (d : ℕ) (flags : Fin (mergeTraceSize d) → Bool) (f : α → β)
    (x : Fin (arity d) → α) : routeMerge d flags (f ∘ x) = f ∘ routeMerge d flags x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [mergeTraceSize, arity] at flags x
    simp only [routeMerge, arity, mergeTraceSize, routeLayer_comp, Fin.comp_append,
      Function.comp_assoc, ih]

/-- Saved sort decisions do not inspect the payload. -/
theorem routeSort_comp (d : ℕ) (flags : Fin (sortTraceSize d) → Bool) (f : α → β)
    (x : Fin (arity d) → α) : routeSort d flags (f ∘ x) = f ∘ routeSort d flags x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [sortTraceSize, arity] at flags x
    simp only [routeSort, arity, sortTraceSize, Function.comp_assoc, ih]
    erw [← Fin.comp_append, routeMerge_comp]
    rfl

/-- Reverse a sort's saved decisions after a pointwise transformation. Neither keys nor
payloads need be distinct, and the transformed payload may have a different type. -/
theorem unrouteSort_comp_sort [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (f : α → β) (x : Fin (arity d) → α) :
    unrouteSort d (sortTrace key d ascending x) (f ∘ sort key d ascending x) = f ∘ x := by
  rw [← routeSort_sortTrace, ← routeSort_comp, unrouteSort_routeSort]

/-- Reversing saved decisions commutes with arbitrary pointwise transformations. -/
theorem unrouteSort_comp (d : ℕ) (flags : Fin (sortTraceSize d) → Bool) (f : α → β)
    (x : Fin (arity d) → α) : unrouteSort d flags (f ∘ x) = f ∘ unrouteSort d flags x := by
  apply Function.LeftInverse.injective (unrouteSort_routeSort d flags)
  rw [routeSort_unrouteSort, routeSort_comp, routeSort_unrouteSort]

/-- Reversal reads the same original position for every payload type. This is deliberately
not a simp lemma: rewriting the identity payload would expand the right-hand side again. -/
theorem unrouteSort_apply (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) (i : Fin (arity d)) :
    unrouteSort d flags x i = x (unrouteSort d flags id i) := by
  simpa only [Function.comp_id, Function.comp_apply] using
    congrFun (unrouteSort_comp d flags x id) i

/-- Pointwise relations between two payload arrays survive reversal by the same saved trace. -/
theorem unrouteSort_rel (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) (y : Fin (arity d) → β) (R : α → β → Prop)
    (h : ∀ i, R (x i) (y i)) (i : Fin (arity d)) :
    R (unrouteSort d flags x i) (unrouteSort d flags y i) := by
  rw [unrouteSort_apply d flags x i, unrouteSort_apply d flags y i]
  exact h _

/-- Transfer specifications from sorted positions to literal original positions. -/
theorem unrouteSort_rel_sort [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (x : Fin (arity d) → α) (y : Fin (arity d) → β)
    (R : α → β → Prop) (h : ∀ i, R (sort key d ascending x i) (y i))
    (i : Fin (arity d)) :
    R (x i) (unrouteSort d (sortTrace key d ascending x) y i) := by
  simpa only [unrouteSort_sort] using
    unrouteSort_rel d (sortTrace key d ascending x) (sort key d ascending x) y R h i

/-- A merge retains one decision for each comparator, or `d * 2^d / 2` decisions. -/
theorem two_mul_mergeTraceSize (d : ℕ) : 2 * mergeTraceSize d = d * 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    calc
      2 * mergeTraceSize (d + 1) = 2 * 2 ^ d + 2 * (2 * mergeTraceSize d) := by
        rw [mergeTraceSize, arity_eq_two_pow]
        ring
      _ = (d + 1) * 2 ^ (d + 1) := by rw [ih, pow_succ]; ring

/-- A sort retains `d * (d + 1) * 2^d / 4` decisions. -/
theorem four_mul_sortTraceSize (d : ℕ) :
    4 * sortTraceSize d = d * (d + 1) * 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    calc
      4 * sortTraceSize (d + 1) =
          2 * (4 * sortTraceSize d) + 2 * (2 * mergeTraceSize (d + 1)) := by
        rw [sortTraceSize]
        ring
      _ = (d + 1) * (d + 1 + 1) * 2 ^ (d + 1) := by
        rw [ih, two_mul_mergeTraceSize, pow_succ]
        ring

end Cslib.BitonicSort
