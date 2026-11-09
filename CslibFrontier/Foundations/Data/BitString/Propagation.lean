/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic

/-!
# Segmented propagation of Boolean sources

Each position contributes a source bit. A true link carries the previous value forward;
a false link starts a new segment. The value of a prefix is true precisely when it contains
a true source connected to the end by uninterrupted true links. The link at the source itself
is irrelevant, including the first link.

## Main definitions

* `Cslib.BitString.propagate`: the source/link recurrence, initialized with false.
* `Cslib.BitString.keyLinks`: link adjacent equal keys.

## Main results

* `Cslib.BitString.propagate_eq_true_iff`: characterization by a connected true source.
* `Cslib.BitString.propagate_sorted_eq_true_iff`: on sorted keys, the output is the OR of
  the sources in the equal-key run ending at the last processed record.

## References

* Adapted from MassProduction/Nonuniform/{Propagation,SortedPropagation}.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.BitString

/-- The propagated value after processing a prefix, starting with false. -/
def propagate (source link : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | count + 1 => source count || (link count && propagate source link count)

/-- Propagation depends only on the source and link bits in its processed prefix. -/
theorem propagate_congr {source source' link link' : ℕ → Bool} (count : ℕ)
    (hs : ∀ i, i < count → source i = source' i)
    (hl : ∀ i, i < count → link i = link' i) :
    propagate source link count = propagate source' link' count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [propagate, propagate, hs count (by lia), hl count (by lia),
      ih (fun i hi => hs i (by lia)) (fun i hi => hl i (by lia))]

/-- A true value has a true source connected to the end by uninterrupted true links. -/
theorem propagate_eq_true_iff (source link : ℕ → Bool) (count : ℕ) :
    propagate source link count = true ↔
      ∃ start, start < count ∧ source start = true ∧
        ∀ index, start < index → index < count → link index = true := by
  induction count with
  | zero => simp [propagate]
  | succ count ih =>
    simp only [propagate, Bool.or_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro (last | ⟨linked, start, startBefore, starts, links⟩)
      · exact ⟨count, by lia, last, by intro index lower upper; lia⟩
      · refine ⟨start, by lia, starts, ?_⟩
        intro index lower upper
        by_cases atLast : index = count
        · exact atLast ▸ linked
        · exact links index lower (by lia)
    · rintro ⟨start, startBefore, starts, links⟩
      by_cases atLast : start = count
      · exact Or.inl (atLast ▸ starts)
      · exact Or.inr ⟨links count (by lia) (by lia), start, by lia, starts,
          fun index lower upper => links index lower (by lia)⟩

/-- Adjacent records are linked precisely when their keys agree; the first link is false. -/
def keyLinks {κ : Type*} [DecidableEq κ] (key : ℕ → κ) (index : ℕ) : Bool :=
  if index = 0 then false else decide (key (index - 1) = key index)

/-- In a sorted prefix, propagation reports exactly the true sources having the last key.
The prefix may be empty. No uniqueness of sources or keys is required, and no order is
required beyond the prefix. The explicit equality instance retains the caller's executable
equality test when it differs from the one inherited from the order. -/
theorem propagate_sorted_eq_true_iff {κ : Type*} [LinearOrder κ] [DecidableEq κ]
    (key : ℕ → κ) (source : ℕ → Bool) (count : ℕ)
    (sorted : MonotoneOn key (Set.Iio count)) :
    propagate source (keyLinks key) count = true ↔
      ∃ start, start < count ∧ source start = true ∧ key start = key (count - 1) := by
  rw [propagate_eq_true_iff]
  constructor
  · rintro ⟨start, startBefore, starts, links⟩
    have connected : ∀ index, start ≤ index → index < count → key start = key index := by
      intro index after
      induction index, after using Nat.le_induction with
      | base => intro _; rfl
      | succ index after ih =>
        intro before
        have adjacent : key index = key (index + 1) := by
          simpa [keyLinks] using links (index + 1) (by lia) before
        exact (ih (by lia)).trans adjacent
    exact ⟨start, startBefore, starts, connected (count - 1) (by lia) (by lia)⟩
  · rintro ⟨start, startBefore, starts, sameKey⟩
    refine ⟨start, startBefore, starts, ?_⟩
    intro index after before
    have hprev : index - 1 < count := by lia
    have hlast : count - 1 < count := by lia
    have previousLe : key (index - 1) ≤ key index := sorted hprev before (by lia)
    have firstLe : key start ≤ key (index - 1) := sorted startBefore hprev (by lia)
    have lastLe : key index ≤ key (count - 1) := sorted before hlast (by lia)
    have equal : key (index - 1) = key index :=
      le_antisymm previousLe (lastLe.trans (sameKey.symm.le.trans firstLe))
    simp only [keyLinks, ite_eq_right (by lia : index ≠ 0), decide_eq_true_eq]
    exact equal

end Cslib.BitString
