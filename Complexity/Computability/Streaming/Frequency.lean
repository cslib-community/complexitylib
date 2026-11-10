/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.List.Count
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Push

/-!
# Frequency statistics of streams

The frequency of an item `a` in a stream `s : List α` is `s.count a`. The `k`-th **frequency
moment** is `F_k = ∑ₐ (count a s) ^ k` (`Cslib.Streaming.freqMoment`), and the **largest
frequency** is `F∞ = maxₐ count a s` (`Cslib.Streaming.maxFreq`), the statistics studied by Alon,
Matias and Szegedy [AlonMatiasSzegedy1999]. `F₀` is the number of distinct items, `F₁` the length
of the stream, and the items of a stream are distinct exactly when `F∞ ≤ 1`
(`Cslib.Streaming.maxFreq_le_one_iff`).

## Main definitions

* `Cslib.Streaming.freqMoment`: the frequency moments `F_k` of a stream.
* `Cslib.Streaming.maxFreq`: the largest frequency `F∞` of a stream.

## Main results

* `Cslib.Streaming.freqMoment_zero`: `F₀` is the number of distinct items.
* `Cslib.Streaming.freqMoment_map`: renaming the items injectively keeps the frequency moments.
* `Cslib.Streaming.freqMoment_eq_sum_of_subset`, `Cslib.Streaming.freqMoment_cons_add`,
  `Cslib.Streaming.freqMoment_pos`: for `k ≠ 0`, `F_k` sums over any set containing the items, and
  prepending an item `a` replaces the term `(count a s) ^ k` by `(count a s + 1) ^ k`.
* `Cslib.Streaming.one_le_maxFreq`, `Cslib.Streaming.two_le_maxFreq_of_not_nodup`,
  `Cslib.Streaming.maxFreq_le_one_iff`: `F∞` is at least `1` on nonempty streams, and at most `1`
  exactly on streams of distinct items.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*][AlonMatiasSzegedy1999]
-/

public section

namespace Cslib.Streaming

variable {α : Type*} [DecidableEq α]

/-- The `k`-th **frequency moment** `F_k = ∑ₐ (count a s) ^ k` of a stream. -/
@[expose] def freqMoment (k : ℕ) (s : List α) : ℕ :=
  ∑ a ∈ s.toFinset, s.count a ^ k

/-- `F₀` is the number of distinct items of the stream. -/
theorem freqMoment_zero (s : List α) : freqMoment 0 s = s.toFinset.card := by
  rw [freqMoment, Finset.card_eq_sum_ones]
  simp only [pow_zero]

/-- Renaming the items of a stream injectively keeps its frequency moments. -/
theorem freqMoment_map {α' : Type*} [DecidableEq α'] {f : α → α'} (hf : Function.Injective f)
    (k : ℕ) (s : List α) : freqMoment k (s.map f) = freqMoment k s := by
  unfold freqMoment
  have hT : (s.map f).toFinset = s.toFinset.image f := by
    ext b
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  rw [hT, Finset.sum_image fun a _ b _ h => hf h]
  exact Finset.sum_congr rfl fun a _ => by rw [List.count_map_of_injective _ _ hf]

/-- For `k ≠ 0`, `F_k` is the sum of `(count a s) ^ k` over any set of items containing those of
`s`. -/
theorem freqMoment_eq_sum_of_subset {k : ℕ} (hk : k ≠ 0) {s : List α} {T : Finset α}
    (hT : s.toFinset ⊆ T) : freqMoment k s = ∑ a ∈ T, s.count a ^ k := by
  unfold freqMoment
  refine Finset.sum_subset hT fun a _ ha => ?_
  rw [List.mem_toFinset, ← List.count_eq_zero] at ha
  rw [ha, Nat.zero_pow (Nat.pos_of_ne_zero hk)]

/-- Prepending an item `a` to the stream replaces the term `(count a s) ^ k` of `F_k` by
`(count a s + 1) ^ k`, for `k ≠ 0`. -/
theorem freqMoment_cons_add {k : ℕ} (hk : k ≠ 0) (a : α) (s : List α) :
    freqMoment k (a :: s) + s.count a ^ k = freqMoment k s + (s.count a + 1) ^ k := by
  have hT : s.toFinset ⊆ insert a s.toFinset := Finset.subset_insert _ _
  have hT' : (a :: s).toFinset ⊆ insert a s.toFinset := by rw [List.toFinset_cons]
  rw [freqMoment_eq_sum_of_subset hk hT, freqMoment_eq_sum_of_subset hk hT',
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self a _),
    ← Finset.add_sum_erase _ _ (Finset.mem_insert_self a _), List.count_cons_self,
    Finset.sum_congr rfl fun x hx =>
      by rw [List.count_cons_of_ne (Finset.ne_of_mem_erase hx).symm]]
  omega

/-- The frequency moments of a nonempty stream are positive. -/
theorem freqMoment_pos (k : ℕ) {s : List α} (hs : s ≠ []) : 0 < freqMoment k s := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil s hs
  exact Finset.sum_pos (fun b hb => Nat.pow_pos (List.count_pos_iff.2 (List.mem_toFinset.1 hb)))
    ⟨a, List.mem_toFinset.2 ha⟩

/-- The largest number of occurrences of an item in the stream `s` (`F∞`; zero for the empty
stream). -/
@[expose] def maxFreq (s : List α) : ℕ :=
  s.toFinset.sup fun a => s.count a

theorem maxFreq_le_one_of_nodup {s : List α} (hs : s.Nodup) : maxFreq s ≤ 1 :=
  Finset.sup_le fun a _ => List.nodup_iff_count_le_one.1 hs a

theorem one_le_maxFreq {s : List α} (hs : s ≠ []) : 1 ≤ maxFreq s := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil s hs
  exact (List.count_pos_iff.2 ha).trans_le (Finset.le_sup (f := fun a => s.count a)
    (List.mem_toFinset.2 ha))

theorem two_le_maxFreq_of_not_nodup {s : List α} (hs : ¬s.Nodup) : 2 ≤ maxFreq s := by
  rw [List.nodup_iff_count_le_one] at hs
  push Not at hs
  obtain ⟨a, ha⟩ := hs
  have hmem : a ∈ s := List.count_pos_iff.1 (by omega)
  exact ha.trans_le (Finset.le_sup (f := fun a => s.count a) (List.mem_toFinset.2 hmem))

/-- The items of a stream are distinct exactly when no item occurs twice. -/
theorem maxFreq_le_one_iff {s : List α} : maxFreq s ≤ 1 ↔ s.Nodup :=
  ⟨fun h => by_contra fun hs => absurd (two_le_maxFreq_of_not_nodup hs) (by omega),
    maxFreq_le_one_of_nodup⟩

end Cslib.Streaming
