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
