/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.BinPacking.Basic
public import Complexity.Computability.Complexity.Problems.Partition
public import Mathlib.Basic.Real.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Bin packing is NP-hard to approximate within a factor below 3/2

A polynomial-time algorithm for bin packing that always uses fewer than `3/2` times the optimal
number of bins decides `Partition`, so it gives `P = NP`
[Williamson and Shmoys, Theorem 3.8][WilliamsonShmoys2011]. Given a list `l` with total `S`,
pack it into bins of capacity `⌊S / 2⌋`. If `l` has a partition, two bins suffice, so the
algorithm uses at most two bins; conversely two bins of capacity `⌊S / 2⌋` holding `S` hold
exactly `S / 2` each, and either is one side of a partition. Lists with a number larger than
`⌊S / 2⌋` have no partition, and the empty list and lists of zeros always have one.

The algorithm is a function `A : List ℕ × ℕ → List (List ℕ)` from items and capacity to bins,
with the numbers in binary (`BinPacking.encBinPacking` and `BinPacking.encBins`). It is required
to return a packing only when one exists, that is when every item fits into a bin
(`Cslib.Algorithms.Lean.BinPacking.exists_isPacking_iff`), and its ratio is compared with every
packing of a nonempty list.

## Main results

* `Cslib.Complexity.BinPacking.decidePartition_iff`: the decider built from the algorithm decides
  `Partition`.
* `Cslib.Complexity.P_eq_NP_of_binPacking_approx`: an algorithm with `2 * |A| < 3 * |Q|` for
  every packing `Q` gives `P = NP`.
* `Cslib.Complexity.P_eq_NP_of_binPacking_ratio`: an algorithm with ratio `ρ < 3/2` gives
  `P = NP`.

## References

* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Algorithms.Lean.BinPacking
open scoped List

namespace BinPacking

/-- A bin-packing instance `(l, C)`, all numbers in binary: the item sizes `l` as a framed list of
framed entries, followed by the capacity `C`, unframed. -/
abbrev encBinPacking : List ℕ × ℕ ↪ List Bool := encPair (encList encNat) encNat

/-- A list of bins, such as the packing an algorithm returns: the concatenation of the framed bins,
each the concatenation of its framed item sizes in binary. This is the layout
`encList (encList encNat)` that other modules name by their own roles, such as
`Cslib.Complexity.KCenter.encDistMatrix`; the name records the role. -/
abbrev encBins : List (List ℕ) ↪ List Bool := encList (encList encNat)

/-- The decider for `Partition` built from a bin-packing algorithm `A`: accept lists summing to
zero, and otherwise accept when every number fits into a bin of capacity `⌊S / 2⌋` and `A` packs
the list into at most two such bins. -/
def decidePartition (A : List ℕ × ℕ → List (List ℕ)) (l : List ℕ) : Bool :=
  decide (l.sum = 0) ||
    (l.all fun a => decide (a ≤ l.sum / 2)) && decide ((A (l, l.sum / 2)).length ≤ 2)

/-- **The decider is correct**: an algorithm that returns packings and uses fewer than `3/2` times
as many bins as any packing of a nonempty list decides `Partition`. -/
theorem decidePartition_iff {A : List ℕ × ℕ → List (List ℕ)}
    (hvalid : ∀ l C, (∀ a ∈ l, a ≤ C) → IsPacking C l (A (l, C)))
    (hratio : ∀ l C Q, l ≠ [] → IsPacking C l Q → 2 * (A (l, C)).length < 3 * Q.length)
    (l : List ℕ) : decidePartition A l = true ↔ l ∈ Partition := by
  simp only [decidePartition, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  constructor
  · rintro (h0 | ⟨hle, hlen⟩)
    · exact mem_Partition_iff.2 ⟨0, Multiset.zero_le _, by simp [h0]⟩
    · obtain ⟨hpack, hsum⟩ := hvalid l (l.sum / 2) hle
      have htot := (IsPacking.mk hpack hsum).sum_eq
      match hA : A (l, l.sum / 2), hlen with
      | [], _ =>
        rw [hA] at htot
        exact mem_Partition_iff.2 ⟨0, Multiset.zero_le _, by simp_all⟩
      | [b], _ =>
        rw [hA] at htot hsum
        have := hsum b List.mem_cons_self
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at htot
        exact mem_Partition_iff.2 ⟨0, Multiset.zero_le _, by simp only [Multiset.sum_zero]; omega⟩
      | [b, b'], _ =>
        rw [hA] at htot hsum hpack
        have h1 := hsum b List.mem_cons_self
        have h2 := hsum b' (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at htot
        refine mem_Partition_iff.2 ⟨b, ?_, by rw [Multiset.sum_coe]; omega⟩
        have hsub : b.Subperm l :=
          (List.sublist_append_left b b').subperm.trans
            (by simpa using hpack.subperm)
        exact Multiset.coe_le.2 hsub
  · intro h
    by_cases h0 : l.sum = 0
    · exact Or.inl h0
    right
    obtain ⟨s, hs, hsum⟩ := mem_Partition_iff_sublist.1 h
    obtain ⟨t, ht⟩ := hs.exists_perm_append
    have htsum := ht.sum_eq
    rw [List.sum_append] at htsum
    have hle : ∀ a ∈ l, a ≤ l.sum / 2 := by
      intro a ha
      rcases List.mem_append.1 (ht.mem_iff.1 ha) with ha | ha
      · have := List.le_sum_of_mem ha
        omega
      · have := List.le_sum_of_mem ha
        omega
    have hQ : IsPacking (l.sum / 2) l [s, t] :=
      ⟨by simpa using ht.symm, by
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> omega⟩
    have hne : l ≠ [] := by rintro rfl; exact h0 rfl
    have := hratio l (l.sum / 2) [s, t] hne hQ
    simp only [List.length_cons, List.length_nil] at this
    exact ⟨hle, by omega⟩

/-- The decider built from a polynomial-time algorithm is polynomial-time. -/
theorem computableInPolyTime_decidePartition {A : List ℕ × ℕ → List (List ℕ)}
    (hA : ComputableInPolyTime A encBinPacking encBins) :
    ComputableInPolyTime (decidePartition A) (encList encNat) encBool := by
  unfold decidePartition
  fun_prop

end BinPacking

/-- **Bin packing is NP-hard to approximate within a factor below `3/2`**
[Williamson and Shmoys, Theorem 3.8][WilliamsonShmoys2011]. A polynomial-time algorithm that
returns a packing whenever every item fits into a bin, and on nonempty lists uses fewer than `3/2`
times as many bins as any packing, gives `P = NP`. -/
theorem P_eq_NP_of_binPacking_approx {A : List ℕ × ℕ → List (List ℕ)}
    (hA : ComputableInPolyTime A BinPacking.encBinPacking BinPacking.encBins)
    (hvalid : ∀ l C, (∀ a ∈ l, a ≤ C) → IsPacking C l (A (l, C)))
    (hratio : ∀ l C Q, l ≠ [] → IsPacking C l Q → 2 * (A (l, C)).length < 3 * Q.length)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  Partition_npComplete.P_eq_NP_of_mem_P
    ⟨_, BinPacking.computableInPolyTime_decidePartition hA,
      fun l => (BinPacking.decidePartition_iff hvalid hratio l).symm⟩ enc

/-- **No `ρ`-approximation for bin packing with `ρ < 3/2` unless `P = NP`**
[Williamson and Shmoys, Theorem 3.8][WilliamsonShmoys2011]: a polynomial-time algorithm that
returns a packing whenever every item fits into a bin, and on nonempty lists uses at most `ρ`
times as many bins as any packing, gives `P = NP`. -/
theorem P_eq_NP_of_binPacking_ratio {A : List ℕ × ℕ → List (List ℕ)} {ρ : ℝ} (hρ : ρ < 3 / 2)
    (hA : ComputableInPolyTime A BinPacking.encBinPacking BinPacking.encBins)
    (hvalid : ∀ l C, (∀ a ∈ l, a ≤ C) → IsPacking C l (A (l, C)))
    (hratio : ∀ l C Q, l ≠ [] → IsPacking C l Q → ((A (l, C)).length : ℝ) ≤ ρ * Q.length)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc := by
  refine P_eq_NP_of_binPacking_approx hA hvalid (fun l C Q hl hQ => ?_) enc
  have h := hratio l C Q hl hQ
  have hQ0 : (0 : ℝ) < Q.length := by
    exact_mod_cast List.length_pos_iff.2 (hQ.ne_nil hl)
  have : (2 * (A (l, C)).length : ℝ) < 3 * Q.length := by nlinarith
  exact_mod_cast this

end Cslib.Complexity
