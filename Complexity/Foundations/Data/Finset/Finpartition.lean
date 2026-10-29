/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Order/Partition/Finpartition.lean`)

public import Complexity.Init
public import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting set partitions of a finset

A finset `s` in a linear order has at most `#s ^ #s` set partitions
(`Fintype.card_finpartition_le`): a set partition is determined by the map sending each element of
`s` to the largest element of its part.

## Main results

* `Fintype.card_finpartition_le`: `Fintype.card (Finpartition s) ≤ #s ^ #s`.

## References

The bound is standard and its proof is original. The Bell number `B_n` counts the set partitions
of an `n`-element set; the bound here is the crude `B_n ≤ n ^ n`.
-/

@[expose] public section

open Finset

namespace Finpartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- The largest element of the part of `x`, as an element of `s`. -/
private def partMax (P : Finpartition s) (x : s) : s :=
  ⟨(P.part x).max' (P.part_nonempty.2 x.2), P.part_subset x (max'_mem _ _)⟩

/-- Two set partitions of `s` whose parts have the same largest element at every point of `s` have
the same part at every point. -/
private theorem mem_part_of_partMax_eq {P P' : Finpartition s} (h : partMax P = partMax P')
    {x y : α} (hx : x ∈ s) (hy : y ∈ P.part x) : y ∈ P'.part x := by
  have hyS : y ∈ s := P.part_subset x hy
  have hPy : P.part y = P.part x := P.part_eq_of_mem (P.part_mem.2 hx) hy
  have hmax (z : α) (hz : z ∈ s) : (P'.part z).max' (P'.part_nonempty.2 hz) =
      (P.part z).max' (P.part_nonempty.2 hz) :=
    congrArg Subtype.val (congrFun h ⟨z, hz⟩).symm
  have h₁ : (P.part x).max' (P.part_nonempty.2 hx) ∈ P'.part x := by
    rw [← hmax x hx]
    exact max'_mem _ _
  have h₂ : (P.part x).max' (P.part_nonempty.2 hx) ∈ P'.part y := by
    have ha : (P.part y).max' (P.part_nonempty.2 hyS) =
        (P.part x).max' (P.part_nonempty.2 hx) := by
      congr 1
    rw [← ha, ← hmax y hyS]
    exact max'_mem _ _
  rw [← P'.eq_of_mem_parts (P'.part_mem.2 hyS) (P'.part_mem.2 hx) h₂ h₁]
  exact P'.mem_part_self.2 hyS

end Finpartition

namespace Fintype

open Finpartition

/-- **The number of set partitions** (standard bound, proof original): a finset `s` in a linear
order has at most `#s ^ #s` set partitions. A set partition is determined by the largest element of
the part of each point. -/
theorem card_finpartition_le {α : Type*} [LinearOrder α] (s : Finset α) :
    Fintype.card (Finpartition s) ≤ #s ^ #s := by
  have hinj : Function.Injective (partMax (s := s)) := by
    intro P P' h
    have hpart (x : α) : P.part x = P'.part x := by
      by_cases hx : x ∈ s
      · ext y
        exact ⟨mem_part_of_partMax_eq h hx, mem_part_of_partMax_eq h.symm hx⟩
      · rw [P.part_eq_empty.2 hx, P'.part_eq_empty.2 hx]
    ext t
    constructor
    · intro ht
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
      rw [← P.part_eq_of_mem ht hx, hpart]
      exact P'.part_mem.2 (P.le ht hx)
    · intro ht
      obtain ⟨x, hx⟩ := P'.nonempty_of_mem_parts ht
      rw [← P'.part_eq_of_mem ht hx, ← hpart]
      exact P.part_mem.2 (P'.le ht hx)
  refine (Fintype.card_le_of_injective _ hinj).trans_eq ?_
  rw [Fintype.card_fun, Fintype.card_coe]

end Fintype
