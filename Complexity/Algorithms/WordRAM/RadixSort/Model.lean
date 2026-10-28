/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Sort

/-!
# Stable binary radix sorting: mathematical specification

The order is the unsigned order on encoded words. In particular this does not claim that
sign-and-magnitude integer encodings are ordered as integers. The construction and proofs here
are original; the executable native program is supplied separately.

## Main definitions

* `digit`: one binary digit, represented as zero or one.
* `select`: the stable subsequence with a specified digit.
* `partition`: zeros followed by ones, preserving the order within each part.
* `passes`: least-significant-digit radix passes.

## Main results

* `partition_perm`: a pass preserves the multiset.
* `passes_correct`: sufficiently many passes give a sorted permutation.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.RadixSort

/-- Binary digit `b` of unsigned word `v`. -/
def digit (b v : ℕ) : ℕ := v / 2 ^ b % 2

/-- The stable subsequence of words whose digit `b` equals `t`. -/
def select (b t : ℕ) (xs : List ℕ) : List ℕ :=
  xs.filter (fun v => decide (digit b v = t))

/-- Stable zero/one partition at digit `b`. -/
def partition (b : ℕ) (xs : List ℕ) : List ℕ := select b 0 xs ++ select b 1 xs

/-- Apply the first `bits` binary radix passes, starting with the least significant bit. -/
def passes : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | b + 1, xs => partition b (passes b xs)

/-- Every binary digit is below two. -/
theorem digit_lt_two (b v : ℕ) : digit b v < 2 := Nat.mod_lt _ (by decide)

/-- The native shift/remainder implementation reads precisely `digit`. -/
theorem digit_eq_shift (b v : ℕ) : digit b v = (v >>> b) % 2 := by
  rw [Nat.shiftRight_eq_div_pow, digit]

/-- A selection never increases the length. -/
theorem length_select_le (b t : ℕ) (xs : List ℕ) : (select b t xs).length ≤ xs.length :=
  List.length_filter_le _ _

/-- A selected word occurred in the original list and has the requested digit. -/
theorem mem_select {b t v : ℕ} {xs : List ℕ} :
    v ∈ select b t xs ↔ v ∈ xs ∧ digit b v = t := by
  simp [select]

/-- Appending an input word appends it to precisely its selected subsequence. -/
theorem select_append (b t : ℕ) (xs ys : List ℕ) :
    select b t (xs ++ ys) = select b t xs ++ select b t ys := by
  simp [select]

/-- A stable bit partition is a permutation of the input, including repeated words. -/
theorem partition_perm (b : ℕ) (xs : List ℕ) : (partition b xs).Perm xs := by
  have h (v : ℕ) : decide (digit b v = 1) = !decide (digit b v = 0) := by
    have := digit_lt_two b v
    by_cases hz : digit b v = 0
    · simp [hz]
    · have ho : digit b v = 1 := by omega
      simp [ho]
  simpa only [partition, select, h] using
    List.filter_append_perm (fun v => decide (digit b v = 0)) xs

/-- Each pass keeps exactly the same number of words. -/
theorem length_partition (b : ℕ) (xs : List ℕ) : (partition b xs).length = xs.length :=
  (partition_perm b xs).length_eq

/-- All radix passes preserve the input multiset. -/
theorem passes_perm (bits : ℕ) (xs : List ℕ) : (passes bits xs).Perm xs := by
  induction bits with
  | zero => exact .refl _
  | succ b ih => exact (partition_perm b _).trans ih

/-- A pass extends sortedness modulo `2^b` to sortedness modulo `2^(b+1)`. -/
theorem partition_pairwise {b : ℕ} {xs : List ℕ}
    (hs : xs.Pairwise (fun u v => u % 2 ^ b ≤ v % 2 ^ b)) :
    (partition b xs).Pairwise (fun u v => u % 2 ^ (b + 1) ≤ v % 2 ^ (b + 1)) := by
  have he (v : ℕ) : v % 2 ^ (b + 1) = v % 2 ^ b + 2 ^ b * digit b v := by
    rw [Nat.pow_succ, Nat.mod_mul, digit]
  have hp (t : ℕ) :
      (select b t xs).Pairwise (fun u v => u % 2 ^ (b + 1) ≤ v % 2 ^ (b + 1)) := by
    apply (hs.filter _).imp_of_mem
    intro u v hu hv huv
    change u ∈ select b t xs at hu
    change v ∈ select b t xs at hv
    rw [mem_select] at hu hv
    rw [he, he, hu.2, hv.2]
    omega
  apply List.pairwise_append.mpr
  refine ⟨hp 0, hp 1, ?_⟩
  intro u hu v hv
  rw [mem_select] at hu hv
  rw [he, he, hu.2, hv.2]
  have hmod := Nat.mod_lt u (Nat.two_pow_pos b)
  omega

/-- The output is sorted on the low `bits` bits. -/
theorem passes_pairwise (bits : ℕ) (xs : List ℕ) :
    (passes bits xs).Pairwise (fun u v => u % 2 ^ bits ≤ v % 2 ^ bits) := by
  induction bits with
  | zero => simp [passes, List.pairwise_iff_getElem, Nat.mod_one]
  | succ b ih => exact partition_pairwise ih

/-- Keys strictly below `2^bits` are sorted in unsigned order after `bits` passes. -/
theorem passes_correct (bits : ℕ) (xs : List ℕ)
    (hbound : ∀ v ∈ xs, v < 2 ^ bits) :
    (passes bits xs).Perm xs ∧ (passes bits xs).Pairwise (· ≤ ·) := by
  refine ⟨passes_perm bits xs, (passes_pairwise bits xs).imp_of_mem ?_⟩
  intro u v hu hv huv
  have hu' := hbound u ((passes_perm bits xs).mem_iff.mp hu)
  have hv' := hbound v ((passes_perm bits xs).mem_iff.mp hv)
  simpa only [Nat.mod_eq_of_lt hu', Nat.mod_eq_of_lt hv'] using huv

end Cslib.Algorithms.WordRAM.RadixSort
