/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# Sums over ranges, consecutive blocks and residue classes

Small facts about lists of natural numbers.

* **Sums over ranges.** A list sum over `List.range n` is the `Finset` sum over `range n`
  (`List.sum_map_range_eq_sum_range`); a list is its entries at `0, …, length - 1`
  (`List.map_getD_range`); sums over a `flatMap` and of a filter's length
  (`List.sum_map_flatMap`, `List.length_filter_eq_sum`), and a `Finset` sum of list sums is a
  list sum of `Finset` sums (`Finset.sum_list_sum_comm`).
* **Consecutive blocks.** Numbering blocks of sizes `w 0, w 1, …` consecutively, block `b` is
  `List.blockRange w b`, starting at `List.blockStart w b`; the blocks below `B` are the numbers
  below `List.blockStart w B` (`List.flatMap_blockRange`). The pairs `g J + h` for `g < G`,
  `h < J` are the numbers below `G J` (`List.flatMap_range_mul`).
* **Residue classes.** `List.residueClass J m g` is the numbers below `m` congruent to `g` modulo
  `J`. Summing over the residue classes modulo `J > 0` sums over the list (`List.sum_filter_mod`),
  and a residue class below `m` has at most `m / J + 1` numbers
  (`List.length_residueClass_le`).

## Main definitions

* `List.blockStart`, `List.blockRange`: consecutive blocks.
* `List.residueClass`: a residue class below `m`.

## Main results

* `List.sum_map_range_eq_sum_range`, `List.map_getD_range`, `List.sum_map_flatMap`,
  `List.length_filter_eq_sum`, `Finset.sum_list_sum_comm`: sums.
* `List.flatMap_blockRange`, `List.flatMap_range_mul`: consecutive blocks.
* `List.sum_filter_mod`, `List.sum_residueClass`, `List.sum_length_filter_mod`,
  `List.length_residueClass_le`: residue classes.
-/

public section

open Finset

namespace List

/-! ### Sums over ranges -/

/-- A list sum over `List.range n` is the `Finset` sum over `range n`. -/
theorem sum_map_range_eq_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  (List.sum_map_range n f).trans (Finset.sum_range f).symm

/-- A list is its entries at `0, …, length - 1`. -/
theorem map_getD_range {α : Type*} (l : List α) (x : α) :
    (List.range l.length).map (l.getD · x) = l := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [List.getElem?_eq_getElem h₂]

/-- A sum over a `flatMap` sums the inner sums. -/
theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

/-- The length of a filtered list counts its elements satisfying the predicate. -/
theorem length_filter_eq_sum {α : Type*} (l : List α) (q : α → Bool) :
    (l.filter q).length = (l.map fun x => if q x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases hx : q x <;> simp [hx, ih, Nat.add_comm]

end List

/-- A `Finset` sum of list sums is the list sum of the `Finset` sums. -/
theorem Finset.sum_list_sum_comm {ι α : Type*} (s : Finset ι) (l : List α) (f : ι → α → ℕ) :
    ∑ h ∈ s, (l.map (f h)).sum = (l.map fun x => ∑ h ∈ s, f h x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

namespace List

/-! ### Consecutive blocks -/

/-- The first number of block `b` when block `b'` has `w b'` numbers: `Σ_{b' < b} w b'`. -/
@[expose] def blockStart (w : ℕ → ℕ) (b : ℕ) : ℕ := ((List.range b).map w).sum

/-- The numbers of block `b`: `blockStart w b, …, blockStart w b + w b - 1`. -/
@[expose] def blockRange (w : ℕ → ℕ) (b : ℕ) : List ℕ := List.range' (blockStart w b) (w b)

theorem blockStart_succ (w : ℕ → ℕ) (b : ℕ) : blockStart w (b + 1) = blockStart w b + w b := by
  simp [blockStart, List.range_succ]

/-- **Consecutive blocks**: the numbers of the blocks below `B`, in order, are the numbers below
`blockStart w B`. -/
theorem flatMap_blockRange (w : ℕ → ℕ) (B : ℕ) :
    (List.range B).flatMap (blockRange w) = List.range (blockStart w B) := by
  induction B with
  | zero => simp [blockStart]
  | succ B ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, blockRange,
      List.range_eq_range', List.range_eq_range', blockStart_succ]
    simpa using List.range'_append_1 (s := 0) (m := blockStart w B) (n := w B)

/-- The pairs `g J + h` for `g < G` and `h < J`, in order, are the numbers below `G J`. -/
theorem flatMap_range_mul (G J : ℕ) :
    (List.range G).flatMap (fun g => (List.range J).map (g * J + ·)) = List.range (G * J) := by
  induction G with
  | zero => simp
  | succ G ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton,
      ← List.range'_eq_map_range, List.range_eq_range', List.range_eq_range', Nat.succ_mul]
    simpa using List.range'_append_1 (s := 0) (m := G * J) (n := J)

/-! ### Residue classes -/

/-- **The residue class of `g` modulo `J` below `m`**: the numbers below `m` congruent to `g`,
in increasing order. -/
@[expose] def residueClass (J m g : ℕ) : List ℕ := (List.range m).filter (· % J = g)

/-- Summing over the residue classes modulo `J > 0` sums over the list. -/
theorem sum_filter_mod {J : ℕ} (hJ : 0 < J) (l : List ℕ) (f : ℕ → ℕ) :
    ∑ h ∈ Finset.range J, ((l.filter (· % J = h)).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hc : ∀ h, (((x :: l).filter (· % J = h)).map f).sum =
        (if x % J = h then f x else 0) + ((l.filter (· % J = h)).map f).sum := by
      intro h
      by_cases hx : x % J = h <;> simp [hx]
    rw [Finset.sum_congr rfl fun h _ => hc h, Finset.sum_add_distrib, ih,
      Finset.sum_ite_eq (Finset.range J) (x % J) (fun _ => f x),
      ite_eq_left (Finset.mem_range.mpr (Nat.mod_lt x hJ))]
    simp

/-- Summing over the residue classes below `m` sums over the numbers below `m`. -/
theorem sum_residueClass {J : ℕ} (hJ : 0 < J) (m : ℕ) (f : ℕ → ℕ) :
    ∑ g ∈ Finset.range J, ((residueClass J m g).map f).sum = ((List.range m).map f).sum :=
  sum_filter_mod hJ _ f

/-- Summing the sizes of the residue classes modulo `J > 0` gives the length. -/
theorem sum_length_filter_mod {J : ℕ} (hJ : 0 < J) (l : List ℕ) :
    ∑ h ∈ Finset.range J, (l.filter (· % J = h)).length = l.length := by
  simpa using sum_filter_mod hJ l fun _ => 1

/-- **A residue class below `m` has at most `m / J + 1` numbers.** -/
theorem length_residueClass_le (J m g : ℕ) : (residueClass J m g).length ≤ m / J + 1 := by
  rw [residueClass, ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  calc #((List.range m).filter (· % J = g)).toFinset
      ≤ #(Finset.range (m / J + 1)) := by
        refine Finset.card_le_card_of_injOn (· / J) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
        · simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range,
            decide_eq_true_eq] at hx
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hx.1.le)
        · simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range,
            decide_eq_true_eq] at hx hy
          rw [← Nat.div_add_mod x J, ← Nat.div_add_mod y J, hx.2, hy.2]
          exact congrArg (J * · + g) hxy
    _ = m / J + 1 := Finset.card_range _

end List
