/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.List.FinRange

/-!
# Finite-array permutations and ranks

Use ordinary `List.Perm` on `List.ofFn` to transport predicates and their multiplicities.
If an entry has a unique key, its sorted position is the number of strictly smaller keys;
other keys may repeat. The key order need only be a partial order.

## Main results

* `List.Perm.exists_ofFn_iff`, `List.Perm.existsUnique_ofFn_iff`: predicate transport.
* `List.Perm.card_filter_ofFn_eq`: preservation of predicate counts.
* `List.countP_range_eq_card_filter`: counting the numbers below `n` that pass a test is counting
  the elements of `Fin n` that pass it.
* `List.sum_map_range`, `List.sum_map_drop_range`, `List.sum_map_drop_range_fin`: sums over
  `List.range n` and its tails as `Fin` or interval sums.
* `Fin.card_lt_of_monotone_of_unique`: a unique value in a monotone array has its index many
  smaller entries.
* `List.Perm.key_ofFn_eq_of_rank`: a unique key occurs at its rank after sorting.
* `List.Perm.apply_ofFn_eq_of_rank`: identify an entire entry at its sorted position.

## References

* The rank argument supports the two-sort routing construction in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
* [OpenAI2026RationalHitting]
-/

@[expose] public section

open Finset

/-- Permuting a finite array preserves whether any entry satisfies a predicate. -/
theorem List.Perm.exists_ofFn_iff {α : Type*} {m n : ℕ} {f : Fin m → α} {g : Fin n → α}
    (perm : (List.ofFn f).Perm (List.ofFn g)) (p : α → Prop) :
    (∃ i, p (f i)) ↔ ∃ i, p (g i) := by
  have h : (∃ x ∈ List.ofFn f, p x) ↔ ∃ x ∈ List.ofFn g, p x :=
    exists_congr fun _ => and_congr_left fun _ => perm.mem_iff
  simpa [List.mem_ofFn] using h

/-- Count satisfying array entries by summing their Boolean indicators. -/
theorem List.countP_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).countP p = ∑ i, if p (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih, Nat.add_comm]

/-- The numbers below `n` that pass a test are as many as the elements of `Fin n` that pass it. -/
theorem List.countP_range_eq_card_filter (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = #{j : Fin n | p j = true} := by
  rw [← List.map_coe_finRange_eq_range, ← List.ofFn_eq_map, List.countP_ofFn, card_filter]

/-- A sum over `List.range n` is a sum over `Fin n`. -/
theorem List.sum_map_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  rfl

/-- A tail of `List.range n`, summed as a list, is the sum over `Finset.Ico lo n`. -/
theorem List.sum_map_drop_range {M : Type*} [AddCommMonoid M] (n lo : ℕ) (f : ℕ → M) :
    (((List.range n).drop lo).map f).sum = ∑ k ∈ Finset.Ico lo n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases h : lo ≤ n
    · rw [List.range_succ, List.drop_append_of_le_length (by simpa using h), List.map_append,
        List.sum_append, ih, List.map_singleton, List.sum_singleton,
        Nat.Ico_succ_right_eq_insert_Ico h, Finset.sum_insert (by simp), add_comm]
    · have hle : n + 1 ≤ lo := by omega
      rw [List.drop_eq_nil_of_le (by simpa using hle), Finset.Ico_eq_empty_of_le hle,
        List.map_nil, List.sum_nil, Finset.sum_empty]

/-- A tail of `List.range n` after `i : Fin n`, summed as a list, is the sum over
`Finset.Ioi i`. -/
theorem List.sum_map_drop_range_fin {M : Type*} [AddCommMonoid M] {n : ℕ} (i : Fin n)
    (f : ℕ → M) :
    (((List.range n).drop (i.val + 1)).map f).sum = ∑ k ∈ Finset.Ioi i, f k.val := by
  rw [List.sum_map_drop_range]
  calc _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by
         congr 1
         ext
         simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
         lia
       _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
       _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by rw [← Fin.sum_univ_eq_sum_range]
       _ = _ := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/-- Permuting a finite array preserves the number of entries satisfying a predicate. -/
theorem List.Perm.card_filter_ofFn_eq {α : Type*} {n : ℕ} {f g : Fin n → α}
    (perm : (List.ofFn f).Perm (List.ofFn g)) (p : α → Prop) [DecidablePred p] :
    #{i | p (f i)} = #{i | p (g i)} := by
  have h := perm.countP_eq (fun x => decide (p x))
  simpa only [List.countP_ofFn, decide_eq_true_eq, Finset.card_filter] using h

/-- Permuting a finite array preserves unique occurrence of a predicate. -/
theorem List.Perm.existsUnique_ofFn_iff {α : Type*} {n : ℕ} {f g : Fin n → α}
    (perm : (List.ofFn f).Perm (List.ofFn g)) (p : α → Prop) :
    (∃! i, p (f i)) ↔ ∃! i, p (g i) := by
  classical
  have h := List.Perm.card_filter_ofFn_eq perm p
  simpa only [Finset.card_eq_one_iff_existsUnique, Finset.mem_filter,
    Finset.mem_univ, true_and] using (congrArg (fun size => size = 1) h).to_iff

/-- A unique value in a monotone finite array has exactly its index many smaller entries. -/
theorem Fin.card_lt_of_monotone_of_unique {α : Type*} [PartialOrder α] [DecidableLT α] {n : ℕ}
    {f : Fin n → α} (sorted : Monotone f) (j : Fin n)
    (unique : ∀ i, f i = f j → i = j) : #{i | f i < f j} = j.val := by
  have lt_iff (i : Fin n) : f i < f j ↔ i < j := by
    constructor
    · intro h
      by_contra hn
      exact (not_lt_of_ge (sorted (le_of_not_gt hn))) h
    · intro h
      exact lt_of_le_of_ne (sorted h.le) (fun he => h.ne (unique i he))
  calc
    #{i | f i < f j} = #(Finset.Iio j) := congrArg Finset.card (by ext i; simp [lt_iff])
    _ = j.val := Fin.card_Iio j

/-- A unique key occurs at its rank after a finite array is sorted by that key. -/
theorem List.Perm.key_ofFn_eq_of_rank {α β : Type*} [PartialOrder β] [DecidableLT β] {n : ℕ}
    {f g : Fin n → α} (perm : (List.ofFn f).Perm (List.ofFn g))
    (key : α → β) (sorted : Monotone (key ∘ g)) (target : β)
    (unique : ∃! i, key (f i) = target) (j : Fin n)
    (rank : #{i | key (f i) < target} = j.val) : key (g j) = target := by
  obtain ⟨i, hi, hu⟩ :=
    (List.Perm.existsUnique_ofFn_iff perm (fun row => key row = target)).mp unique
  have ri := Fin.card_lt_of_monotone_of_unique sorted i (fun k hk => hu k (hk.trans hi))
  have preserve := List.Perm.card_filter_ofFn_eq perm (fun row => key row < target)
  simp only [Function.comp_apply, hi] at ri
  have same : i = j := Fin.ext (by lia)
  simpa only [same] using hi

/-- Sorting places an entry with a unique key at the number of strictly smaller keys. -/
theorem List.Perm.apply_ofFn_eq_of_rank {α β : Type*} [PartialOrder β] [DecidableLT β] {n : ℕ}
    {f g : Fin n → α} (perm : (List.ofFn f).Perm (List.ofFn g))
    (key : α → β) (sorted : Monotone (key ∘ g)) (source j : Fin n)
    (unique : ∀ i, key (f i) = key (f source) → i = source)
    (rank : #{i | key (f i) < key (f source)} = j.val) : g j = f source := by
  have hj := List.Perm.key_ofFn_eq_of_rank perm key sorted (key (f source))
    ⟨source, rfl, unique⟩ j rank
  have mem : g j ∈ List.ofFn f := perm.mem_iff.mpr (by simp)
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp mem
  have same := unique i (by simpa only [hi] using hj)
  simpa only [same] using hi.symm

