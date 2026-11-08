/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.BinPacking.Basic

/-!
# First Fit

First Fit keeps every bin open. It places each item into the first bin with enough room, opening
a new last bin when no bin has room. So every item of a bin did not fit into any earlier bin,
even into that bin's final contents
(`Cslib.Algorithms.Lean.BinPacking.pairwise_forall_lt_sum_add_firstFit`), and as no bin is empty
(`Cslib.Algorithms.Lean.BinPacking.ne_nil_of_mem_firstFit`), any two bins it returns are jointly
overfull (`Cslib.Algorithms.Lean.BinPacking.pairwise_firstFit`). So First Fit uses fewer than
twice as many bins as any packing (`Cslib.Algorithms.Lean.BinPacking.length_firstFit_lt`), that
is at most `2 * OPT - 1` bins, a slight sharpening of the bound `2 * OPT + 1` of
[Williamson and Shmoys, Section 3.3][WilliamsonShmoys2011] by the same pairing argument. Johnson's
thesis [Johnson][Johnson1973] analyses Next Fit and First Fit; by the notes to Chapter 3 of
Williamson and Shmoys, their First Fit argument uses the thesis's analysis of Next Fit. The
asymptotic bound `17/10 * OPT + 2` of
[Johnson, Demers, Ullman, Garey and Graham][JohnsonDemersUllmanGareyGraham1974], sharpened to
`17/10 * OPT + 4/5`, is in `Complexity.Algorithms.Lean.BinPacking.FirstFitWeight`.

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.firstFitInsert`: insert an item into the first bin with room.
* `Cslib.Algorithms.Lean.BinPacking.firstFit`: the First Fit algorithm.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.isPacking_firstFit`: First Fit returns a packing.
* `Cslib.Algorithms.Lean.BinPacking.pairwise_forall_lt_sum_add_firstFit`: every item of a later
  bin of First Fit overflows every earlier bin.
* `Cslib.Algorithms.Lean.BinPacking.ne_nil_of_mem_firstFit`: First Fit opens no empty bin.
* `Cslib.Algorithms.Lean.BinPacking.pairwise_firstFit`: any two bins of First Fit are jointly
  overfull.
* `Cslib.Algorithms.Lean.BinPacking.length_firstFit_lt`: First Fit uses fewer than twice as many
  bins as any packing.

## References

* [D. S. Johnson, *Near-optimal bin packing algorithms*][Johnson1973]
* [D. S. Johnson, A. Demers, J. D. Ullman, M. R. Garey, R. L. Graham, *Worst-case performance
  bounds for simple one-dimensional packing algorithms*][JohnsonDemersUllmanGareyGraham1974]
* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

open scoped List

/-- Insert the item `a` into the first bin with enough room, or into a new last bin if no bin has
room. -/
@[expose] def firstFitInsert (C a : ℕ) : List (List ℕ) → List (List ℕ)
  | [] => [[a]]
  | b :: bs => if b.sum + a ≤ C then (b ++ [a]) :: bs else b :: firstFitInsert C a bs

/-- **First Fit** with bin capacity `C`. -/
@[expose] def firstFit (C : ℕ) (l : List ℕ) : List (List ℕ) :=
  l.foldl (fun bins a => firstFitInsert C a bins) []

/-- Inserting an item adds it to the bins' contents. -/
theorem perm_flatten_firstFitInsert (C a : ℕ) :
    ∀ bins : List (List ℕ), (firstFitInsert C a bins).flatten ~ bins.flatten ++ [a]
  | [] => by simp [firstFitInsert]
  | b :: bs => by
    simp only [firstFitInsert]
    split_ifs
    · simp only [List.flatten_cons, List.append_assoc]
      exact List.Perm.append_left b List.perm_append_comm
    · simp only [List.flatten_cons, List.append_assoc]
      exact List.Perm.append_left b (perm_flatten_firstFitInsert C a bs)

/-- A bin after inserting `a` is an old bin, an old bin with room for `a` extended by `a`, or the
new bin `[a]`. -/
theorem mem_firstFitInsert {C a : ℕ} :
    ∀ {bins : List (List ℕ)} {c : List ℕ}, c ∈ firstFitInsert C a bins →
      c ∈ bins ∨ (∃ b ∈ bins, b.sum + a ≤ C ∧ c = b ++ [a]) ∨ c = [a]
  | [], c, h => by simp_all [firstFitInsert]
  | b :: bs, c, h => by
    simp only [firstFitInsert] at h
    split_ifs at h with hb
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (Or.inl ⟨b, List.mem_cons_self, hb, rfl⟩)
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl List.mem_cons_self
      · rcases mem_firstFitInsert h with h | ⟨b', hb', hfit, rfl⟩ | rfl
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (Or.inl ⟨b', List.mem_cons_of_mem _ hb', hfit, rfl⟩)
        · exact Or.inr (Or.inr rfl)

private theorem pairwise_forall_lt_sum_add_firstFitInsert {C a : ℕ} :
    ∀ {bins : List (List ℕ)}, bins.Pairwise (fun b b' => ∀ c ∈ b', C < b.sum + c) →
      (firstFitInsert C a bins).Pairwise (fun b b' => ∀ c ∈ b', C < b.sum + c)
  | [], _ => by simp [firstFitInsert]
  | b :: bs, h => by
    rw [List.pairwise_cons] at h
    simp only [firstFitInsert]
    split_ifs with hb
    · rw [List.pairwise_cons]
      refine ⟨fun c hc x hx => ?_, h.2⟩
      have := h.1 c hc x hx
      simp only [List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · rw [List.pairwise_cons]
      refine ⟨fun c hc x hx => ?_, pairwise_forall_lt_sum_add_firstFitInsert h.2⟩
      rcases mem_firstFitInsert hc with hc | ⟨b', hb', _, rfl⟩ | rfl
      · exact h.1 c hc x hx
      · rcases List.mem_append.1 hx with hx | hx
        · exact h.1 b' hb' x hx
        · rw [List.mem_singleton] at hx
          omega
      · rw [List.mem_singleton] at hx
        omega

private theorem ne_nil_of_mem_firstFitInsert {C a : ℕ} {bins : List (List ℕ)}
    (h : ∀ b ∈ bins, b ≠ []) : ∀ c ∈ firstFitInsert C a bins, c ≠ [] := by
  intro c hc
  rcases mem_firstFitInsert hc with hc | ⟨b, _, _, rfl⟩ | rfl
  · exact h c hc
  · simp
  · simp

private theorem sum_le_of_mem_firstFitInsert {C a : ℕ} {bins : List (List ℕ)}
    (hbins : ∀ b ∈ bins, b.sum ≤ C) (ha : a ≤ C) :
    ∀ c ∈ firstFitInsert C a bins, c.sum ≤ C := by
  intro c hc
  rcases mem_firstFitInsert hc with hc | ⟨b, _, hfit, rfl⟩ | rfl
  · exact hbins c hc
  · simpa using hfit
  · simpa using ha

private theorem foldl_firstFitInsert_spec (C : ℕ) :
    ∀ (l : List ℕ) (acc : List (List ℕ)),
      (l.foldl (fun bins a => firstFitInsert C a bins) acc).flatten ~ acc.flatten ++ l ∧
      (acc.Pairwise (fun b b' => ∀ c ∈ b', C < b.sum + c) →
        (l.foldl (fun bins a => firstFitInsert C a bins) acc).Pairwise
          (fun b b' => ∀ c ∈ b', C < b.sum + c)) ∧
      ((∀ b ∈ acc, b ≠ []) → ∀ b ∈ l.foldl (fun bins a => firstFitInsert C a bins) acc, b ≠ []) ∧
      ((∀ a ∈ l, a ≤ C) → (∀ b ∈ acc, b.sum ≤ C) →
        ∀ b ∈ l.foldl (fun bins a => firstFitInsert C a bins) acc, b.sum ≤ C)
  | [], acc => by simp
  | a :: l, acc => by
    obtain ⟨h1, h2, h3, h4⟩ := foldl_firstFitInsert_spec C l (firstFitInsert C a acc)
    refine ⟨?_, fun h => h2 (pairwise_forall_lt_sum_add_firstFitInsert h),
      fun h => h3 (ne_nil_of_mem_firstFitInsert h), fun hl hacc => h4
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (sum_le_of_mem_firstFitInsert hacc (hl a List.mem_cons_self))⟩
    rw [List.foldl_cons]
    refine h1.trans ?_
    have := (perm_flatten_firstFitInsert C a acc).append_right l
    simpa using this

/-- First Fit's bins hold exactly the items. -/
theorem perm_flatten_firstFit (C : ℕ) (l : List ℕ) : (firstFit C l).flatten ~ l := by
  simpa [firstFit] using (foldl_firstFitInsert_spec C l []).1

/-- **The First Fit rule**: every item of a bin opened later did not fit into an earlier bin,
even into that bin's final contents. -/
theorem pairwise_forall_lt_sum_add_firstFit (C : ℕ) (l : List ℕ) :
    (firstFit C l).Pairwise (fun b b' => ∀ c ∈ b', C < b.sum + c) :=
  (foldl_firstFitInsert_spec C l []).2.1 List.Pairwise.nil

/-- First Fit opens no empty bin. -/
theorem ne_nil_of_mem_firstFit {C : ℕ} {l : List ℕ} {b : List ℕ} (hb : b ∈ firstFit C l) :
    b ≠ [] :=
  (foldl_firstFitInsert_spec C l []).2.2.1 (by simp) b hb

/-- Any two bins of First Fit are jointly overfull. -/
theorem pairwise_firstFit (C : ℕ) (l : List ℕ) :
    (firstFit C l).Pairwise (fun b b' => C < b.sum + b'.sum) :=
  (pairwise_forall_lt_sum_add_firstFit C l).imp_of_mem fun _ hb' h => by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (ne_nil_of_mem_firstFit hb')
    have := h c hc
    have := List.le_sum_of_mem hc
    omega

/-- First Fit returns a packing whenever every item fits into a bin. -/
theorem isPacking_firstFit {C : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a ≤ C) :
    IsPacking C l (firstFit C l) :=
  ⟨perm_flatten_firstFit C l, (foldl_firstFitInsert_spec C l []).2.2.2 hl (by simp)⟩

/-- **First Fit is a 2-approximation**: on a nonempty list of items it uses fewer than twice as
many bins as any packing, that is at most `2 * OPT - 1` bins. -/
theorem length_firstFit_lt {C : ℕ} {l : List ℕ} {Q : List (List ℕ)} (hQ : IsPacking C l Q)
    (hl : l ≠ []) : (firstFit C l).length < 2 * Q.length :=
  length_lt_two_mul_of_isChain (perm_flatten_firstFit C l) (pairwise_firstFit C l).isChain hQ hl

end Cslib.Algorithms.Lean.BinPacking
