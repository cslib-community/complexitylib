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
a new last bin when no bin has room. Any two bins it returns are jointly overfull: whichever was
opened later received its first item only because that item did not fit into the earlier one
(`Cslib.Algorithms.Lean.BinPacking.pairwise_firstFit`). So First Fit uses fewer than twice as many
bins as any packing (`Cslib.Algorithms.Lean.BinPacking.length_firstFit_lt`), that is at most
`2 * OPT - 1` bins, a slight sharpening of the bound `2 * OPT + 1` of
[Williamson and Shmoys, Section 3.3][WilliamsonShmoys2011] by the same pairing argument.
The tight bound `⌊1.7 * OPT⌋` [Johnson, Demers, Ullman, Garey and
Graham][JohnsonDemersUllmanGareyGraham1974] is not formalized here.

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.firstFitInsert`: insert an item into the first bin with room.
* `Cslib.Algorithms.Lean.BinPacking.firstFit`: the First Fit algorithm.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.isPacking_firstFit`: First Fit returns a packing.
* `Cslib.Algorithms.Lean.BinPacking.pairwise_firstFit`: any two bins of First Fit are jointly
  overfull.
* `Cslib.Algorithms.Lean.BinPacking.length_firstFit_lt`: First Fit uses fewer than twice as many
  bins as any packing.

## References

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

private theorem pairwise_firstFitInsert {C a : ℕ} :
    ∀ {bins : List (List ℕ)}, bins.Pairwise (fun b b' => C < b.sum + b'.sum) →
      (firstFitInsert C a bins).Pairwise (fun b b' => C < b.sum + b'.sum)
  | [], _ => by simp [firstFitInsert]
  | b :: bs, h => by
    rw [List.pairwise_cons] at h
    simp only [firstFitInsert]
    split_ifs with hb
    · rw [List.pairwise_cons]
      refine ⟨fun c hc => ?_, h.2⟩
      have := h.1 c hc
      simp only [List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · rw [List.pairwise_cons]
      refine ⟨fun c hc => ?_, pairwise_firstFitInsert h.2⟩
      rcases mem_firstFitInsert hc with hc | ⟨b', hb', _, rfl⟩ | rfl
      · exact h.1 c hc
      · have := h.1 b' hb'
        simp only [List.sum_append, List.sum_cons, List.sum_nil]
        omega
      · simp only [List.sum_cons, List.sum_nil]
        omega

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
      (acc.Pairwise (fun b b' => C < b.sum + b'.sum) →
        (l.foldl (fun bins a => firstFitInsert C a bins) acc).Pairwise
          (fun b b' => C < b.sum + b'.sum)) ∧
      ((∀ a ∈ l, a ≤ C) → (∀ b ∈ acc, b.sum ≤ C) →
        ∀ b ∈ l.foldl (fun bins a => firstFitInsert C a bins) acc, b.sum ≤ C)
  | [], acc => by simp
  | a :: l, acc => by
    obtain ⟨h1, h2, h3⟩ := foldl_firstFitInsert_spec C l (firstFitInsert C a acc)
    refine ⟨?_, fun h => h2 (pairwise_firstFitInsert h), fun hl hacc => h3
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (sum_le_of_mem_firstFitInsert hacc (hl a List.mem_cons_self))⟩
    rw [List.foldl_cons]
    refine h1.trans ?_
    have := (perm_flatten_firstFitInsert C a acc).append_right l
    simpa using this

/-- First Fit's bins hold exactly the items. -/
theorem perm_flatten_firstFit (C : ℕ) (l : List ℕ) : (firstFit C l).flatten ~ l := by
  simpa [firstFit] using (foldl_firstFitInsert_spec C l []).1

/-- Any two bins of First Fit are jointly overfull. -/
theorem pairwise_firstFit (C : ℕ) (l : List ℕ) :
    (firstFit C l).Pairwise (fun b b' => C < b.sum + b'.sum) :=
  (foldl_firstFitInsert_spec C l []).2.1 List.Pairwise.nil

/-- First Fit returns a packing whenever every item fits into a bin. -/
theorem isPacking_firstFit {C : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a ≤ C) :
    IsPacking C l (firstFit C l) :=
  ⟨perm_flatten_firstFit C l, (foldl_firstFitInsert_spec C l []).2.2 hl (by simp)⟩

/-- **First Fit is a 2-approximation**: on a nonempty list of items it uses fewer than twice as
many bins as any packing, that is at most `2 * OPT - 1` bins. -/
theorem length_firstFit_lt {C : ℕ} {l : List ℕ} {Q : List (List ℕ)} (hQ : IsPacking C l Q)
    (hl : l ≠ []) : (firstFit C l).length < 2 * Q.length :=
  length_lt_two_mul_of_isChain (perm_flatten_firstFit C l) (pairwise_firstFit C l).isChain hQ hl

end Cslib.Algorithms.Lean.BinPacking
