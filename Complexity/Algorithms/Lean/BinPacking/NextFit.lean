/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.BinPacking.Basic

/-!
# Next Fit

Next Fit keeps a single open bin. It places each item into the open bin when the item fits, and
otherwise closes the bin and opens a new one holding the item. Every two consecutive bins it
returns are jointly overfull, since the first item of the later bin did not fit into the earlier
one, so Next Fit uses fewer than twice as many bins as any packing
(`Cslib.Algorithms.Lean.BinPacking.length_nextFit_lt`), that is at most `2 * OPT - 1` bins
[Johnson, Demers, Ullman, Garey and Graham][JohnsonDemersUllmanGareyGraham1974].
[Williamson and Shmoys, Section 3.3][WilliamsonShmoys2011] prove the bound `2 * OPT + 1` for First
Fit by the same pairing argument; it applies to Next Fit unchanged.

Next Fit keeps the items in their input order (`flatten_nextFit`), so it returns a packing
whenever every item fits into a bin (`isPacking_nextFit`).

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.nextFit`: the Next Fit algorithm.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.isPacking_nextFit`: Next Fit returns a packing.
* `Cslib.Algorithms.Lean.BinPacking.add_one_mul_length_nextFit_div_two_le`: Next Fit's volume
  bound `(C + 1) * ⌊NF / 2⌋ ≤ l.sum`.
* `Cslib.Algorithms.Lean.BinPacking.length_nextFit_lt`: Next Fit uses fewer than twice as many
  bins as any packing.

## References

* [D. S. Johnson, A. Demers, J. D. Ullman, M. R. Garey, R. L. Graham, *Worst-case performance
  bounds for simple one-dimensional packing algorithms*][JohnsonDemersUllmanGareyGraham1974]
* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

/-- One step of Next Fit on the bins in reverse order, the open bin first: add the item to the
open bin if it fits, and otherwise open a new bin holding it. -/
@[expose] def nextFitStep (C : ℕ) : List (List ℕ) → ℕ → List (List ℕ)
  | [], a => [[a]]
  | b :: bs, a => if b.sum + a ≤ C then (b ++ [a]) :: bs else [a] :: b :: bs

/-- **Next Fit** with bin capacity `C`. -/
@[expose] def nextFit (C : ℕ) (l : List ℕ) : List (List ℕ) :=
  (l.foldl (nextFitStep C) []).reverse

private theorem flatten_reverse_nextFitStep (C : ℕ) (acc : List (List ℕ)) (a : ℕ) :
    (nextFitStep C acc a).reverse.flatten = acc.reverse.flatten ++ [a] := by
  cases acc with
  | nil => simp [nextFitStep]
  | cons b bs =>
    simp only [nextFitStep]
    split_ifs <;> simp

private theorem flatten_reverse_foldl_nextFitStep (C : ℕ) :
    ∀ (l : List ℕ) (acc : List (List ℕ)),
      (l.foldl (nextFitStep C) acc).reverse.flatten = acc.reverse.flatten ++ l
  | [], acc => by simp
  | a :: l, acc => by
    rw [List.foldl_cons, flatten_reverse_foldl_nextFitStep C l, flatten_reverse_nextFitStep]
    simp

/-- Next Fit keeps the items in their input order. -/
@[simp] theorem flatten_nextFit (C : ℕ) (l : List ℕ) : (nextFit C l).flatten = l := by
  simpa [nextFit] using flatten_reverse_foldl_nextFitStep C l []

private theorem sum_le_of_mem_nextFitStep {C : ℕ} {acc : List (List ℕ)} {a : ℕ}
    (hacc : ∀ b ∈ acc, b.sum ≤ C) (ha : a ≤ C) : ∀ b ∈ nextFitStep C acc a, b.sum ≤ C := by
  cases acc with
  | nil => simpa [nextFitStep] using ha
  | cons b bs =>
    simp only [nextFitStep]
    split_ifs with h
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · simpa using h
      · exact hacc c (List.mem_cons_of_mem _ hc)
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · simpa using ha
      · exact hacc c hc

private theorem isChain_nextFitStep {C : ℕ} {acc : List (List ℕ)} {a : ℕ}
    (hacc : acc.IsChain (fun b b' => C < b.sum + b'.sum)) :
    (nextFitStep C acc a).IsChain (fun b b' => C < b.sum + b'.sum) := by
  cases acc with
  | nil => simp [nextFitStep]
  | cons b bs =>
    simp only [nextFitStep]
    split_ifs with h
    · cases bs with
      | nil => simp
      | cons c cs =>
        rw [List.isChain_cons_cons] at hacc ⊢
        refine ⟨?_, hacc.2⟩
        have := hacc.1
        simp only [List.sum_append, List.sum_cons, List.sum_nil]
        omega
    · rw [List.isChain_cons_cons]
      refine ⟨?_, hacc⟩
      simp only [List.sum_cons, List.sum_nil]
      omega

private theorem isChain_foldl_nextFitStep (C : ℕ) :
    ∀ (l : List ℕ) (acc : List (List ℕ)), acc.IsChain (fun b b' => C < b.sum + b'.sum) →
      (l.foldl (nextFitStep C) acc).IsChain (fun b b' => C < b.sum + b'.sum)
  | [], _, h => h
  | _ :: l, _, h => isChain_foldl_nextFitStep C l _ (isChain_nextFitStep h)

private theorem sum_le_of_mem_foldl_nextFitStep (C : ℕ) :
    ∀ (l : List ℕ) (acc : List (List ℕ)), (∀ a ∈ l, a ≤ C) → (∀ b ∈ acc, b.sum ≤ C) →
      ∀ b ∈ l.foldl (nextFitStep C) acc, b.sum ≤ C
  | [], _, _, h => h
  | a :: l, _, hl, h =>
    sum_le_of_mem_foldl_nextFitStep C l _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (sum_le_of_mem_nextFitStep h (hl a List.mem_cons_self))

/-- Every two consecutive bins of Next Fit are jointly overfull. -/
theorem isChain_nextFit (C : ℕ) (l : List ℕ) :
    (nextFit C l).IsChain (fun b b' => C < b.sum + b'.sum) := by
  have h := List.isChain_reverse.2 (isChain_foldl_nextFitStep C l [] List.isChain_nil)
  exact h.imp fun _ _ hb => by omega

/-- Next Fit returns a packing whenever every item fits into a bin. -/
theorem isPacking_nextFit {C : ℕ} {l : List ℕ} (hl : ∀ a ∈ l, a ≤ C) :
    IsPacking C l (nextFit C l) :=
  ⟨by rw [flatten_nextFit], fun b hb =>
    sum_le_of_mem_foldl_nextFitStep C l [] hl (by simp) b (List.mem_reverse.1 hb)⟩

/-- **Next Fit's volume bound**: `(C + 1) * ⌊NF / 2⌋ ≤ l.sum`. -/
theorem add_one_mul_length_nextFit_div_two_le (C : ℕ) (l : List ℕ) :
    (C + 1) * ((nextFit C l).length / 2) ≤ l.sum := by
  have h := add_one_mul_div_two_le_of_isChain (isChain_nextFit C l)
  rwa [← List.sum_flatten, flatten_nextFit] at h

/-- **Next Fit is a 2-approximation**: on a nonempty list of items it uses fewer than twice as
many bins as any packing, that is at most `2 * OPT - 1` bins
[Johnson, Demers, Ullman, Garey and Graham][JohnsonDemersUllmanGareyGraham1974]. -/
theorem length_nextFit_lt {C : ℕ} {l : List ℕ} {Q : List (List ℕ)} (hQ : IsPacking C l Q)
    (hl : l ≠ []) : (nextFit C l).length < 2 * Q.length :=
  length_lt_two_mul_of_isChain (by rw [flatten_nextFit]) (isChain_nextFit C l) hQ hl

end Cslib.Algorithms.Lean.BinPacking
