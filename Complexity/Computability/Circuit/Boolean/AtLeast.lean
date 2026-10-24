/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Synthesis
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Complexity.Foundations.Data.BitString.Threshold
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Linarith

/-!
# Threshold functions by De Morgan circuits of quadratic size

Given Boolean functions `f 0, f 1, …` that are already available, the functions "at least `j` of
`f 0, …, f (i - 1)` are true" satisfy the recursion

`atLeast (i + 1) (j + 1) = atLeast i (j + 1) ∨ (f i ∧ atLeast i j)`,

so all of them for `i, j ≤ k` are synthesised with `O(k ^ 2)` gates over the De Morgan basis. In
particular every threshold function, and the majority, of `k` available functions has a circuit of
size `O(k ^ 2)` on top of them.

## Main definitions

* `Cslib.Circuits.Boolean.atLeast`, `Cslib.Circuits.Boolean.atLeastUpTo`: the counting functions,
  and the counting functions up to a given level.

## Main results

* `Cslib.Circuits.Boolean.synthesis_atLeastUpTo`: all counting functions for `i ≤ k`.
* `Cslib.Circuits.Boolean.synthesis_atLeast`: one threshold function, within `O(k ^ 2)` gates.
* `Cslib.Circuits.Boolean.complexity_threshold_le`: the threshold functions `Cslib.threshold` on
  `m` variables have circuits with `O(m ^ 2)` gates.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {n : ℕ}

/-- `atLeast f i j x`: at least `j` of `f 0 x, …, f (i - 1) x` are true. -/
def atLeast (f : ℕ → BooleanFunction n) (i j : ℕ) : BooleanFunction n :=
  fun x => decide (j ≤ ((Finset.range i).filter fun l => f l x = true).card)

variable (f : ℕ → BooleanFunction n)

/-- At least `0` of the first `i` functions are always true. -/
@[simp] theorem atLeast_zero_right (i : ℕ) : atLeast f i 0 = fun _ => true := by
  funext x
  simp [atLeast]

/-- Among `0` functions, at least `j + 1` are never true. -/
theorem atLeast_zero_succ (j : ℕ) : atLeast f 0 (j + 1) = fun _ => false := by
  funext x
  simp [atLeast]

/-- The counting recursion. -/
theorem atLeast_succ_succ (i j : ℕ) (x : Fin n → Bool) :
    atLeast f (i + 1) (j + 1) x = (atLeast f i (j + 1) x || (f i x && atLeast f i j x)) := by
  simp only [atLeast, Finset.range_add_one, Finset.filter_insert]
  by_cases hi : f i x = true
  · rw [ite_eq_left hi, Finset.card_insert_of_notMem (by simp)]
    simp only [hi, Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  · rw [ite_eq_right hi]
    simp [hi]

/-- The counting functions of levels `0, …, i`. -/
def atLeastUpTo (k i : ℕ) : Set (BooleanFunction n) :=
  {g | ∃ i' ≤ i, ∃ j ≤ k + 1, g = atLeast f i' j}

/-- All counting functions of levels `0, …, i ≤ k`, if `f 0, …, f (k - 1)` are available in `s`:
two constants, and two gates for each pair `(i', j)` with `0 < i' ≤ i` and `j ≤ k + 1`. -/
theorem synthesis_atLeastUpTo {s : Set (BooleanFunction n)} (k : ℕ) (hf : ∀ i < k, f i ∈ s) :
    ∀ i ≤ k, Synthesis interpretation s (atLeastUpTo f k i) (2 + i * (2 * (k + 2)))
  | 0, _ => by
    refine ((Synthesis.const true).union (Synthesis.const false)).mono Set.Subset.rfl ?_
      (by omega)
    rintro g ⟨i', hi', j, -, rfl⟩
    obtain rfl : i' = 0 := Nat.le_zero.1 hi'
    rcases j with _ | j
    · exact Or.inl (by rw [atLeast_zero_right]; rfl)
    · exact Or.inr (by rw [atLeast_zero_succ]; rfl)
  | i + 1, hi => by
    have hprev := synthesis_atLeastUpTo k hf i (by omega)
    have hmem : ∀ j ≤ k + 1, atLeast f i j ∈ s ∪ atLeastUpTo f k i :=
      fun j hj => Or.inr ⟨i, le_rfl, j, hj, rfl⟩
    have hlevel : Synthesis interpretation (s ∪ atLeastUpTo f k i)
        (⋃ j ∈ Finset.range (k + 2), {atLeast f (i + 1) j}) (∑ _j ∈ Finset.range (k + 2), 2) := by
      refine Synthesis.biUnion _ _ _ fun j hj => ?_
      have hj := Finset.mem_range.1 hj
      rcases j with _ | j
      · refine (Synthesis.of_mem (hmem 0 (Nat.zero_le _))).mono Set.Subset.rfl ?_ (Nat.zero_le 2)
        simp
      · have h := (Synthesis.of_mem (hmem (j + 1) (by omega))).or
          ((Synthesis.of_mem (Or.inl (hf i (by omega)) : f i ∈ s ∪ atLeastUpTo f k i)).and
            (Synthesis.of_mem (hmem j (by omega))))
        refine (h.mono Set.Subset.rfl ?_ le_rfl)
        rw [Set.singleton_subset_iff, Set.mem_singleton_iff]
        funext x
        rw [atLeast_succ_succ]
    refine (hprev.comp hlevel).mono Set.Subset.rfl ?_ ?_
    · rintro g ⟨i', hi', j, hj, rfl⟩
      rcases Nat.lt_or_ge i' (i + 1) with h | h
      · exact Or.inl ⟨i', by omega, j, hj, rfl⟩
      · obtain rfl : i' = i + 1 := by omega
        exact Or.inr (Set.mem_biUnion (Finset.mem_range.2 (by omega)) rfl)
    · rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      nlinarith

/-- The threshold function "at least `j` of `f 0, …, f (k - 1)` are true", for `j ≤ k + 1`, on
top of available functions, within `O(k ^ 2)` gates. -/
theorem synthesis_atLeast {s : Set (BooleanFunction n)} {k j : ℕ} (hf : ∀ i < k, f i ∈ s)
    (hj : j ≤ k + 1) :
    Synthesis interpretation s {atLeast f k j} (2 + k * (2 * (k + 2))) :=
  (synthesis_atLeastUpTo f k hf k le_rfl).mono Set.Subset.rfl
    (Set.singleton_subset_iff.2 ⟨k, le_rfl, j, hj, rfl⟩) le_rfl

/-- On the `m` coordinate projections, `atLeast` at level `m` is `threshold m j`. -/
theorem atLeast_eq_threshold (m j : ℕ) :
    atLeast (fun l y => if h : l < m then y ⟨l, h⟩ else false) m j = threshold m j := by
  funext y
  simp only [atLeast, threshold, BitString.weight]
  congr 2
  rw [Finset.card_filter, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun l => if (if h : l < m then y ⟨l, h⟩ else false) = true then 1
      else 0)]
  simp

/-- The threshold functions on `m` variables have circuits with `O(m ^ 2)` gates. -/
theorem complexity_threshold_le (m j : ℕ) :
    complexity interpretation (single (threshold m j)) ≤ 2 + m * (2 * (m + 2)) := by
  by_cases hj : j ≤ m + 1
  · rw [← atLeast_eq_threshold]
    have hg : ∀ l < m, (fun y : BitString m => if h : l < m then y ⟨l, h⟩ else false) ∈
        inputs m := fun l hl => ⟨⟨l, hl⟩, funext fun y => by simp [hl]⟩
    exact (synthesis_atLeast _ hg hj).complexity_le
  · have : threshold m j = fun _ => false := funext fun y => by
      have := BitString.weight_le y
      rw [Fintype.card_fin] at this
      rw [← Bool.not_eq_true, threshold_eq_true_iff]
      omega
    rw [this]
    exact (Synthesis.const false).complexity_le.trans (by omega)

end Cslib.Circuits.Boolean
