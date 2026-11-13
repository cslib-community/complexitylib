/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# The permanent of a 0/1 matrix

The permanent of a matrix `A : Matrix n n ℕ` whose entries are all at most `1` is the number of
permutations `σ` with `A i (σ i) = 1` for every `i`, that is, the number of perfect matchings of
the bipartite graph whose edges are the one-entries of `A`.

Boolean permutation matrices supported in an arbitrary relation are counted by the permutations
respecting that relation (`Matrix.card_filter_isPermMatrix`).

## Main results

* `Matrix.permanent_eq_card_filter_of_le_one`: the permanent of a 0/1 matrix counts permutations.
* `Matrix.card_filter_isPermMatrix`: Boolean permutation matrices supported in a relation are as
  many as the permutations along it.
-/

public section

open Finset

namespace Matrix

section

variable {n : ℕ}

/-- **Boolean permutation matrices count permutations.** The Boolean `n × n` matrices with a
`true` entry in every row, at most one in every row and column, and `true` entries only where
`r` holds, are as many as the permutations `σ` with `r i (σ i)` for every `i`. -/
theorem card_filter_isPermMatrix (r : Fin n → Fin n → Prop) [∀ i j, Decidable (r i j)] :
    (Finset.univ.filter fun M : Fin n → Fin n → Bool =>
        (∀ i, ∃ j, M i j = true) ∧ (∀ i j k, M i j = true → M i k = true → j = k) ∧
          (∀ i k j, M i j = true → M k j = true → i = k) ∧
            ∀ i j, M i j = true → r i j).card =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => ∀ i, r i (σ i)).card := by
  classical
  symm
  refine Finset.card_bij (fun σ _ i j => decide (σ i = j)) (fun σ hσ => ?_)
    (fun σ _ τ _ h => ?_) (fun M hM => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hσ ⊢
    refine ⟨fun i => ⟨σ i, rfl⟩, fun i j k hj hk => hj ▸ hk, fun i k j hi hk => ?_,
      fun i j h => h ▸ hσ i⟩
    exact σ.injective (hi.trans hk.symm)
  · ext i
    have := congrFun (congrFun h i) (σ i)
    simp only [decide_true] at this
    exact congrArg Fin.val (of_decide_eq_true this.symm).symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    obtain ⟨hrow, huniq, hcol, hsupp⟩ := hM
    choose f hf using hrow
    have hinj : Function.Injective f := fun i k h => hcol i k (f i) (hf i) (h ▸ hf k)
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    refine ⟨σ, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun i => hsupp i (f i) (hf i)
    funext i j
    change decide (f i = j) = M i j
    by_cases h : M i j = true
    · rw [h, decide_eq_true_iff]
      exact huniq i (f i) j (hf i) h
    · rw [Bool.not_eq_true] at h
      rw [h, decide_eq_false_iff_not]
      rintro rfl
      exact absurd (hf i) (by simp [h])

end

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The permanent of a 0/1 matrix counts the permutations along its one-entries. -/
theorem permanent_eq_card_filter_of_le_one {A : Matrix n n ℕ} (hA : ∀ i j, A i j ≤ 1) :
    A.permanent = #{σ : Equiv.Perm n | ∀ i, A i (σ i) = 1} := by
  rw [← permanent_transpose, permanent, card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun σ _ => ?_
  split_ifs with h
  · exact prod_eq_one fun i _ => h i
  · obtain ⟨i, hi⟩ := not_forall.1 h
    exact prod_eq_zero (mem_univ i) (by have := hA i (σ i); simp only [transpose_apply]; omega)

end Matrix
