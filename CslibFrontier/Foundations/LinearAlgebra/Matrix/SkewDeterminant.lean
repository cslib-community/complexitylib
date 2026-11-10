/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `LinearAlgebra/Matrix/Determinant/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CslibFrontier.Foundations.GroupTheory.Perm.ReverseCycle

/-!
# Odd cycles cancel in the determinant of a skew-symmetric matrix

Let `A` be a square matrix over a commutative ring with `Aᵀ = -A`. In the Leibniz expansion
`det A = ∑ σ, sign σ • ∏ i, A (σ i) i`, the permutations with a cycle of odd length cancel in
pairs: reversing the odd cycle through a chosen point (`Equiv.Perm.reverseCycle`) keeps the sign,
negates the product (the cycle has an odd number of entries, each replaced by its negative), and
is an involution on these permutations. So the determinant is the sum over the permutations all of
whose cycles have even length (`Matrix.det_eq_sum_even_cycleType_of_transpose_eq_neg`). This is the
step in the standard proof of Tutte's determinant criterion for perfect matchings [Tutte1947].

When moreover the diagonal vanishes and the order is odd, every such permutation has a fixed point,
so the determinant is `0` (`Matrix.det_eq_zero_of_transpose_eq_neg_of_odd`). The diagonal
assumption matters only in characteristic `2`, where `Aᵀ = -A` says that `A` is symmetric.

## Main results

* `Matrix.det_eq_sum_even_cycleType_of_transpose_eq_neg`: the determinant of a skew-symmetric
  matrix is the Leibniz sum over the permutations with only even cycles.
* `Matrix.det_eq_zero_of_transpose_eq_neg_of_odd`: an alternating matrix of odd order has
  determinant `0`.

## References

* [W. T. Tutte, *The factorization of linear graphs*][Tutte1947]
-/

public section

open Equiv Equiv.Perm Finset

namespace Matrix

variable {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [CommRing R]

/-- The points of `α` on cycles of `σ` of odd length. -/
private def oddPoints (σ : Perm α) : Finset α :=
  univ.filter fun x => Odd #(σ.cycleOf x).support

private theorem mem_oddPoints {σ : Perm α} {x : α} :
    x ∈ oddPoints σ ↔ Odd #(σ.cycleOf x).support := by
  simp [oddPoints]

private theorem oddPoints_reverseCycle (σ : Perm α) (x : α) :
    oddPoints (reverseCycle σ x) = oddPoints σ := by
  unfold oddPoints
  simp only [support_cycleOf_reverseCycle]

/-- Reversing an odd cycle negates the product of a skew-symmetric matrix along a
permutation. -/
private theorem prod_reverseCycle {A : Matrix α α R} (hA : Aᵀ = -A) {σ : Perm α} {x : α}
    (hx : Odd #(σ.cycleOf x).support) :
    ∏ i, A (reverseCycle σ x i) i = -∏ i, A (σ i) i := by
  have hσx := apply_ne_of_odd_card_support_cycleOf hx
  set S := (σ.cycleOf x).support with hS
  have hmem : ∀ y, y ∈ S ↔ σ.SameCycle x y := fun y => mem_support_cycleOf_iff' hσx
  rw [← prod_mul_prod_compl S, ← prod_mul_prod_compl S (fun i => A (σ i) i)]
  have hc : ∏ i ∈ Sᶜ, A (reverseCycle σ x i) i = ∏ i ∈ Sᶜ, A (σ i) i :=
    prod_congr rfl fun i hi => by
      rw [reverseCycle_apply, ite_eq_right (by rw [← hmem]; simpa using hi)]
  have hs : ∏ i ∈ S, A (reverseCycle σ x i) i = -∏ i ∈ S, A (σ i) i := by
    rw [prod_congr rfl fun i hi => by rw [reverseCycle_apply, ite_eq_left ((hmem i).1 hi)]]
    have hre : ∏ i ∈ S, A (σ⁻¹ i) i = ∏ j ∈ S, A j (σ j) := by
      refine prod_nbij' (fun i => σ⁻¹ i) (fun j => σ j) (fun i hi => ?_) (fun j hj => ?_)
        (fun i _ => σ.apply_symm_apply i) (fun j _ => σ.symm_apply_apply j)
        (fun i _ => by rw [show σ (σ⁻¹ i) = i from σ.apply_symm_apply i])
      · exact (hmem _).2 (sameCycle_symm_apply_right.2 ((hmem i).1 hi))
      · exact (hmem _).2 (sameCycle_apply_right.2 ((hmem j).1 hj))
    have hneg : ∀ j, A j (σ j) = -A (σ j) j := fun j => by
      rw [← transpose_apply A (σ j) j, hA, Matrix.neg_apply]
    rw [hre, prod_congr rfl fun j _ => hneg j, prod_neg, hx.neg_one_pow, neg_one_mul]
  rw [hs, hc, neg_mul]

/-- A point of a nonempty finite set, chosen so that equal sets give equal points. -/
private noncomputable def pick (s : Finset α) (hs : s.Nonempty) : α := hs.choose

omit [Fintype α] [DecidableEq α] in
private theorem pick_mem (s : Finset α) (hs : s.Nonempty) : pick s hs ∈ s := hs.choose_spec

omit [Fintype α] [DecidableEq α] in
private theorem pick_congr {s t : Finset α} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    pick s hs = pick t ht := by
  subst hst
  rfl

/-- In the Leibniz expansion of the determinant of a skew-symmetric matrix, the permutations with
an odd cycle contribute `0` in total. -/
private theorem sum_oddPoints_nonempty_eq_zero {A : Matrix α α R} (hA : Aᵀ = -A) :
    ∑ σ ∈ univ.filter (fun σ : Perm α => (oddPoints σ).Nonempty),
      sign σ • ∏ i, A (σ i) i = 0 := by
  refine sum_involution
    (fun σ hσ => reverseCycle σ (pick (oddPoints σ) (mem_filter.1 hσ).2)) ?_ ?_ ?_ ?_
  · intro σ hσ
    have hx := pick_mem _ (mem_filter.1 hσ).2
    rw [mem_oddPoints] at hx
    rw [sign_reverseCycle, prod_reverseCycle hA hx, smul_neg, add_neg_cancel]
  · intro σ hσ _
    have hx := pick_mem _ (mem_filter.1 hσ).2
    rw [mem_oddPoints] at hx
    exact reverseCycle_ne hx
  · intro σ hσ
    simpa only [mem_filter, mem_univ, true_and, oddPoints_reverseCycle] using hσ
  · intro σ hσ
    rw [pick_congr (oddPoints_reverseCycle _ _) _ (mem_filter.1 hσ).2, reverseCycle_reverseCycle]

/-- **Odd cycles cancel**: the determinant of a skew-symmetric matrix is the Leibniz sum over the
permutations all of whose cycles have even length. -/
theorem det_eq_sum_even_cycleType_of_transpose_eq_neg {A : Matrix α α R} (hA : Aᵀ = -A) :
    A.det = ∑ σ ∈ univ.filter (fun σ : Perm α => ∀ n ∈ σ.cycleType, Even n),
      sign σ • ∏ i, A (σ i) i := by
  rw [det_apply, ← sum_filter_add_sum_filter_not univ (fun σ : Perm α => (oddPoints σ).Nonempty),
    sum_oddPoints_nonempty_eq_zero hA, zero_add]
  refine sum_congr (filter_congr fun σ _ => ?_) fun _ _ => rfl
  rw [forall_even_cycleType_iff]
  simp only [oddPoints, Finset.not_nonempty_iff_eq_empty, filter_eq_empty_iff, mem_univ,
    true_implies, Nat.not_odd_iff_even]

/-- An alternating matrix (`Aᵀ = -A` with zero diagonal) of odd order has determinant `0`: every
permutation with only even cycles moves an even number of points, so it fixes some point. -/
theorem det_eq_zero_of_transpose_eq_neg_of_odd {A : Matrix α α R} (hA : Aᵀ = -A)
    (hdiag : ∀ i, A i i = 0) (hα : Odd (Fintype.card α)) : A.det = 0 := by
  rw [det_eq_sum_even_cycleType_of_transpose_eq_neg hA]
  refine sum_eq_zero fun σ hσ => ?_
  rw [mem_filter] at hσ
  have hsupp : #σ.support ≠ Fintype.card α := by
    intro h
    have heven : 2 ∣ σ.cycleType.sum :=
      Multiset.dvd_sum fun n hn => even_iff_two_dvd.1 (hσ.2 n hn)
    rw [sum_cycleType, h] at heven
    exact Nat.not_even_iff_odd.2 hα (even_iff_two_dvd.2 heven)
  obtain ⟨x, hx⟩ : ∃ x, σ x = x := by
    by_contra! hall
    refine hsupp ?_
    rw [← card_univ, eq_univ_of_forall fun x => mem_support.2 (hall x)]
  rw [prod_eq_zero (mem_univ x) (by rw [hx, hdiag]), smul_zero]

end Matrix
