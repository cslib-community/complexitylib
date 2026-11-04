/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Ryser's Boolean-sum formula for the permanent

Ryser's inclusion–exclusion identity expresses the permanent as a signed sum over Boolean
column selectors [Schauz, Theorem 1.2, p. 3][Schauz2006]. The sign is the product of `1` for each
selected column and `-1` for each unselected column. Each summand multiplies the selected row
sums. The proof works over every commutative ring, including characteristic two and the zero
ring; Schauz's section-wide convention is an integral domain of characteristic zero.

The proof expands the row product into a sum over all functions from rows to columns. Summing
the signs cancels every nonsurjective function. On a finite square matrix, the surviving
functions are exactly the permutations. The empty matrix has permanent `1` and contributes
one empty Boolean assignment.

## Main results

* `Matrix.permanent_eq_ryser_bool`: Ryser's formula as a sum over `ι → Bool`.

## References

* [U. Schauz, *Colorings and orientations of matrices and graphs*][Schauz2006], Theorem 1.2

The proof is adapted from the saved Complexitylib development at revision `5b8acca7`.
-/

@[expose] public section

namespace Matrix

open Equiv Equiv.Perm Finset Fintype

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- Boolean-indicator form of Ryser's inclusion–exclusion formula for the permanent
[Schauz, Theorem 1.2, p. 3][Schauz2006], generalized to every commutative ring. -/
theorem permanent_eq_ryser_bool (A : Matrix n n R) :
    A.permanent =
      ∑ e : n → Bool,
        (∏ j : n, if e j then (1 : R) else -1) *
          ∏ i : n, ∑ j : n, if e j then A i j else 0 := by
  have hprod (e : n → Bool) :
      (∏ i : n, ∑ j : n, if e j then A i j else 0) =
        ∑ f : n → n, (if ∀ i, e (f i) = true then (1 : R) else 0) * ∏ i : n, A i (f i) := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with hf
    · rw [one_mul]
      exact Finset.prod_congr rfl fun i _ => by simp [hf i]
    · rw [zero_mul]
      push Not at hf
      obtain ⟨i, hi⟩ := hf
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hstep1 :
      (∑ e : n → Bool,
        (∏ j : n, if e j then (1 : R) else -1) *
          ∏ i : n, ∑ j : n, if e j then A i j else 0) =
      ∑ f : n → n,
        (∑ e : n → Bool,
          (∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) *
          ∏ i : n, A i (f i) := by
    calc _ = ∑ e : n → Bool, ∑ f : n → n,
          ((∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) * ∏ i : n, A i (f i) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [hprod e, Finset.mul_sum]
          exact Finset.sum_congr rfl fun f _ => (mul_assoc _ _ _).symm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun f _ => (Finset.sum_mul _ _ _).symm
  rw [hstep1]
  have hfactor (f : n → n) (e : n → Bool) :
      (∏ j : n, if e j then (1 : R) else -1) *
          (if ∀ i, e (f i) = true then (1 : R) else 0) =
        ∏ j : n, if e j then (1 : R) else if j ∈ univ.image f then 0 else -1 := by
    split_ifs with hf
    · rw [mul_one]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hej : e j = true
      · simp [hej]
      · have hj : j ∉ univ.image f := by
          intro hmem
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
          exact hej (hf i)
        simp [hej, hj]
    · rw [mul_zero]
      push Not at hf
      obtain ⟨i, hi⟩ := hf
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ (f i)) ?_
      have hmem : f i ∈ univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ i)
      simp [hi, hmem]
  have hsum_e (f : n → n) :
      (∑ e : n → Bool,
          (∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) =
        if Function.Surjective f then (1 : R) else 0 := by
    simp_rw [hfactor]
    rw [← Fintype.prod_sum (fun (j : n) (b : Bool) =>
      if b = true then (1 : R) else if j ∈ univ.image f then 0 else -1)]
    have h1 (j : n) :
        (∑ b : Bool, if b = true then (1 : R) else if j ∈ univ.image f then 0 else -1) =
          if j ∈ univ.image f then (1 : R) else 0 := by
      rw [Fintype.sum_bool]
      by_cases hj : j ∈ univ.image f <;> simp [hj]
    simp_rw [h1]
    split_ifs with hsurj
    · refine Finset.prod_eq_one fun j _ => ?_
      obtain ⟨i, rfl⟩ := hsurj j
      have hmem : f i ∈ univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ i)
      simp [hmem]
    · unfold Function.Surjective at hsurj
      push Not at hsurj
      obtain ⟨j, hj⟩ := hsurj
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      have hj' : j ∉ univ.image f := by simpa using hj
      simp [hj']
  have hstep2 :
      (∑ f : n → n,
        (∑ e : n → Bool,
          (∏ j : n, if e j then (1 : R) else -1) *
            (if ∀ i, e (f i) = true then (1 : R) else 0)) *
          ∏ i : n, A i (f i)) =
      ∑ f : n → n, (if Function.Surjective f then (1 : R) else 0) * ∏ i : n, A i (f i) :=
    Finset.sum_congr rfl fun f _ => by rw [hsum_e f]
  rw [hstep2, ← permanent_transpose, permanent]
  have hbij :
      (∑ σ : Perm n, ∏ i : n, Aᵀ (σ i) i) =
        ∑ f ∈ univ.filter (fun f : n → n => Function.Surjective f), ∏ i : n, A i (f i) := by
    refine Finset.sum_bij (fun (σ : Perm n) _ => (σ : n → n)) ?_ ?_ ?_ ?_
    · intro σ _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.surjective⟩
    · intro σ₁ _ σ₂ _ h
      exact DFunLike.coe_injective h
    · intro f hf
      have hsurj : Function.Surjective f := (Finset.mem_filter.mp hf).2
      exact ⟨Equiv.ofBijective f (Finite.surjective_iff_bijective.mp hsurj),
        Finset.mem_univ _, rfl⟩
    · intro σ _
      rfl
  rw [hbij, Finset.sum_filter]
  refine Finset.sum_congr rfl fun f _ => ?_
  split_ifs <;> simp

end Matrix
