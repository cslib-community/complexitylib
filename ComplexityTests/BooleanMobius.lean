/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.Mobius
import Mathlib.Algebra.Field.ZMod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Concrete Boolean Möbius sums, including polynomials depending on the original assignment.
The numeric left-hand sums are kernel-computed independently of the reconstruction theorem.
-/

open scoped BigOperators
open Finset MvPolynomial Cslib.BitString

namespace BooleanMobiusTests

private theorem cube_two_sum {A : Type*} [AddCommMonoid A]
    (s : Finset (Fin 2 → Bool)) (f : (Fin 2 → Bool) → A) (hs : ∀ x, x ∈ s) :
    (∑ x ∈ s, f x) =
      f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  have hsuniv : s = univ := Finset.eq_univ_iff_forall.mpr hs
  rw [hsuniv, ← (finTwoArrowEquiv Bool).symm.sum_comp f]
  change (∑ b : Bool × Bool, f ![b.1, b.2]) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

private theorem cube_one_sum {A : Type*} [AddCommMonoid A]
    (s : Finset (Fin 1 → Bool)) (f : (Fin 1 → Bool) → A) (hs : ∀ x, x ∈ s) :
    (∑ x ∈ s, f x) = f (fun _ => false) + f (fun _ => true) := by
  have hsuniv : s = univ := Finset.eq_univ_iff_forall.mpr hs
  rw [hsuniv, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp f]
  change (∑ b : Bool, f (fun _ => b)) = _
  simp only [Fintype.sum_bool]
  exact add_comm _ _

private noncomputable def subsetSum {ι A : Type*} [Fintype ι] [CommRing A]
    (q : ℕ) (p : (ι → Bool) → MvPolynomial ι A) : A := by
  classical
  exact ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
    ∑ U ∈ E.powerset, (-1 : A) ^ (#E - #U) *
      ∑ x ∈ (univ : Finset (ι → Bool)).filter (fun x => ∀ i ∈ E, x i = true),
        MvPolynomial.eval (fun i => bitVal A (decide (i ∈ U))) (p x)

open Classical in
private theorem subsetSum_eq {ι A : Type*} [Fintype ι] [CommRing A]
    (q : ℕ) (p : (ι → Bool) → MvPolynomial ι A) (hp : ∀ x, (p x).totalDegree ≤ q) :
    subsetSum q p = ∑ x : ι → Bool, MvPolynomial.eval (fun i => bitVal A (x i)) (p x) :=
  (sum_eval_eq_restricted_subsets q p hp).symm

-- The polynomial, not just its evaluation point, changes with x. The answer is 3+3+0+1.
private noncomputable def dependentFamily (x : Fin 2 → Bool) : MvPolynomial (Fin 2) ℤ :=
  if x 0 then X 1 else C 3

-- Assignment-dependent polynomials, degree-0 families on `Fin 2` and `Fin 0`, degree bounds
-- exceeding dimension, characteristic-2 cancellation, trivial ring `ZMod 1`, and truncation loss
-- when the degree bound is violated.
example :
    subsetSum 1 dependentFamily = 7 ∧
      subsetSum 0 (fun x : Fin 2 → Bool => C (if x 0 then (-2 : ℤ) else 3)) = 2 ∧
      subsetSum 0 (fun _ : Fin 0 → Bool => C (-7 : ℤ)) = -7 ∧
      subsetSum 5 (fun _ : Fin 1 → Bool => (X 0 : MvPolynomial (Fin 1) ℤ) ^ 3) = 1 ∧
      subsetSum 1 (fun x : Fin 2 → Bool =>
        if x 0 then (X 1 : MvPolynomial (Fin 2) (ZMod 2)) else 0) = 1 ∧
      subsetSum 0 (fun _ : Fin 1 → Bool => (0 : MvPolynomial (Fin 1) (ZMod 1))) = 0 ∧
      (∑ x : Fin 1 → Bool,
        MvPolynomial.eval (fun i => bitVal ℤ (x i)) (X 0 : MvPolynomial (Fin 1) ℤ)) = 1 ∧
      subsetSum 0 (fun _ : Fin 1 → Bool => (X 0 : MvPolynomial (Fin 1) ℤ)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [subsetSum_eq]
    · simp only [dependentFamily, apply_ite, MvPolynomial.eval_X, MvPolynomial.eval_C]
      rw [cube_two_sum]
      · decide +kernel
      · intro x; simp
    · intro x
      unfold dependentFamily
      split_ifs <;> simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] <;> decide
  · rw [subsetSum_eq]
    · simp only [MvPolynomial.eval_C]
      rw [cube_two_sum]
      · decide +kernel
      · intro x; simp
    · intro x
      simp only [MvPolynomial.totalDegree_C, Nat.le_refl]
  · rw [subsetSum_eq]
    · simp only [MvPolynomial.eval_C]
      decide +kernel
    · intro x
      simp only [MvPolynomial.totalDegree_C, Nat.le_refl]
  · rw [subsetSum_eq]
    · simp only [map_pow, MvPolynomial.eval_X]
      rw [cube_one_sum]
      · decide +kernel
      · intro x; simp
    · intro x
      simp only [MvPolynomial.totalDegree_X_pow]
      decide
  · rw [subsetSum_eq]
    · simp only [apply_ite, MvPolynomial.eval_X, map_zero]
      rw [cube_two_sum]
      · decide +kernel
      · intro x; simp
    · intro x
      split_ifs <;> simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_zero] <;> decide
  · rw [subsetSum_eq]
    · simp only [map_zero, sum_const_zero]
    · intro x
      simp only [MvPolynomial.totalDegree_zero, Nat.le_refl]
  · simp only [MvPolynomial.eval_X]
    rw [cube_one_sum]
    · decide +kernel
    · intro x; simp
  · classical
    have hfilter : (univ : Finset (Fin 1)).powerset.filter (fun E => #E ≤ 0) = {∅} := by
      ext E
      simp only [mem_filter, mem_powerset, Nat.le_zero, card_eq_zero, mem_singleton]
      exact and_iff_right_of_imp (fun h => by simp [h])
    unfold subsetSum
    rw [hfilter]
    simp [bitVal]

end BooleanMobiusTests
