/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Pi

/-!
# Boolean Möbius reconstruction

A polynomial of degree at most `q`, evaluated at a Boolean assignment, is reconstructed from
its values on subsets of at most `q` coordinates. Summing this identity permits the polynomial
to depend on the original assignment. Coefficients may lie in any commutative ring.

The proof uses the existing Boolean low-degree span; it introduces no multilinear polynomial
representation. It follows Lemma 3.3, equation (3.10), p24 of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH].

## Main results

* `Cslib.BitString.lowDegree_reconstruction`: pointwise reconstruction in the existing span.
* `Cslib.BitString.sum_eval_eq_restricted_subsets`: the assignment-dependent polynomial sum.
-/

open scoped BigOperators
open Finset

namespace Cslib.BitString

variable {ι R : Type*} [CommRing R]

open Classical in
private theorem subset_kernel (S E : Finset ι) :
    (∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) * (if S ⊆ U then 1 else 0)) =
      if S = E then 1 else 0 := by
  classical
  by_cases hSE : S ⊆ E
  · have hbij :
        (∑ U ∈ E.powerset.filter (S ⊆ ·), (-1 : R) ^ (#E - #U)) =
          ∑ Z ∈ (E \ S).powerset, (-1 : R) ^ #Z := by
      refine sum_bij (fun U _ => E \ U) ?_ ?_ ?_ ?_
      · intro U hU
        exact mem_powerset.mpr (Finset.sdiff_subset_sdiff_right E (mem_filter.mp hU).2)
      · intro U hU V hV h
        have hU' := mem_powerset.mp (mem_filter.mp hU).1
        have hV' := mem_powerset.mp (mem_filter.mp hV).1
        simpa [Finset.sdiff_sdiff_eq_self hU', Finset.sdiff_sdiff_eq_self hV'] using
          congrArg (E \ ·) h
      · intro Z hZ
        have hZE := (mem_powerset.mp hZ).trans sdiff_subset
        refine ⟨E \ Z, mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, ?_⟩,
          Finset.sdiff_sdiff_eq_self hZE⟩
        intro i hi
        refine mem_sdiff.mpr ⟨hSE hi, ?_⟩
        intro hiZ
        exact (mem_sdiff.mp (mem_powerset.mp hZ hiZ)).2 hi
      · intro U hU
        rw [card_sdiff_of_subset (mem_powerset.mp (mem_filter.mp hU).1)]
    have hcancel : (∑ Z ∈ (E \ S).powerset, (-1 : R) ^ #Z) =
        if E \ S = ∅ then 1 else 0 := by
      have h := congrArg (Int.castRingHom R)
        (sum_powerset_neg_one_pow_card (x := E \ S))
      simp only [map_sum, map_pow, map_neg, map_one] at h
      split_ifs at h ⊢ <;> simpa using h
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter, hbij, hcancel]
    congr 1
    exact propext ⟨fun h => hSE.antisymm (sdiff_eq_empty_iff_subset.mp h),
      fun h => by simp [h]⟩
  · have hnone : ∀ U ∈ E.powerset, ¬S ⊆ U := fun U hU hSU =>
        hSE (hSU.trans (mem_powerset.mp hU))
    have hne : S ≠ E := by
      rintro rfl
      exact hSE (Subset.refl _)
    simp only [ite_eq_right hne]
    exact sum_eq_zero fun U hU => by simp [hnone U hU]

open Classical in
private noncomputable def reconstruction [Fintype ι] (q : ℕ) (x : ι → Bool) :
    ((ι → Bool) → R) →ₗ[R] R :=
  ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
    if ∀ i ∈ E, x i = true then
      ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) •
        (LinearMap.proj (fun i => decide (i ∈ U)) : ((ι → Bool) → R) →ₗ[R] R)
    else 0

open Classical in
private theorem reconstruction_apply [Fintype ι] (q : ℕ) (x : ι → Bool)
    (f : (ι → Bool) → R) :
    reconstruction q x f =
      ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
        if ∀ i ∈ E, x i = true then
          ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) * f (fun i => decide (i ∈ U))
        else 0 := by
  unfold reconstruction
  simp only [LinearMap.sum_apply]
  apply sum_congr rfl
  intro E _
  split_ifs <;> simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, LinearMap.zero_apply]

open Classical in
private theorem reconstruction_monomial [Fintype ι] (q : ℕ) (x : ι → Bool)
    (S : Finset ι) (hS : #S ≤ q) :
    reconstruction q x (monomial R S) = monomial R S x := by
  rw [reconstruction_apply]
  simp_rw [monomial_apply, decide_eq_true_eq, ← Finset.subset_iff, subset_kernel]
  rw [sum_eq_single S]
  · simp
  · intro E _ hES
    simp [Ne.symm hES]
  · simp [hS]

open Classical in
/-- A low-degree function on the cube is reconstructed from its subset evaluations. -/
public theorem lowDegree_reconstruction [Fintype ι] {q : ℕ} {f : (ι → Bool) → R}
    (hf : f ∈ lowDegree R ι q) (x : ι → Bool) :
    f x = ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
      if ∀ i ∈ E, x i = true then
        ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) * f (fun i => decide (i ∈ U))
      else 0 := by
  rw [← reconstruction_apply]
  refine Submodule.span_induction (p := fun f _ => f x = reconstruction q x f) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S, hS, rfl⟩
    exact (reconstruction_monomial q x S hS).symm
  · simp
  · intro f g _ _ hf hg
    simp only [Pi.add_apply, map_add, hf, hg]
  · intro c f _ hf
    simp only [Pi.smul_apply, map_smul, hf]

private theorem aeval_bit_apply (p : MvPolynomial ι R) (x : ι → Bool) :
    (MvPolynomial.aeval (fun i (y : ι → Bool) => bitVal R (y i)) p) x =
      MvPolynomial.eval (fun i => bitVal R (x i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => simp only [map_add, Pi.add_apply, hp, hr]
  | mul_X p i hp => simp only [map_mul, Pi.mul_apply, MvPolynomial.aeval_X,
      MvPolynomial.eval_X, hp]

private theorem polynomial_mem_lowDegree (p : MvPolynomial ι R) {q : ℕ}
    (hp : p.totalDegree ≤ q) :
    (fun x : ι → Bool => MvPolynomial.eval (fun i => bitVal R (x i)) p) ∈ lowDegree R ι q := by
  rw [lowDegree_eq_map_restrictTotalDegree]
  refine ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hp, ?_⟩
  funext x
  exact aeval_bit_apply p x

open Classical in
/-- Boolean Möbius reconstruction for an assignment-dependent polynomial family, over any
commutative ring (Lemma 3.3, equation (3.10) of the cited manuscript). The polynomial evaluated
at `1_U` is still `p x`, indexed by the original assignment in the restricted inner sum. -/
public theorem sum_eval_eq_restricted_subsets [Fintype ι] (q : ℕ)
    (p : (ι → Bool) → MvPolynomial ι R) (hp : ∀ x, (p x).totalDegree ≤ q) :
    (∑ x : ι → Bool, MvPolynomial.eval (fun i => bitVal R (x i)) (p x)) =
      ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
        ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) *
          ∑ x ∈ (univ : Finset (ι → Bool)).filter (fun x => ∀ i ∈ E, x i = true),
            MvPolynomial.eval (fun i => bitVal R (decide (i ∈ U))) (p x) := by
  calc
    _ = ∑ x : ι → Bool,
        ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
          if ∀ i ∈ E, x i = true then
            ∑ U ∈ E.powerset, (-1 : R) ^ (#E - #U) *
              MvPolynomial.eval (fun i => bitVal R (decide (i ∈ U))) (p x)
          else 0 := by
      apply sum_congr rfl
      intro x _
      exact lowDegree_reconstruction (polynomial_mem_lowDegree (p x) (hp x)) x
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro E _
      rw [← sum_filter, sum_comm]
      apply sum_congr rfl
      intro U _
      rw [mul_sum]

end Cslib.BitString
