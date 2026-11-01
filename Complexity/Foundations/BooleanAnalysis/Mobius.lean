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

The Möbius transform on the subsets of a set (`Cslib.BitString.subsetMobius`) inverts subset
sums (`Cslib.BitString.sum_powerset_subsetMobius`). Applied to the values of a function on the
indicators of subsets, it gives the function's coefficient at a monomial
(`Cslib.BitString.subsetMobius_monomial`), so it vanishes above the degree
(`Cslib.BitString.subsetMobius_eq_zero_of_mem_lowDegree`). This is the subset inversion in the
proof of Lemma D.2, p. 56 of [OpenAI2026ETH].

## Main definitions

* `Cslib.BitString.subsetMobius`: `∑_{T ⊆ S} (-1) ^ (#S - #T) • f T`.

## Main results

* `Cslib.BitString.lowDegree_reconstruction`: pointwise reconstruction in the existing span.
* `Cslib.BitString.sum_eval_eq_restricted_subsets`: the assignment-dependent polynomial sum.
* `Cslib.BitString.sum_powerset_subsetMobius`: Möbius inversion on the subsets of a set.
* `Cslib.BitString.subsetMobius_eq_zero_of_mem_lowDegree`: the transform vanishes above the
  degree.
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

/-! ### The Möbius transform on the subsets of a set -/

section SubsetMobius

variable {M : Type*} [AddCommGroup M]

/-- The **Möbius transform on the subsets of `S`** of a function `f` on finite sets,
`∑_{T ⊆ S} (-1) ^ (#S - #T) • f T`. It inverts subset sums
(`Cslib.BitString.sum_powerset_subsetMobius`). When `f T` is the value of a function on the cube
at the indicator of `T`, it is the coefficient of that function at the monomial of `S`
(`Cslib.BitString.subsetMobius_monomial`). -/
@[expose] public def subsetMobius (f : Finset ι → M) (S : Finset ι) : M :=
  ∑ T ∈ S.powerset, (-1 : ℤ) ^ (#S - #T) • f T

/-- An additive map commutes with the subset Möbius transform. -/
public theorem map_subsetMobius {N : Type*} [AddCommGroup N] (φ : M →+ N) (f : Finset ι → M)
    (S : Finset ι) : φ (subsetMobius f S) = subsetMobius (fun T => φ (f T)) S := by
  simp only [subsetMobius, map_sum, map_zsmul]

/-- The subset Möbius transform is additive. -/
public theorem subsetMobius_add (f g : Finset ι → M) (S : Finset ι) :
    subsetMobius (fun T => f T + g T) S = subsetMobius f S + subsetMobius g S := by
  simp only [subsetMobius, smul_add, sum_add_distrib]

/-- The signed count of the sets between `U` and `T`. -/
private theorem sum_neg_one_pow_superset [DecidableEq ι] {U T : Finset ι} (hUT : U ⊆ T) :
    (∑ S ∈ T.powerset with U ⊆ S, (-1 : ℤ) ^ (#S - #U)) = if U = T then 1 else 0 := by
  have hbij : (∑ S ∈ T.powerset with U ⊆ S, (-1 : ℤ) ^ (#S - #U)) =
      ∑ Z ∈ (T \ U).powerset, (-1 : ℤ) ^ #Z := by
    refine sum_nbij' (fun S => S \ U) (fun Z => Z ∪ U) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powerset] at hS ⊢
      exact sdiff_subset_sdiff hS.1 subset_rfl
    · intro Z hZ
      simp only [mem_filter, mem_powerset] at hZ ⊢
      exact ⟨union_subset (hZ.trans sdiff_subset) hUT, subset_union_right⟩
    · intro S hS
      exact sdiff_union_of_subset (mem_filter.mp hS).2
    · intro Z hZ
      have hZ' : Disjoint Z U := disjoint_of_subset_left (mem_powerset.mp hZ) sdiff_disjoint
      exact union_sdiff_cancel_right hZ'
    · intro S hS
      rw [card_sdiff_of_subset (mem_filter.mp hS).2]
  rw [hbij, sum_powerset_neg_one_pow_card]
  by_cases h : U = T
  · simp [h]
  · have hne : T \ U ≠ ∅ := fun he => h (hUT.antisymm (sdiff_eq_empty_iff_subset.mp he))
    simp only [h, hne, ↓reduceIte]

/-- **Möbius inversion on the subsets of a set**: summing the subset Möbius transform of `f` over
the subsets of `T` gives back `f T`. -/
public theorem sum_powerset_subsetMobius (f : Finset ι → M) (T : Finset ι) :
    ∑ S ∈ T.powerset, subsetMobius f S = f T := by
  classical
  simp only [subsetMobius]
  rw [sum_comm' (t' := T.powerset) (s' := fun U => T.powerset.filter (U ⊆ ·))]
  · simp_rw [← sum_smul]
    rw [sum_eq_single T]
    · rw [sum_neg_one_pow_superset subset_rfl, ite_eq_left rfl, one_smul]
    · intro U hU hUT
      rw [sum_neg_one_pow_superset (mem_powerset.mp hU), ite_eq_right hUT, zero_smul]
    · intro h
      exact absurd (mem_powerset_self T) h
  · intro S U
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => h.1⟩

/-- **The subset Möbius transform of a monomial**: at the indicators of subsets, the monomial of
`U` has transform `1` at `U` and `0` at every other set. -/
public theorem subsetMobius_monomial [DecidableEq ι] (U S : Finset ι) :
    subsetMobius (fun T => monomial R U fun i => decide (i ∈ T)) S = if U = S then 1 else 0 := by
  convert subset_kernel (R := R) U S using 1
  · rw [subsetMobius]
    refine sum_congr rfl fun T _ => ?_
    rw [monomial_apply, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    congr 1
    simp only [decide_eq_true_eq]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd (fun i hi => h₁ i hi) h₂
    · exact absurd (fun i hi => h₂ hi) h₁
    · rfl
  · split_ifs <;> rfl

/-- **The subset Möbius transform vanishes above the degree**: for a function of degree at most
`D`, the transform of its values at the indicators of subsets vanishes at every set of more than
`D` elements. -/
public theorem subsetMobius_eq_zero_of_mem_lowDegree [DecidableEq ι] {D : ℕ}
    {f : (ι → Bool) → R} (hf : f ∈ lowDegree R ι D) {S : Finset ι} (hS : D < #S) :
    subsetMobius (fun T => f fun i => decide (i ∈ T)) S = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨U, hU, rfl⟩ := hg
    have hU' : #U ≤ D := hU
    rw [subsetMobius_monomial, ite_eq_right]
    rintro rfl
    omega
  | zero => simp only [Pi.zero_apply, subsetMobius, smul_zero, sum_const_zero]
  | add g h _ _ hg hh => simp only [Pi.add_apply, subsetMobius_add, hg, hh, add_zero]
  | smul c g _ hg =>
    have h := map_subsetMobius (AddMonoidHom.mulLeft c) (fun T => g fun i => decide (i ∈ T)) S
    simp only [AddMonoidHom.coe_mulLeft, hg, mul_zero] at h
    simpa only [Pi.smul_apply, smul_eq_mul] using h.symm

end SubsetMobius

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
