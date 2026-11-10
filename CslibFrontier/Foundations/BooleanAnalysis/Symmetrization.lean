/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Minsky–Papert symmetrization

Averaging a function on the cube over each layer of inputs of a given weight turns it into a
function of the weight. For a function of degree at most `D` this function of the weight is a
univariate polynomial of degree at most `D` [MinskyPapert1969]
(`BitString.exists_natDegree_le_eval_eq_layerAverage`): the monomial of a set `S` of `s`
coordinates is `1` on `(n - s).choose (k - s)` of the `n.choose k` inputs of weight `k`, an average
of `k.choose s / n.choose s`, and `k.choose s = k (k - 1) ⋯ (k - s + 1) / s!` is a polynomial of
degree `s` in `k`. Conversely, a univariate polynomial of degree `D` evaluated at the weight has
degree at most `D` on the cube (`BitString.eval_weight_mem_lowDegree`).

Substituting into a function of degree at most `D` a map whose output bits each have degree at most
`1` keeps the degree at most `D` (`BitString.comp_mem_lowDegree`), so restricting a function to
the cube spanned by disjoint blocks of coordinates, as in block sensitivity, and then symmetrizing
reduces questions about the degree of a Boolean function to univariate polynomials.

## Main definitions

* `Cslib.BitString.layerAverage`: the average of a function over the inputs of weight `k`.

## Main results

* `Cslib.BitString.exists_natDegree_le_eval_eq_layerAverage`: **Minsky–Papert symmetrization**.
* `Cslib.BitString.eval_weight_mem_lowDegree`: a polynomial in the weight has degree at most its
  degree.
* `Cslib.BitString.comp_mem_lowDegree`: substituting functions of degree at most `1` preserves
  degree.

## References

* [M. Minsky, S. Papert, *Perceptrons*][MinskyPapert1969]
* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Polynomial
open scoped BigOperators

section Substitution

variable {R : Type*} [CommRing R] {ι κ : Type*}

/-- **Substitution preserves degree**: if every output bit of `φ`, read in `R`, is a function of
degree at most `1`, then `f ∘ φ` has degree at most that of `f`. -/
theorem comp_mem_lowDegree {φ : (κ → Bool) → ι → Bool}
    (hφ : ∀ i, (fun y => bitVal R (φ y i)) ∈ lowDegree R κ 1) {D : ℕ} {f : (ι → Bool) → R}
    (hf : f ∈ lowDegree R ι D) : (fun y => f (φ y)) ∈ lowDegree R κ D := by
  suffices h : lowDegree R ι D ≤ (lowDegree R κ D).comap (LinearMap.funLeft R R φ) from h hf
  refine Submodule.span_le.2 ?_
  rintro _ ⟨S, hS, rfl⟩
  have h : (fun y => monomial R S (φ y)) = ∏ i ∈ S, fun y => bitVal R (φ y i) := by
    funext y
    simp [monomial, Finset.prod_apply]
  change (fun y => monomial R S (φ y)) ∈ lowDegree R κ D
  rw [h]
  exact lowDegree_mono (by simpa using hS) (prod_mem_lowDegree S fun i _ => hφ i)

/-- The weight, read in `R`, has degree at most `1`. -/
theorem weight_mem_lowDegree [Fintype ι] :
    (fun x : ι → Bool => (weight x : R)) ∈ lowDegree R ι 1 := by
  have h : (fun x : ι → Bool => (weight x : R)) = ∑ i, fun x => bitVal R (x i) := by
    funext x
    simp only [weight_eq_sum_toNat, Nat.cast_sum, Finset.sum_apply]
    exact sum_congr rfl fun i _ => by cases x i <;> simp [bitVal]
  rw [h]
  exact sum_mem_lowDegree _ fun i _ => bitVal_mem_lowDegree i

/-- A univariate polynomial evaluated at the weight has degree at most its degree on the cube. -/
theorem eval_weight_mem_lowDegree [Fintype ι] (q : R[X]) :
    (fun x : ι → Bool => q.eval (weight x : R)) ∈ lowDegree R ι q.natDegree := by
  have h : (fun x : ι → Bool => q.eval (weight x : R)) =
      ∑ j ∈ range (q.natDegree + 1), q.coeff j • (fun x : ι → Bool => (weight x : R)) ^ j := by
    funext x
    simp only [eval_eq_sum_range, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
  rw [h]
  refine sum_mem_lowDegree _ fun j hj => Submodule.smul_mem _ _ (lowDegree_mono ?_
    (pow_mem_lowDegree weight_mem_lowDegree j))
  rw [mul_one]
  exact Nat.lt_succ_iff.1 (mem_range.1 hj)

end Substitution

section Symmetrization

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The average of `f` over the inputs of weight `k`. -/
def layerAverage (f : (ι → Bool) → 𝕜) (k : ℕ) : 𝕜 :=
  𝔼 x ∈ {x : ι → Bool | weight x = k}, f x

/-- The inputs of weight `k` on which the monomial of `S` is `1` correspond to the `k`-sets of
coordinates containing `S`. -/
private theorem card_filter_weight_eq_subset (S : Finset ι) (k : ℕ) :
    #{x : ι → Bool | weight x = k ∧ ∀ i ∈ S, x i = true} =
      #((univ.powersetCard k).filter (S ⊆ ·)) := by
  refine card_nbij' (fun x => ({i | x i = true} : Finset ι)) (fun T i => decide (i ∈ T))
    (fun x hx => ?_) (fun T hT => ?_) (fun x _ => ?_) (fun T _ => ?_)
  · obtain ⟨hw, hS⟩ := by simpa using hx
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hw⟩, fun i hi => ?_⟩
    simpa using hS i hi
  · obtain ⟨hT, hST⟩ := mem_filter.1 hT
    refine mem_filter.2 ⟨mem_univ _, ?_, fun i hi => by simpa using hST hi⟩
    rw [← (mem_powersetCard.1 hT).2, weight]
    congr 1
    ext i
    simp
  · funext i
    simp
  · ext i
    simp

/-- The monomial of a set of `s` coordinates averages to `k.choose s / n.choose s` over the inputs
of weight `k ≤ n`. -/
theorem layerAverage_monomial (S : Finset ι) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    layerAverage (monomial 𝕜 S) k = (k.choose #S : 𝕜) / (Fintype.card ι).choose #S := by
  set n := Fintype.card ι
  have hsum : ∑ x ∈ {x : ι → Bool | weight x = k}, monomial 𝕜 S x =
      #((univ.powersetCard k).filter (S ⊆ ·)) := by
    rw [← card_filter_weight_eq_subset, ← filter_filter, natCast_card_filter]
    exact sum_congr rfl fun x _ => (monomial_apply S x).trans (by congr)
  rw [layerAverage, expect_eq_sum_div_card, hsum, card_filter_weight_eq]
  have hnk : (n.choose k : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hk).ne'
  rcases lt_or_ge k #S with hks | hks
  · -- no `k`-set contains `S`
    have : (univ.powersetCard k).filter (S ⊆ ·) = ∅ :=
      filter_false_of_mem fun T hT hST =>
        absurd ((card_le_card hST).trans (mem_powersetCard.1 hT).2.le) (not_le.2 hks)
    rw [this, Nat.choose_eq_zero_of_lt hks]
    simp
  · rw [card_filter_powersetCard_subset S univ k (subset_univ S) hks, card_univ]
    have hns : (n.choose #S : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos (hks.trans hk)).ne'
    rw [div_eq_div_iff hnk hns]
    exact_mod_cast (show (n - #S).choose (k - #S) * n.choose #S = k.choose #S * n.choose k by
      rw [mul_comm, ← Nat.choose_mul hks, mul_comm])

/-- **Minsky–Papert symmetrization**: the layer averages of a function of degree at most `D` are
the values at the weights of a univariate polynomial of degree at most `D`. -/
theorem exists_natDegree_le_eval_eq_layerAverage {D : ℕ} {f : (ι → Bool) → 𝕜}
    (hf : f ∈ lowDegree 𝕜 ι D) :
    ∃ q : 𝕜[X], q.natDegree ≤ D ∧
      ∀ k ≤ Fintype.card ι, q.eval (k : 𝕜) = layerAverage f k := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S, hS, rfl⟩ := hf
    refine ⟨C (((#S).factorial * (Fintype.card ι).choose #S : ℕ) : 𝕜)⁻¹ * descPochhammer 𝕜 #S,
      (natDegree_C_mul_le _ _).trans ((descPochhammer_natDegree _ _).trans_le hS), fun k hk => ?_⟩
    rw [layerAverage_monomial S hk, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    have hfac : ((#S).factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    push_cast
    field_simp
  | zero => exact ⟨0, by simp, fun k _ => by simp [layerAverage]⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp, hpf⟩ := hf
    obtain ⟨q, hq, hqg⟩ := hg
    refine ⟨p + q, natDegree_add_le_of_degree_le hp hq, fun k hk => ?_⟩
    rw [eval_add, hpf k hk, hqg k hk, layerAverage, layerAverage, layerAverage,
      ← expect_add_distrib]
    rfl
  | smul a f _ hf =>
    obtain ⟨p, hp, hpf⟩ := hf
    refine ⟨C a * p, (natDegree_C_mul_le _ _).trans hp, fun k hk => ?_⟩
    rw [eval_mul, eval_C, hpf k hk, layerAverage, layerAverage, mul_expect]
    rfl

end Symmetrization

end Cslib.BitString
