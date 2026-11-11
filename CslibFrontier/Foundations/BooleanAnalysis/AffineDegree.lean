/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.BooleanAnalysis.Mobius
import CslibFrontier.Foundations.Combinatorics.InclusionMatrix
import Mathlib.Algebra.BigOperators.Field

/-!
# Multiplying by an affine function raises the degree

Let `L x = m - ∑ᵢ cᵢ xᵢ` be an affine function on the cube `ι → Bool` with values in a field `F`,
with every coefficient `cᵢ` nonzero, where `n = card ι` and the integers `1, …, n` are nonzero in
`F`. Lemma 5.2 of [ImpagliazzoPudlakSgall1999] states that multiplying a nonzero function `r` of
degree `k` with `2k < n` by `L` raises the degree by exactly one
(`Cslib.BitString.totalDegree_affine_mul`). The degree here is the multilinear degree on the cube
(`Cslib.BitString.totalDegree`), which is the degree of the multilinear reduction of a polynomial.

The proof compares the subset Möbius coefficients of `r` and `L * r` at sets of `k + 1` elements
(`Cslib.BitString.subsetMobius_bitVal_mul`). If `L * r` had degree at most `k`, the top
coefficients `μ A` of `r`, at the sets `A` of `k` elements, would satisfy
`∑_{i ∈ B} cᵢ μ (B \ {i}) = 0` for every set `B` of `k + 1` elements. After rescaling `μ A` by
`∏_{i ∈ A} cᵢ`, this says that a weighting of the `k`-sets lies in the kernel of the transposed
inclusion matrix of `k`-sets against `(k+1)`-sets, which is zero by Gottlieb's theorem
(`Finset.eq_zero_of_sum_powersetCard_eq_zero`) since `k + (k + 1) ≤ n`.

[ImpagliazzoPudlakSgall1999] state the lemma over `ℝ`. Here it holds over every field in which
`n!` is nonzero, using the characteristic-free form of Gottlieb's theorem proved in
`CslibFrontier.Foundations.Combinatorics.InclusionMatrix`. This is a mild generalization of the
stated lemma, read off from the same proof, not a new result.

The intended client is Theorem 5.1 of [ImpagliazzoPudlakSgall1999]: with the Boolean axioms, the
subset-sum polynomial `m - ∑ᵢ cᵢ xᵢ` has no polynomial calculus refutation of degree `⌈n / 2⌉`.
The proof keeps every line of a refutation of degree `d` equal on the cube to `L * r` with
`deg r ≤ d - 1`. This lemma shows that the line `1` cannot have that form at low degree.

## Main results

* `Cslib.BitString.totalDegree_affine_mul`: Lemma 5.2 of [ImpagliazzoPudlakSgall1999].

## References

* [R. Impagliazzo, P. Pudlák, J. Sgall, *Lower bounds for the polynomial calculus and the Gröbner
  basis algorithm*][ImpagliazzoPudlakSgall1999]
* [D. H. Gottlieb, *A certain class of incidence matrices*][Gottlieb1966]
-/

public section

open Finset

namespace Cslib.BitString

variable {ι F : Type*} [Field F] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem affine_mem_lowDegree (c : ι → F) (m : F) :
    (fun x : ι → Bool => m - ∑ i, c i * bitVal F (x i)) ∈ lowDegree F ι 1 := by
  have h : (fun x : ι → Bool => m - ∑ i, c i * bitVal F (x i)) =
      (fun _ => m) - ∑ i, c i • fun x : ι → Bool => bitVal F (x i) := by
    funext x
    simp [Finset.sum_apply]
  rw [h]
  exact Submodule.sub_mem _ (const_mem_lowDegree 1 m)
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bitVal_mem_lowDegree i))

/-- The top subset Möbius coefficients of `r` vanish when `L * r` does not raise the degree. -/
private theorem subsetMobius_eq_zero_of_mem_lowDegree_mul {c : ι → F} (hc : ∀ i, c i ≠ 0)
    (m : F) {k : ℕ} (hk : 2 * k < Fintype.card ι)
    (hF : ∀ j : ℕ, 0 < j → j ≤ Fintype.card ι → (j : F) ≠ 0) {r : (ι → Bool) → F}
    (hr : r ∈ lowDegree F ι k)
    (hLr : (fun x => m - ∑ i, c i * bitVal F (x i)) * r ∈ lowDegree F ι k)
    {A : Finset ι} (hA : k ≤ #A) :
    subsetMobius (fun T => r fun i => decide (i ∈ T)) A = 0 := by
  rcases Nat.eq_or_lt_of_le hA with hA | hA
  swap
  · exact subsetMobius_eq_zero_of_mem_lowDegree hr hA
  set μ : Finset ι → F := subsetMobius (fun T => r fun i => decide (i ∈ T)) with hμ
  -- the coefficients of `L * r` at the sets of `k + 1` elements
  have key : ∀ B : Finset ι, #B = k + 1 → ∑ i ∈ B, c i * μ (B.erase i) = 0 := by
    intro B hB
    have h0 : μ B = 0 := subsetMobius_eq_zero_of_mem_lowDegree hr (by omega)
    have h1 := subsetMobius_eq_zero_of_mem_lowDegree hLr (S := B) (by omega)
    simp only [Pi.mul_apply, sub_mul, sum_mul] at h1
    rw [subsetMobius_sub, subsetMobius_const_mul, subsetMobius_sum] at h1
    simp only [mul_assoc] at h1
    simp only [subsetMobius_const_mul, subsetMobius_bitVal_mul] at h1
    rw [← hμ] at h1
    simp only [mul_ite, mul_zero] at h1
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, h0] at h1
    simp only [zero_add, mul_zero, zero_sub, neg_eq_zero] at h1
    exact h1
  -- rescaled, the top coefficients lie in the kernel of the inclusion matrix
  set a : Finset ι → F := fun A => μ A / ∏ j ∈ A, c j with ha
  have hprod : ∀ A : Finset ι, ∏ j ∈ A, c j ≠ 0 := fun A => prod_ne_zero_iff.2 fun j _ => hc j
  have hsum : ∀ B ∈ (univ : Finset ι).powersetCard (k + 1),
      ∑ A ∈ B.powersetCard k, a A = 0 := by
    intro B hB
    rw [mem_powersetCard] at hB
    have hB2 := hB.2
    have hsplit : ∑ A ∈ B.powersetCard k, a A = ∑ i ∈ B, a (B.erase i) := by
      have := sum_sum_powersetCard_erase a k B
      rw [hB2, Nat.add_sub_cancel_left, one_smul] at this
      rw [← this]
      refine sum_congr rfl fun i hi => ?_
      have hcard : #(B.erase i) = k := by rw [card_erase_of_mem hi, hB2]; rfl
      rw [← hcard, powersetCard_self, sum_singleton]
    have hterm : ∀ i ∈ B, a (B.erase i) = c i * μ (B.erase i) / ∏ j ∈ B, c j := by
      intro i hi
      rw [ha, ← mul_prod_erase B c hi, mul_div_mul_left _ _ (hc i)]
    rw [hsplit, sum_congr rfl hterm, ← sum_div, key B hB2, zero_div]
  have hzero := eq_zero_of_sum_powersetCard_eq_zero (U := (univ : Finset ι)) (t := k)
    (s := k + 1) (by omega) (by rw [card_univ]; omega) (by rw [card_univ]; exact hF) hsum A
    (mem_powersetCard.2 ⟨subset_univ A, hA.symm⟩)
  rw [ha] at hzero
  exact (div_eq_zero_iff.1 hzero).resolve_right (hprod A)

omit [DecidableEq ι] in
/-- **Lemma 5.2 of [ImpagliazzoPudlakSgall1999].** Let `L x = m - ∑ᵢ cᵢ xᵢ` with every `cᵢ` nonzero,
over a field in which `1, …, card ι` are nonzero. Multiplying a nonzero function `r` on the cube
with `2 * totalDegree r < card ι` by `L` raises its degree by exactly one. The source states the
lemma over `ℝ`, for `deg r < ⌈n/2⌉`, which is `2 * deg r < n`. -/
theorem totalDegree_affine_mul {c : ι → F} (hc : ∀ i, c i ≠ 0) (m : F)
    (hF : ∀ j : ℕ, 0 < j → j ≤ Fintype.card ι → (j : F) ≠ 0) {r : (ι → Bool) → F} (hr : r ≠ 0)
    (hk : 2 * totalDegree r < Fintype.card ι) :
    totalDegree ((fun x => m - ∑ i, c i * bitVal F (x i)) * r) = totalDegree r + 1 := by
  classical
  have hrk : r ∈ lowDegree F ι (totalDegree r) := mem_lowDegree_totalDegree r
  refine le_antisymm ?_ ?_
  · rw [add_comm]
    exact totalDegree_le_of_mem_lowDegree (mul_mem_lowDegree (affine_mem_lowDegree c m) hrk)
  · by_contra hlt
    have hLr : (fun x => m - ∑ i, c i * bitVal F (x i)) * r ∈ lowDegree F ι (totalDegree r) :=
      totalDegree_le_iff_mem_lowDegree.1 (by omega)
    have hμ : ∀ A : Finset ι, totalDegree r ≤ #A →
        subsetMobius (fun T => r fun i => decide (i ∈ T)) A = 0 :=
      fun A hA => subsetMobius_eq_zero_of_mem_lowDegree_mul hc m hk hF hrk hLr hA
    rcases Nat.eq_zero_or_pos (totalDegree r) with h0 | hpos
    · exact hr (eq_zero_of_subsetMobius_eq_zero fun S => hμ S (by omega))
    · have h := totalDegree_le_of_mem_lowDegree
        (mem_lowDegree_iff_subsetMobius_eq_zero (D := totalDegree r - 1).2
          fun S hS => hμ S (by omega))
      omega

end Cslib.BitString
