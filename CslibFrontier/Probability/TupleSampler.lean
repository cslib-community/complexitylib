/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.BigOperators
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform tuples as samplers

A uniformly random tuple `b : ι → U` samples every `[0, 1]`-valued function `F` on `U` well: the
sum `∑ i, F (b i)` falls to half its expectation for at most an `exp (-μ #ι / 8)` fraction of the
tuples, where `μ` is a lower bound on the mean of `F`
(`Cslib.Probability.card_filter_sum_le_half_le_exp`). This is the multiplicative Chernoff bound
`Cslib.Probability.PMF.pi_sum_le_one_sub_mul` at relative deviation `1 / 2`, stated by counting.

Two consequences describe the bipartite graph joining each point `x : U` to each pair `(b, i)` with
`b i = x`, restricted to a family `W` of tuples.

* **Edges into a dense family** (`Cslib.Probability.sub_mul_le_two_mul_sum_sum`): summing
  `F` over the entries of the tuples in `W` gives at least
  `(#W - #U ^ #ι exp (-μ #ι / 8)) μ #ι / 2`.
* **Regrouping by points** (`Cslib.Probability.sum_sum_comp_eq_sum_nsmul`): the same sum, over
  the positions in any set `s`, is `∑ x, d x • F x`, where `d x` counts the pairs `(b, i)` with
  `b ∈ W`, `i ∈ s` and `b i = x`; `Cslib.Probability.sum_sum_comp_eq_sum_mul` is the real form over
  all positions.

Resampling one coordinate of a uniform tuple at a uniform value leaves it uniform, so drawing a
point and planting it at a fixed coordinate of a uniform tuple is the same as drawing a uniform
tuple and reading the point off that coordinate
(`Cslib.Probability.sum_sum_update_eq_card_nsmul_sum`). In terms of the decoder of
[Impagliazzo, Jaiswal, Kabanets and Wigderson][ImpagliazzoJaiswalKabanetsWigderson2010] (preprint
numbering), with uniform tuples as the library form of their `k`-sets: the lower tail is the
one-sided part of their Lemma 2.12 sampler property (their Definition 2.9 also bounds the upper
deviation, which is not proved here), and the weight bound is of the type of their Lemma 2.13.
Their Lemma 2.14 is not proved here. The decoder module
(`CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.DirectProduct.Decode`) uses
the weight bound and the regrouping over the free positions to prove its analogue of their
Lemma 3.9, and does without Lemma 2.14.

## Main results

* `Cslib.Probability.card_filter_sum_le_half_le_exp`: the lower tail.
* `Cslib.Probability.sum_sum_update_eq_card_nsmul_sum`: planting a point at a coordinate.
* `Cslib.Probability.sub_mul_le_two_mul_sum_sum`: edges into a dense family.
* `Cslib.Probability.sum_sum_comp_eq_sum_nsmul`, `Cslib.Probability.sum_sum_comp_eq_sum_mul`:
  regrouping the edges by points.

## References

* [R. Impagliazzo, R. Jaiswal, V. Kabanets and A. Wigderson, *Uniform Direct Product Theorems:
  Simplified, Optimized, and Derandomized*][ImpagliazzoJaiswalKabanetsWigderson2010]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*, Section 4.2][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.Probability

open Finset

variable {U ι : Type*} [Fintype U] [Fintype ι]

/-- **The lower tail for uniform tuples**: if `F` takes values in `[0, 1]` and has mean at least
`μ`, at most an `exp (-μ #ι / 8)` fraction of the tuples `b : ι → U` have
`∑ i, F (b i) ≤ μ #ι / 2`. -/
theorem card_filter_sum_le_half_le_exp [DecidableEq ι] [Nonempty U] (F : U → ℝ)
    (hF : ∀ x, F x ∈ Set.Icc 0 1) {μ : ℝ} (hμ : μ * Fintype.card U ≤ ∑ x, F x) :
    (#{b : ι → U | ∑ i, F (b i) ≤ μ * Fintype.card ι / 2} : ℝ) ≤
      Fintype.card U ^ Fintype.card ι * Real.exp (-(μ * Fintype.card ι / 8)) := by
  classical
  have hU : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hmean : μ * Fintype.card ι ≤
      ∑ _i : ι, ∑ a, ((PMF.uniformOfFintype U) a).toReal * F a := by
    have hrow : ∑ a, ((PMF.uniformOfFintype U) a).toReal * F a =
        (Fintype.card U : ℝ)⁻¹ * ∑ a, F a := by
      simp [mul_sum]
    have hμ' : μ ≤ (Fintype.card U : ℝ)⁻¹ * ∑ a, F a := by
      rw [le_inv_mul_iff₀ hU, mul_comm]
      exact hμ
    rw [sum_const, card_univ, nsmul_eq_mul, hrow, mul_comm μ]
    exact mul_le_mul_of_nonneg_left hμ' (Nat.cast_nonneg _)
  have hch := PMF.pi_sum_le_one_sub_mul (fun _ : ι => PMF.uniformOfFintype U) (fun _ => F)
    (fun _ a _ => hF a) hmean (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [PMF.pi_uniformOfFintype, PMF.toOuterMeasure_uniformOfFintype_toReal,
    Fintype.card_fun] at hch
  have hpos : (0 : ℝ) < (Fintype.card U : ℝ) ^ Fintype.card ι := by positivity
  rw [div_le_iff₀ (by exact_mod_cast hpos)] at hch
  have hset : #{x : ι → U | x ∈ {outcome : ι → U |
      ∑ i, F (outcome i) ≤ (1 - 1 / 2) * (μ * Fintype.card ι)}} =
      #{b : ι → U | ∑ i, F (b i) ≤ μ * Fintype.card ι / 2} := by
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset] at hch
  calc (#{b : ι → U | ∑ i, F (b i) ≤ μ * Fintype.card ι / 2} : ℝ)
      ≤ Real.exp (-((1 / 2) ^ 2 * (μ * Fintype.card ι) / 2)) *
          ((Fintype.card U : ℝ) ^ Fintype.card ι) := by exact_mod_cast hch
    _ = Fintype.card U ^ Fintype.card ι * Real.exp (-(μ * Fintype.card ι / 8)) := by
        rw [mul_comm]
        congr 2
        ring

/-- **Planting a point**: summing over a point `x` and a tuple `r` with `x` written at coordinate
`j` counts every tuple `b` once for each value `r j` it overwrote, with `x = b j`. -/
theorem sum_sum_update_eq_card_nsmul_sum [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    (j : ι) (H : U → (ι → U) → M) :
    ∑ x, ∑ r : ι → U, H x (Function.update r j x) =
      Fintype.card U • ∑ b : ι → U, H (b j) b := by
  classical
  let e : U × (ι → U) ≃ (ι → U) × U :=
    { toFun := fun p => (Function.update p.2 j p.1, p.2 j)
      invFun := fun q => (q.1 j, Function.update q.1 j q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  rw [← Fintype.sum_prod_type', ← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [e, Equiv.coe_fn_symm_mk, Function.update_eq_self, Function.update_idem]
  rw [sum_comm, sum_const, card_univ]

/-- **Edges into a dense family**: if `F` takes values in `[0, 1]` and has mean at least `μ`, the
entries of the tuples in any family `W` carry total weight at least
`(#W - #U ^ #ι exp (-μ #ι / 8)) μ #ι / 2`. -/
theorem sub_mul_le_two_mul_sum_sum [Nonempty U] (F : U → ℝ)
    (hF : ∀ x, F x ∈ Set.Icc 0 1) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ * Fintype.card U ≤ ∑ x, F x)
    (W : Finset (ι → U)) :
    ((#W : ℝ) - Fintype.card U ^ Fintype.card ι * Real.exp (-(μ * Fintype.card ι / 8))) *
        (μ * Fintype.card ι) ≤ 2 * ∑ b ∈ W, ∑ i, F (b i) := by
  classical
  set t : ℝ := μ * Fintype.card ι with ht
  have ht0 : 0 ≤ t := by positivity
  set bad := W.filter fun b => ∑ i, F (b i) ≤ t / 2
  have hbad : (#bad : ℝ) ≤ Fintype.card U ^ Fintype.card ι * Real.exp (-(t / 8)) := by
    refine le_trans ?_ (card_filter_sum_le_half_le_exp F hF hμ)
    exact_mod_cast card_le_card fun b hb => by
      simp only [bad, mem_filter] at hb
      simpa using hb.2
  have hgood : ((#W : ℝ) - #bad) * (t / 2) ≤ ∑ b ∈ W, ∑ i, F (b i) := by
    rw [← sum_filter_add_sum_filter_not W fun b => ∑ i, F (b i) ≤ t / 2]
    have hnn : 0 ≤ ∑ b ∈ W.filter (fun b => ∑ i, F (b i) ≤ t / 2), ∑ i, F (b i) :=
      sum_nonneg fun b _ => sum_nonneg fun i _ => (hF _).1
    have hcard : (#W : ℝ) - #bad = #(W.filter fun b => ¬∑ i, F (b i) ≤ t / 2) := by
      rw [← card_filter_add_card_filter_not (s := W) (p := fun b => ∑ i, F (b i) ≤ t / 2)]
      push_cast
      ring
    have hlow : (#(W.filter fun b => ¬∑ i, F (b i) ≤ t / 2) : ℝ) * (t / 2) ≤
        ∑ b ∈ W.filter (fun b => ¬∑ i, F (b i) ≤ t / 2), ∑ i, F (b i) := by
      have h := card_nsmul_le_sum (W.filter fun b => ¬∑ i, F (b i) ≤ t / 2)
        (fun b => ∑ i, F (b i)) (t / 2) fun b hb => (not_le.1 (mem_filter.1 hb).2).le
      simpa only [nsmul_eq_mul] using h
    rw [hcard]
    linarith
  nlinarith

omit [Fintype ι] in
/-- **Regrouping by points**: summing `F` over the entries at positions `s` of the tuples in `W` is
summing `F x` weighted by the number of pairs `(b, i)` with `b ∈ W`, `i ∈ s` and `b i = x`. -/
theorem sum_sum_comp_eq_sum_nsmul [DecidableEq U] {M : Type*} [AddCommMonoid M] (F : U → M)
    (W : Finset (ι → U)) (s : Finset ι) :
    ∑ b ∈ W, ∑ i ∈ s, F (b i) = ∑ x, #((W ×ˢ s).filter fun p => p.1 p.2 = x) • F x := by
  rw [← sum_product', ← sum_fiberwise (W ×ˢ s) (fun p => p.1 p.2) fun p => F (p.1 p.2)]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_congr rfl fun p hp => by rw [(mem_filter.1 hp).2], sum_const]

/-- **Regrouping by points**, real form over all positions: summing `F` over the entries of the
tuples in `W` is summing `F x` weighted by the number of pairs `(b, i)` with `b ∈ W` and
`b i = x`. -/
theorem sum_sum_comp_eq_sum_mul [DecidableEq U] (F : U → ℝ) (W : Finset (ι → U)) :
    ∑ b ∈ W, ∑ i, F (b i) =
      ∑ x, (#((W ×ˢ (univ : Finset ι)).filter fun p => p.1 p.2 = x) : ℝ) * F x := by
  simp only [sum_sum_comp_eq_sum_nsmul F W univ, nsmul_eq_mul]

end Cslib.Probability
