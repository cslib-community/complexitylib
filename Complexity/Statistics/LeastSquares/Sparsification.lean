/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Backbone
import Complexity.Foundations.LinearAlgebra.Box
import Mathlib.Analysis.Real.Sqrt

/-!
# Sparsification of arbitrary feasible least-squares weights

Lemma 3.2 of [XuGaoHu2027], PDF p. 6: maximize mass in the unit box
subject to the residual normal equations at the original fitted coefficient.
General position and mass above `d - 1` ensure nonsingularity of the optimizer.
No sparsity or fully retained backbone is assumed for the input weights.
-/

public section

namespace Cslib.LeastSquares

open Matrix Submodule Set

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- In general position, box weights with mass above `d - 1` have positive definite Gram matrix. -/
theorem GeneralPosition.weightedGram_posDef (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (w : ι → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i) :
    (weightedGram 0 Finset.univ x w).PosDef := by
  classical
  let s := Finset.univ.filter fun i => 0 < w i
  have hle : (∑ i, w i) ≤ (s.card : ℝ) := by
    calc
      _ = ∑ i ∈ s, w i := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        have hn : ¬ 0 < w i := by simpa [s] using hi
        exact le_antisymm (not_lt.mp hn) (hw i).1
      _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hw i).2
      _ = _ := by simp
  have hs : Fintype.card d ≤ s.card := by
    by_contra hn
    have hnat : s.card + 1 ≤ Fintype.card d := by omega
    have hcast := Nat.cast_le (α := ℝ).mpr hnat
    push_cast at hcast
    linarith
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  have hspan : span ℝ (x '' (t : Set ι)) = ⊤ := by
    have := (hgp t ht).span_eq_top_of_card_eq_finrank' (by simpa using ht)
    have heq : x '' (t : Set ι) = range (fun i : t => x i) := by
      ext v
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.property, rfl⟩
    rwa [heq]
  let z := fun i => Real.sqrt (w i) • x i
  have hzspan : span ℝ (z '' ((Finset.univ : Finset ι) : Set ι)) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hwi : 0 < w i := (Finset.mem_filter.mp (hts hi)).2
    have hzi : z i ∈ span ℝ (z '' ((Finset.univ : Finset ι) : Set ι)) :=
      subset_span ⟨i, Finset.mem_univ _, rfl⟩
    have heq : (Real.sqrt (w i))⁻¹ • z i = x i := by
      exact inv_smul_smul₀ (ne_of_gt (Real.sqrt_pos.mpr hwi)) (x i)
    rw [← heq]
    exact smul_mem _ _ hzi
  have hp := posDef_sum_vecMulVec_of_span_eq_top Finset.univ z hzspan
  convert hp using 1
  simp only [weightedGram, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  ext j k
  simp only [z, smul_vecMulVec, vecMulVec_smul, smul_smul]
  rw [Real.mul_self_sqrt (hw i).1]

/-- The actual inverse-matrix estimate solves the weighted normal equations. -/
theorem weightedEstimate_normal (x : ι → d → ℝ) (y w : ι → ℝ)
    (hG : (weightedGram 0 Finset.univ x w).PosDef) :
    ∑ i, w i • ((y i - x i ⬝ᵥ weightedEstimate 0 0 Finset.univ x y w) • x i) = 0 := by
  have h : weightedGram 0 Finset.univ x w *ᵥ weightedEstimate 0 0 Finset.univ x y w =
      weightedResponse 0 Finset.univ x y w := by
    rw [weightedEstimate, mulVec_mulVec,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG.isUnit), one_mulVec]
  simp only [weightedGram, weightedResponse, zero_add, sum_mulVec, smul_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, ← mul_smul] at h
  simp only [sub_smul, smul_sub, ← mul_smul, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr h.symm

/-- Positive definiteness makes every normal-equation solution the actual
inverse-matrix fit. No general-position or retained-mass hypothesis is needed. -/
theorem weightedEstimate_eq_of_normal (x : ι → d → ℝ) (y w : ι → ℝ) (b : d → ℝ)
    (hG : (weightedGram 0 Finset.univ x w).PosDef)
    (hn : (∑ i, w i • ((y i - x i ⬝ᵥ b) • x i)) = 0) :
    weightedEstimate 0 0 Finset.univ x y w = b := by
  apply hG.mulVec_injective
  rw [weightedEstimate, mulVec_mulVec,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG.isUnit), one_mulVec]
  have heq : (∑ i, (w i * y i) • x i) = ∑ i, w i • ((x i ⬝ᵥ b) • x i) := by
    simpa only [sub_smul, smul_sub, mul_smul, Finset.sum_sub_distrib, sub_eq_zero] using hn
  simpa only [weightedResponse, weightedGram, zero_add, sum_mulVec,
    smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul] using heq

/-- Lemma 3.2: arbitrary feasible box weights can be replaced by weights of at least
as much mass, with exactly the same fitted coefficient vector and at most `d`
fractional coordinates. Feasibility for every linear target is thus preserved. -/
theorem exists_sparse_weights (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y w : ι → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i) :
    ∃ u : ι → ℝ, (∀ i, u i ∈ Icc (0 : ℝ) 1) ∧
      (∑ i, w i) ≤ ∑ i, u i ∧
      (Finset.univ.filter fun i => 0 < u i ∧ u i < 1).card ≤ Fintype.card d ∧
      weightedEstimate 0 0 Finset.univ x y u = weightedEstimate 0 0 Finset.univ x y w ∧
      (weightedGram 0 Finset.univ x u).PosDef := by
  classical
  let b := weightedEstimate 0 0 Finset.univ x y w
  let a := fun i => (y i - x i ⬝ᵥ b) • x i
  obtain ⟨u, hu, heq, hmassu, hcount⟩ := exists_sparse_box_solution a w hw
  have hG := hgp.weightedGram_posDef x u hu (hmass.trans_le hmassu)
  refine ⟨u, hu, hmassu, ?_, ?_, hG⟩
  · simpa only [Fintype.card_subtype, Finset.card_univ] using hcount
  · have hnormal : ∑ i, u i • a i = 0 :=
      heq.trans (weightedEstimate_normal x y w (hgp.weightedGram_posDef x w hw hmass))
    apply hG.mulVec_injective
    rw [weightedEstimate, mulVec_mulVec,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG.isUnit), one_mulVec]
    have hn : (∑ i, (u i * y i) • x i) =
        ∑ i, u i • ((x i ⬝ᵥ b) • x i) := by
      simpa only [a, sub_smul, smul_sub, mul_smul, Finset.sum_sub_distrib,
        sub_eq_zero] using hnormal
    simpa only [weightedResponse, weightedGram, zero_add, sum_mulVec,
      smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul] using hn

/-- Theorem 3.3's rounding conclusion for any input weights of mass at least `2d`.
The input need not be sparse; Lemma 3.2 supplies the sparse weights internally. -/
theorem exists_round [Nonempty d] (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y w : ι → ℝ) (e : d → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    ∃ u : ι → ℝ, (∀ i, u i = 0 ∨ u i = 1) ∧
      e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y u ≤
        e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y w ∧
      (∑ i, w i) - (∑ i, u i) < Fintype.card d ∧
      (weightedGram 0 Finset.univ x u).PosDef := by
  have hd := Fintype.card_pos (α := d)
  obtain ⟨v, hv, hmv, hcv, hev, _⟩ := exists_sparse_weights x hgp y w hw (by
    have : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr hd
    linarith)
  obtain ⟨u, hu, _, he, hm, hG⟩ := exists_round_sparse x hgp Finset.univ y v e hd
    (fun i _ => hv i) hcv (hmass.trans hmv)
  refine ⟨u, fun i => hu i (Finset.mem_univ i), ?_, ?_, hG⟩
  · rwa [hev] at he
  · linarith

end Cslib.LeastSquares
