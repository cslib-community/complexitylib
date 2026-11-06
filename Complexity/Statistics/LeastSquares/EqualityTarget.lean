/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Stability
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-!
# Equality targets and normal-equation decision oracles

The external algorithm used in [XuGaoHu2027], Corollary 3.4(iii), decides a
normal-equation equality target, including singular weighted designs. The local
stability uses a nonsingular inequality target. This module derives the bridge
in the high-retained-mass regime, rather than identifying these problems by
definition. Exact real-valued output and threshold decisions are distinct APIs.
-/

public section

namespace Cslib.LeastSquares

open Matrix Set

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

/-- Feasible normal equations for an equality target and a deletion threshold.
The coefficient witness need not be unique; singular designs are permitted,
as in the fractional decision problem of Moitra and Rohatgi. -/
@[expose] def EqualityNormalDecision (x : ι → d → ℝ) (y : ι → ℝ)
    (e : d → ℝ) (θ k : ℝ) : Prop :=
  ∃ (w : ι → ℝ) (b : d → ℝ), (∀ i, w i ∈ Icc (0 : ℝ) 1) ∧
    (∑ i, w i • ((y i - x i ⬝ᵥ b) • x i)) = 0 ∧ e ⬝ᵥ b = θ ∧
      (Fintype.card ι : ℝ) - ∑ i, w i ≤ k

/-- A feasible inequality target can be moved toward the full data until the
target is an equality, without decreasing mass. The full-data target must be
strictly violated. General position supplies positive definiteness along the
entire segment from its mass lower bound. -/
theorem exists_equal_target (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w)
    (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i)
    (hfull : θ < e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1)) :
    ∃ v, Feasible x y e θ v ∧
      e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y v = θ ∧ (∑ i, w i) ≤ ∑ i, v i := by
  let v : ℝ → ι → ℝ := fun t i => w i + t * (1 - w i)
  have hbox (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ∀ i, v t i ∈ Icc (0 : ℝ) 1 := by
    intro i
    have hwi := hw.1 i
    dsimp only [v]
    constructor
    · nlinarith [hwi.1, mul_nonneg ht.1 (sub_nonneg.mpr hwi.2)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hwi.2)]
  have hge (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (∑ i, w i) ≤ ∑ i, v t i := by
    apply Finset.sum_le_sum
    intro i _
    dsimp only [v]
    exact le_add_of_nonneg_right (mul_nonneg ht.1 (sub_nonneg.mpr (hw.1 i).2))
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (weightedGram 0 Finset.univ x (v t)).PosDef :=
    hgp.weightedGram_posDef x (v t) (hbox t ht) (hmass.trans_le (hge t ht))
  have hc : ContinuousOn (fun t => e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (v t)) (Icc 0 1) := by
    intro t ht
    have hv : Continuous (fun t : ℝ => v t) := by unfold v; fun_prop
    have hb := (continuousAt_weightedEstimate x y (v t) (hG t ht)).comp hv.continuousAt
    exact ((continuous_const.dotProduct continuous_id).continuousAt.comp hb).continuousWithinAt
  have hv0 : v 0 = w := by ext i; simp [v]
  have hv1 : v 1 = fun _ => 1 := by ext i; simp [v]
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
    ⟨by simpa only [hv0] using hw.2.2, by simpa only [hv1] using hfull.le⟩
  exact ⟨v t, ⟨hbox t ht, hG t ht, heq.le⟩, heq, hge t ht⟩

/-- A normal-equation solution at mass above `d - 1` is the unique inverse-matrix
fit in general position. This derives nonsingularity instead of assuming that
the external solver rejected singular designs. -/
theorem estimate_eq_of_normal (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y w : ι → ℝ) (b : d → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1)
    (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i)
    (hn : (∑ i, w i • ((y i - x i ⬝ᵥ b) • x i)) = 0) :
    weightedEstimate 0 0 Finset.univ x y w = b := by
  have hG := hgp.weightedGram_posDef x w hw hmass
  apply hG.mulVec_injective
  rw [weightedEstimate, mulVec_mulVec,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hG.isUnit), one_mulVec]
  have heq : (∑ i, (w i * y i) • x i) = ∑ i, w i • ((x i ⬝ᵥ b) • x i) := by
    simpa only [sub_smul, smul_sub, mul_smul, Finset.sum_sub_distrib, sub_eq_zero] using hn
  simpa only [weightedResponse, weightedGram, zero_add, sum_mulVec,
    smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul] using heq

/-- The external equality-normal-equation decision and local fractional threshold
agree when the queried mass remains above the singular regime. Attainment is
derived from a supplied high-mass feasible input. -/
theorem equalityNormalDecision_iff (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w) (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i)
    (hfull : θ < e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1))
    (k : ℝ) (hk : k ≤ Fintype.card ι - Fintype.card d) :
    EqualityNormalDecision x y e θ k ↔ fractionalStability x y e θ ≤ k := by
  constructor
  · rintro ⟨v, b, hv, hn, hb, hdel⟩
    have hm : (Fintype.card d : ℝ) - 1 < ∑ i, v i := by linarith
    have heq := estimate_eq_of_normal x hgp y v b hv hm hn
    have hf : Feasible x y e θ v :=
      ⟨hv, hgp.weightedGram_posDef x v hv hm, by rw [heq, hb]⟩
    exact (fractionalStability_le x y e θ v hf).trans hdel
  · intro hle
    obtain ⟨u, hu, hopt⟩ := fractionalStability_attained x hgp y e θ w hw hmass
    have hleu := fractionalStability_le x y e θ w hw
    have hmu : (Fintype.card d : ℝ) - 1 < ∑ i, u i := by rw [hopt] at hleu; linarith
    obtain ⟨v, hv, heq, hmv⟩ := exists_equal_target x hgp y e θ u hu hmu hfull
    refine ⟨v, weightedEstimate 0 0 Finset.univ x y v, hv.1,
      weightedEstimate_normal x y v hv.2.1, heq, ?_⟩
    rw [hopt] at hle
    linarith

end Cslib.LeastSquares
