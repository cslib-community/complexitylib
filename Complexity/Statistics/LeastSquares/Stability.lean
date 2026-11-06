/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Sparsification
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

/-!
# Attainment and stability bounds for least-squares audits

Theorem 3.3 and Corollary 3.4 of [XuGaoHu2027], PDF pp. 6–7.
Feasibility includes positive definiteness and an arbitrary linear inequality target.
The fractional infimum is attained when the supremal retained mass exceeds `d - 1`.
The rounding theorem starts with arbitrary feasible weights, rather than sparse input.
The external fractional solver and its running time are not formalized here.
-/

public section

namespace Cslib.LeastSquares

open Matrix Set

variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]

/-- Feasibility for an inequality target, with nonsingularity required explicitly. -/
@[expose] def Feasible (x : ι → d → ℝ) (y : ι → ℝ) (e : d → ℝ)
    (θ : ℝ) (w : ι → ℝ) : Prop :=
  (∀ i, w i ∈ Icc (0 : ℝ) 1) ∧ (weightedGram 0 Finset.univ x w).PosDef ∧
    e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y w ≤ θ

/-- Fractional stability: infimal deleted mass among all feasible real box weights. -/
@[expose] noncomputable def fractionalStability (x : ι → d → ℝ) (y : ι → ℝ)
    (e : d → ℝ) (θ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ w, Feasible x y e θ w ∧ r = Fintype.card ι - ∑ i, w i}

open Classical in
/-- Integral stability: the fewest deletions among feasible retained subsets.
As usual for a natural infimum, the empty feasible set has value zero; results
about stability below include hypotheses ensuring nonempty feasibility. -/
@[expose] noncomputable def integralStability (x : ι → d → ℝ) (y : ι → ℝ)
    (e : d → ℝ) (θ : ℝ) : ℕ :=
  sInf {k : ℕ | ∃ s : Finset ι,
    Feasible x y e θ (fun i => if i ∈ s then 1 else 0) ∧ k = Fintype.card ι - s.card}

private theorem mass_le_card (w : ι → ℝ) (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) :
    (∑ i, w i) ≤ Fintype.card ι := by
  simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ => (1 : ℝ)) (fun i _ => (hw i).2)

private theorem deleted_bddBelow (x : ι → d → ℝ) (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) :
    BddBelow {r : ℝ | ∃ w, Feasible x y e θ w ∧ r = Fintype.card ι - ∑ i, w i} := by
  refine ⟨0, ?_⟩
  rintro r ⟨w, hw, rfl⟩
  linarith [mass_le_card w hw.1]

/-- Every feasible weight vector bounds fractional stability from above. -/
theorem fractionalStability_le (x : ι → d → ℝ) (y : ι → ℝ) (e : d → ℝ) (θ : ℝ)
    (w : ι → ℝ) (hw : Feasible x y e θ w) :
    fractionalStability x y e θ ≤ Fintype.card ι - ∑ i, w i :=
  csInf_le (deleted_bddBelow x y e θ) ⟨w, hw, rfl⟩

/-- Fractional stability is nonnegative when feasibility is nonempty. -/
theorem fractionalStability_nonneg (x : ι → d → ℝ) (y : ι → ℝ) (e : d → ℝ) (θ : ℝ)
    (hne : ∃ w, Feasible x y e θ w) : 0 ≤ fractionalStability x y e θ := by
  obtain ⟨w, hw⟩ := hne
  apply le_csInf (show {r : ℝ | ∃ v, Feasible x y e θ v ∧
    r = Fintype.card ι - ∑ i, v i}.Nonempty from ⟨_, w, hw, rfl⟩)
  rintro r ⟨v, hv, rfl⟩
  linarith [mass_le_card v hv.1]

/-- The inverse-matrix estimator is continuous at every positive definite design. -/
theorem continuousAt_weightedEstimate (x : ι → d → ℝ) (y w : ι → ℝ)
    (hG : (weightedGram 0 Finset.univ x w).PosDef) :
    ContinuousAt (fun u : ι → ℝ => weightedEstimate 0 0 Finset.univ x y u) w := by
  have hGc : Continuous (fun u : ι → ℝ => weightedGram 0 Finset.univ x u) := by
    unfold weightedGram
    fun_prop
  have hinv : ContinuousAt (fun u : ι → ℝ => (weightedGram 0 Finset.univ x u)⁻¹) w := by
    apply (continuousAt_matrix_inv _ ?_).comp hGc.continuousAt
    simp only [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀
      (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hG.isUnit))
  have hresp : Continuous (fun u : ι → ℝ => weightedResponse 0 Finset.univ x y u) := by
    unfold weightedResponse
    fun_prop
  exact (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
    (hinv.prodMk hresp.continuousAt)

/-- Attainment whenever some feasible point has mass above `d - 1`. The optimizer
is global over all feasible weights, including those outside the compact slice. -/
theorem exists_max_mass (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w)
    (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i) :
    ∃ u, Feasible x y e θ u ∧ ∀ v, Feasible x y e θ v → (∑ i, v i) ≤ ∑ i, u i := by
  let K := {u : ι → ℝ | (∀ i, u i ∈ Icc (0 : ℝ) 1) ∧ (∑ i, w i) ≤ ∑ i, u i}
  have hK : IsCompact K := by
    have heq : K = Icc (0 : ι → ℝ) 1 ∩ {u : ι → ℝ | (∑ i, w i) ≤ ∑ i, u i} := by
      ext u
      simp only [K, mem_ofPred_eq, mem_inter_iff, mem_Icc, Pi.le_def]
      aesop
    rw [heq]
    exact isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))
  have hcont : ContinuousOn (fun u : ι → ℝ => e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y u) K := by
    intro u hu
    have hc := continuousAt_weightedEstimate x y u
      (hgp.weightedGram_posDef x u hu.1 (hmass.trans_le hu.2))
    have ht : ContinuousAt (fun u : ι → ℝ => e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y u) u :=
      (continuous_const.dotProduct continuous_id).continuousAt.comp hc
    exact ht.continuousWithinAt
  let L := K ∩ (fun u : ι → ℝ => e ⬝ᵥ weightedEstimate 0 0 Finset.univ x y u) ⁻¹' Iic θ
  have hL : IsCompact L := hK.of_isClosed_subset
    (hcont.preimage_isClosed_of_isClosed hK.isClosed isClosed_Iic) inter_subset_left
  have hmasscont : Continuous (fun u : ι → ℝ => ∑ i, u i) := by fun_prop
  obtain ⟨u, hu, hmax⟩ := hL.exists_isMaxOn ⟨w, ⟨hw.1, le_rfl⟩, hw.2.2⟩
    hmasscont.continuousOn
  have hfu : Feasible x y e θ u :=
    ⟨hu.1.1, hgp.weightedGram_posDef x u hu.1.1 (hmass.trans_le hu.1.2), hu.2⟩
  refine ⟨u, hfu, fun v hv => ?_⟩
  by_cases hm : (∑ i, w i) ≤ ∑ i, v i
  · exact hmax ⟨⟨hv.1, hm⟩, hv.2.2⟩
  · exact (not_le.mp hm).le.trans hu.1.2

/-- The fractional infimum is attained under the retained-mass hypothesis. -/
theorem fractionalStability_attained (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w) (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i) :
    ∃ u, Feasible x y e θ u ∧
      fractionalStability x y e θ = Fintype.card ι - ∑ i, u i := by
  obtain ⟨u, hu, hmax⟩ := exists_max_mass x hgp y e θ w hw hmass
  refine ⟨u, hu, le_antisymm (fractionalStability_le x y e θ u hu) ?_⟩
  apply le_csInf (show {r : ℝ | ∃ w, Feasible x y e θ w ∧
    r = Fintype.card ι - ∑ i, w i}.Nonempty from ⟨_, w, hw, rfl⟩)
  rintro r ⟨v, hv, rfl⟩
  linarith [hmax v hv]

/-- The more general attainment criterion in Theorem 3.3. Nonempty feasibility is
explicit, since the real infimum of the empty set does not encode infeasibility. -/
theorem fractionalStability_attained_of_gap (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ)
    (hne : ∃ w, Feasible x y e θ w)
    (hgap : (Fintype.card d : ℝ) - 1 < Fintype.card ι - fractionalStability x y e θ) :
    ∃ u, Feasible x y e θ u ∧
      fractionalStability x y e θ = Fintype.card ι - ∑ i, u i := by
  have hD : {r : ℝ | ∃ w, Feasible x y e θ w ∧ r = Fintype.card ι - ∑ i, w i}.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨_, w, hw, rfl⟩
  obtain ⟨r, ⟨w, hw, hr⟩, hlt⟩ := exists_lt_of_csInf_lt hD
    (show fractionalStability x y e θ < Fintype.card ι - ((Fintype.card d : ℝ) - 1) by linarith)
  exact fractionalStability_attained x hgp y e θ w hw (by linarith)

open Classical in
/-- Attainment can be chosen sparse, with no sparsity premise on the feasible set. -/
theorem fractionalStability_attained_sparse (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w) (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i) :
    ∃ u, Feasible x y e θ u ∧
      fractionalStability x y e θ = Fintype.card ι - ∑ i, u i ∧
      (Finset.univ.filter fun i => 0 < u i ∧ u i < 1).card ≤ Fintype.card d := by
  obtain ⟨v, hv, hmax⟩ := exists_max_mass x hgp y e θ w hw hmass
  obtain ⟨u, hu, hmu, hcu, heu, hGu⟩ := exists_sparse_weights x hgp y v hv.1
    (hmass.trans_le (hmax w hw))
  have hfu : Feasible x y e θ u := ⟨hu, hGu, by rw [heu]; exact hv.2.2⟩
  refine ⟨u, hfu, le_antisymm (fractionalStability_le x y e θ u hfu) ?_, hcu⟩
  apply le_csInf (show {r : ℝ | ∃ v, Feasible x y e θ v ∧
    r = Fintype.card ι - ∑ i, v i}.Nonempty from ⟨_, w, hw, rfl⟩)
  rintro r ⟨z, hz, rfl⟩
  linarith [hmax z hz]

open Classical in
/-- Rounding produces an actual retained subset, preserving feasibility and losing
strictly less than `d` mass from the arbitrary input. -/
theorem exists_round_subset [Nonempty d] (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w) (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    ∃ s : Finset ι, Feasible x y e θ (fun i => if i ∈ s then 1 else 0) ∧
      (∑ i, w i) - (s.card : ℝ) < Fintype.card d := by
  classical
  obtain ⟨u, hu, he, hm, hG⟩ := exists_round x hgp y w e hw.1 hmass
  let s := Finset.univ.filter fun i => u i = 1
  have heq : u = (fun i => if i ∈ s then 1 else 0) := by
    ext i
    rcases hu i with h | h <;> simp [s, h]
  have hsum : (∑ i, u i) = (s.card : ℝ) := by
    rw [heq]
    simp
  refine ⟨s, ?_, ?_⟩
  · rw [← heq]
    exact ⟨fun i => by rcases hu i with h | h <;> simp [h], hG, he.trans hw.2.2⟩
  · rwa [hsum] at hm

/-- Theorem 3.3: attained fractional stability and the strict additive integral gap
for arbitrary linear inequality targets in general position. -/
theorem stability_bounds [Nonempty d] (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w) (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    (∃ u, Feasible x y e θ u ∧
      fractionalStability x y e θ = Fintype.card ι - ∑ i, u i) ∧
    fractionalStability x y e θ ≤ (integralStability x y e θ : ℝ) ∧
    (integralStability x y e θ : ℝ) < fractionalStability x y e θ + Fintype.card d := by
  classical
  have hd : (0 : ℝ) < Fintype.card d := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨u, hu, hmax⟩ := exists_max_mass x hgp y e θ w hw (by linarith)
  have hfrac : fractionalStability x y e θ = Fintype.card ι - ∑ i, u i := by
    apply le_antisymm (fractionalStability_le x y e θ u hu)
    apply le_csInf (show {r : ℝ | ∃ v, Feasible x y e θ v ∧
      r = Fintype.card ι - ∑ i, v i}.Nonempty from ⟨_, w, hw, rfl⟩)
    rintro r ⟨v, hv, rfl⟩
    linarith [hmax v hv]
  obtain ⟨s, hs, hloss⟩ := exists_round_subset x hgp y e θ u hu (hmass.trans (hmax w hw))
  let D := {k : ℕ | ∃ s : Finset ι,
    Feasible x y e θ (fun i => if i ∈ s then 1 else 0) ∧ k = Fintype.card ι - s.card}
  have hD : D.Nonempty := ⟨_, s, hs, rfl⟩
  obtain ⟨t, ht, hmin⟩ := Nat.sInf_mem hD
  have htcard : t.card ≤ Fintype.card ι := Finset.card_le_univ _
  have hscard : s.card ≤ Fintype.card ι := Finset.card_le_univ _
  have hminle : integralStability x y e θ ≤ Fintype.card ι - s.card :=
    Nat.sInf_le (show Fintype.card ι - s.card ∈ D from ⟨s, hs, rfl⟩)
  have htval : (integralStability x y e θ : ℝ) = Fintype.card ι - (t.card : ℝ) := by
    change ((sInf D : ℕ) : ℝ) = _
    rw [hmin, Nat.cast_sub htcard]
  refine ⟨⟨u, hu, hfrac⟩, ?_, ?_⟩
  · have h := fractionalStability_le x y e θ _ ht
    simpa only [htval, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one] using h
  · have hcast : (integralStability x y e θ : ℝ) ≤ Fintype.card ι - (s.card : ℝ) := by
      have := Nat.cast_le (α := ℝ).mpr hminle
      rwa [Nat.cast_sub hscard] at this
    rw [hfrac]
    linarith

/-- Corollary 3.4: the integral optimum is one of `d` consecutive integers whose
first element is the ceiling of the fractional optimum. -/
theorem stability_ceiling_bounds [Nonempty d] (x : ι → d → ℝ) (hgp : GeneralPosition x)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w) (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    ⌈fractionalStability x y e θ⌉₊ ≤ integralStability x y e θ ∧
      integralStability x y e θ ≤ ⌈fractionalStability x y e θ⌉₊ + Fintype.card d - 1 := by
  obtain ⟨_, hlo, hhi⟩ := stability_bounds x hgp y e θ w hw hmass
  refine ⟨Nat.ceil_le.mpr hlo, ?_⟩
  have hlt : (integralStability x y e θ : ℝ) <
      (⌈fractionalStability x y e θ⌉₊ : ℝ) + Fintype.card d :=
    hhi.trans_le (add_le_add (Nat.le_ceil _) le_rfl)
  have hnat : integralStability x y e θ < ⌈fractionalStability x y e θ⌉₊ + Fintype.card d := by
    exact_mod_cast hlt
  omega

/-- In dimension one, integral stability equals the ceiling of fractional stability. -/
theorem integralStability_eq_ceil_of_card_eq_one [Nonempty d]
    (x : ι → d → ℝ) (hgp : GeneralPosition x) (hd : Fintype.card d = 1)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w) (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    integralStability x y e θ = ⌈fractionalStability x y e θ⌉₊ := by
  obtain ⟨hlo, hhi⟩ := stability_ceiling_bounds x hgp y e θ w hw hmass
  omega

/-- In dimension two (including simple regression with an intercept), only the
ceiling and its successor can be the integral optimum. -/
theorem integralStability_eq_ceil_or_succ [Nonempty d]
    (x : ι → d → ℝ) (hgp : GeneralPosition x) (hd : Fintype.card d = 2)
    (y : ι → ℝ) (e : d → ℝ) (θ : ℝ) (w : ι → ℝ)
    (hw : Feasible x y e θ w) (hmass : 2 * (Fintype.card d : ℝ) ≤ ∑ i, w i) :
    integralStability x y e θ = ⌈fractionalStability x y e θ⌉₊ ∨
      integralStability x y e θ = ⌈fractionalStability x y e θ⌉₊ + 1 := by
  obtain ⟨hlo, hhi⟩ := stability_ceiling_bounds x hgp y e θ w hw hmass
  omega

end Cslib.LeastSquares
