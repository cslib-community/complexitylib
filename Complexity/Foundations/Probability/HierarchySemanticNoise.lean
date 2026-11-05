/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyGatedNoise

/-!
# Canonical semantic boundary sampling

Genuine canonical ranges and the terminal-vertex charge sum pay semantic groups
with unchanged production steps. Positive and exhausted endpoints stay distinct.
The denominator, joint retained densities and complete prefix cube remain literal.
These original bounds do not pay the final prefix reserve or recursive availability.
The unfiltered product range is used; no approximate canonical support, error
independence, or centered-noise rarity is assumed. Horizon normalization uses
`1 ≤ P ^ 4 * rate ka`, not the false first-power comparison.

## Main results

* `residualCanonicalRay_abs_le_charge`: genuine direct/product and final correction ranges.
* `residualSemantic_centered_relative_fourth_le`: retained-pair moment with constant 65536.
* `rawRelativeNoiseBudget_semantic_le`: unchanged production spectral payment.
* `rawRelativeNoiseBudget_residual_le_of_gates`: combined actual input budget.
-/

public section
noncomputable section
open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Genuine canonical rays have their production per-vertex range. The negative
correction uses the actual final canonical child; no recursive history is supplied. -/
theorem residualCanonicalRay_abs_le_charge
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ)
    (ht : r.terminal.rate = rate ka) (bin : Option ℕ) (σ : Environment P 3) (x y : ZMod P) :
    |B.residualCanonicalRay r bin σ x y| ≤
      match bin with
      | some i => B.positiveCharge r i y
      | none => rate ka * B.atomCap := by
  cases bin with
  | some i =>
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)
    exact B.rawPositiveSample_abs_le_positiveCharge r i
      (fun q => B.residualCanonicalChild i q σ) x y
      (B.residualCanonicalChild_dense_abs_le i Q.direct _ _ rfl σ x y)
      (fun z => B.residualCanonicalChild_correction_abs_le i Q.left rfl σ x z)
      (fun z => B.residualCanonicalChild_dense_abs_le i Q.right _ _ rfl σ z y)
  | none =>
    let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
    have hu : q.usage.rate = rate ka := by simp [q, midpoint, ht]
    have hr : HierarchyTask.usageRatio (channels B.padding) r.terminal q y = 1 := by
      rw [usageRatio_grid B.padding r.terminal q ka ka ht hu y]
      exact div_self (gridMass_pos (P := P) ka).ne'
    have hc := B.residualCanonicalChild_correction_abs_le 0 q rfl σ x y
    simp only [residualCanonicalRay, Pi.neg_apply, HierarchyTask.rawNegativeSample,
      HierarchyTask.rawRequests]
    change |-((midpoint r).rate * HierarchyTask.usageRatio (channels B.padding)
      r.terminal q y * B.residualCanonicalChild 0 q σ x y)| ≤ _
    rw [hr]
    simp only [midpoint, ht, mul_one, abs_neg, abs_mul, abs_of_pos (rate_pos ka)]
    exact mul_le_mul_of_nonneg_left hc (rate_pos ka).le

/-- Both literal endpoint references are bounded, including active/exhausted boundaries. -/
theorem residualSemanticGroupInput_abs_le_magnitude_div
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ)
    (ht : r.terminal.rate = rate ka) (hi : ∀ i ∈ B.bins, B.binRate i = rate i) :
    ∀ σ x y, |B.residualSemanticGroupInput M d r σ x y| ≤
      2 * B.magnitude r / P := by
  let charge : Option ℕ → ℝ := fun bin => match bin with
    | some i => B.positiveCharge r i 0
    | none => rate ka * B.atomCap
  have hc (bin : Option ℕ) : 0 ≤ charge bin := by
    cases bin with
    | some i => exact B.positiveCharge_nonneg r i 0
    | none => exact mul_nonneg (rate_pos ka).le (by
        unfold atomCap; exact mul_nonneg (by norm_num) (HP.Q_nonneg _))
  let E := fun m bin σ x y =>
    if m = 0 then 0 else B.residualCanonicalRay r bin σ x y
  have he (bin : Option ℕ) (hb : bin ∈ B.rays .residual) (m : ℕ)
      (σ x y) : |E m bin σ x y| ≤ 2 * charge bin := by
    by_cases hz : m = 0
    · simp only [E, hz, ↓reduceIte, abs_zero]
      exact mul_nonneg (by norm_num) (hc bin)
    · have hh := B.residualCanonicalRay_abs_le_charge r ka ht bin σ x y
      cases bin with
      | none => simpa only [E, hz, ↓reduceIte, charge] using hh.trans (by
          change rate ka * B.atomCap ≤ 2 * (rate ka * B.atomCap)
          linarith only [hc none])
      | some b =>
        have hbin : b ∈ B.bins := by
          simpa only [rays, List.mem_append, List.mem_map, mem_toList, List.mem_singleton,
            Option.some.injEq, Option.some_ne_none, or_false, exists_eq_right] using hb
        dsimp only at hh
        rw [B.positiveCharge_grid_const r ka b ht (hi b hbin)] at hh
        simpa only [E, hz, ↓reduceIte, charge] using hh.trans (by
          change charge (some b) ≤ 2 * charge (some b)
          linarith only [hc (some b)])
  have hsum : ((B.rays .residual).map charge).sum =
      (∑ i ∈ B.bins, B.positiveCharge r i 0) + rate ka * B.atomCap := by
    simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def, charge]
    rw [sum_map_toList]
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  intro σ x y
  change |((B.rays .residual).map (fun bin =>
    E (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) bin σ x y -
    E (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) bin σ x y)).sum| ≤ _
  have hbound : ∀ bin ∈ B.rays .residual,
      |E (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) bin σ x y -
       E (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) bin σ x y| ≤
      4 * charge bin := by
    intro bin hb
    exact (abs_sub _ _).trans (by
      linarith only [
        he bin hb (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) σ x y,
        he bin hb (LogSpaceEstimation.lastBudget M (2 * d) B.slack
          (B.sampleScale r bin)) σ x y])
  have hconvert (v : Option ℕ → ℝ) :
      ((B.rays .residual).map v).sum = ∑ bin ∈ insert none (B.bins.image some), v bin := by
    rw [sum_insert (by simp), sum_image (fun _ _ _ _ h => Option.some.inj h)]
    simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
    rw [sum_map_toList]; ring
  rw [hconvert]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ bin ∈ insert none (B.bins.image some), 4 * charge bin := by
      apply sum_le_sum
      intro bin hb
      apply hbound
      simpa only [rays, List.mem_append, List.mem_map, mem_toList, List.mem_singleton,
        mem_insert, mem_image, eq_comm, or_comm] using hb
    _ = 4 * ((∑ i ∈ B.bins, B.positiveCharge r i 0) + rate ka * B.atomCap) := by
      rw [← mul_sum, ← hconvert, hsum]
    _ ≤ _ := by
      apply (le_div_iff₀ hP).mpr
      have hm := B.magnitude_grid_eq r ka ht hi
      have ha : 0 ≤ B.atomCap := by
        unfold atomCap; exact mul_nonneg (by norm_num) (HP.Q_nonneg _)
      nlinarith only [hm, ha]

/-- The semantic moment is proved from genuine ranges and actual joint grid density.
The real residual remains inside the denominator; no support minimum is needed. -/
theorem residualSemantic_centered_relative_fourth_le
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (ht : r.terminal.rate = rate ka) (hrate : ∀ i ∈ B.bins, B.binRate i = rate i)
    (H : Horizon P) (hs : ks ≤ H.maxExponent) (ha : ka ≤ H.maxExponent)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    let X := NormalizedMoments.retainedMask s (side P ks) B.padding ss
    let Y := NormalizedMoments.retainedMask t (side P ka) B.padding st
    rowNormPow 4 P (rate ks) X Y
      (fun σ x y => (B.residualSemanticGroupInput M d r σ x y -
        rowSliceMean X Y (B.residualSemanticGroupInput M d r) x y) / (rate ka + G x y)) ≤
      65536 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3) :=
  B.residualTransported_centered_relative_fourth_le_of_abs s t hst ks ka ss st H hs ha
    r _ G hG (B.residualSemanticGroupInput_abs_le_magnitude_div M d r ka ht hrate)

/-- Semantic boundary payment with explicit constant 64 and eighth-power decay.
No semantic moment, history availability, or child accuracy is assumed. -/
theorem rawRelativeNoiseBudget_semantic_le
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal.rate = rate ka) (hks : ka ≤ ks)
    (hrate : ∀ i ∈ B.bins, B.binRate i = rate i)
    (H : Horizon P) (hsource : ks ≤ H.maxExponent)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (j : ℕ) :
    B.rawRelativeNoiseBudget M r s t hst ks ka ss st
      (fun i => B.residualSemanticGroupInput M
        (dyadicSlack (Nat.log2 M + 1) i) r) G j ≤
      (j : ℝ) ^ 3 * ∑ i ∈ range j,
        64 * (((2 : ℝ) ^ (-B.requestPrecision M r)) *
          (64 : ℝ)⁻¹ ^ dyadicSlack (Nat.log2 M + 1) i) ^ 8 := by
  let ρ : ℝ := 1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)
  have hρ : 0 ≤ ρ := by norm_num [ρ]
  let cost := 65536 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3)
  have hcost : 0 ≤ cost := by
    dsimp only [cost]
    exact div_nonneg (by positivity)
      (mul_nonneg (by positivity) (pow_nonneg (rate_pos ka).le _))
  have hbound := B.rawRelativeNoiseBudget_le_of_centered_fourth M r s t hst ks ka ss st
    hs (fun i => B.residualSemanticGroupInput M
      (dyadicSlack (Nat.log2 M + 1) i) r) G j (fun _ => cost) (by
        intro i _
        rw [show r.source.rate = rate ks by rw [hs]; rfl]
        exact B.residualSemantic_centered_relative_fourth_le M _ r s t hst ks ka ss st
          ht hrate H hsource (hks.trans hsource) G hG)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro i _
  let d := dyadicSlack (Nat.log2 M + 1) i
  have hw : ‖fun xy : ZMod P × ZMod P => 2 *
      (graph s t hst (side P ks) (side P ka) (side_le P ks) (side_le P ka)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding st)
        xy.1 xy.2).spectralExpansion ^ (2 * B.steps M r d)‖ ≤
      2 * ρ ^ (2 * B.steps M r d) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro xy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg (RotationMap.spectralExpansion_nonneg _) _))]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (RotationMap.spectralExpansion_nonneg _)
    unfold graph
    rw [RotationMap.spectralExpansion_reindex, RotationMap.spectralExpansion_reindex]
    exact spectralExpansion_lazy_ofPerms_componentMove_le (by decide)
  apply (mul_le_mul_of_nonneg_right hw hcost).trans
  have hh := B.transported_range_spectral_payment M d r ks ka
    (by rw [hs]; rfl) hks H (hks.trans hsource)
  convert hh using 1
  dsimp only [cost]
  ring

/-- Every semantic endpoint is literally zero after complete budget exhaustion. -/
theorem residualSemanticGroupInput_eq_zero_of_le (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hd : M ≤ d) :
    B.residualSemanticGroupInput M d r = 0 := by
  have hf (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hc (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  funext σ x y
  simp [residualSemanticGroupInput, hf, hc]

/-- Actual production input payment combines the proved semantic and transported
budgets. The factor sixteen includes the correlated split; the prefix reserve
is displayed in full rather than replaced by an assumed uniform allowance. -/
theorem rawRelativeNoiseBudget_residual_le_of_gates
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal.rate = rate ka) (hks : ka ≤ ks)
    (hrate : ∀ i ∈ B.bins, B.binRate i = rate i)
    (H : Horizon P) (hsource : ks ≤ H.maxExponent)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (j : ℕ)
    (hg : ∀ i ∈ range j, ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) i)
          B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) i)
          B.slack (B.sampleScale r bin)) → B.ResidualEndpointGates history m r bin) :
    B.rawRelativeNoiseBudget M r s t hst ks ka ss st
      (fun i => B.decodedGroupInput history M
        (dyadicSlack (Nat.log2 M + 1) i) .residual r) G j ≤
      16 * ((j : ℝ) ^ 3 * ∑ i ∈ range j,
        64 * (((2 : ℝ) ^ (-B.requestPrecision M r)) *
          (64 : ℝ)⁻¹ ^ dyadicSlack (Nat.log2 M + 1) i) ^ 8) := by
  have hS := B.rawRelativeNoiseBudget_semantic_le M r s t hst ks ka ss st hs ht hks
    hrate H hsource G hG j
  have hT := B.rawRelativeNoiseGroup_transported_le_of_gates history M r s t hst
    ks ka ss st hs ht hks hrate H hsource G hG j hg
  have hsplit := B.rawRelativeNoiseBudget_residual_split_le history M r s t hst
    ks ka ss st hs G j
  linarith only [hS, hT, hsplit]

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
