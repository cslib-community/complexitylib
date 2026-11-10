/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Computability.LogSpaceDerandomization.HierarchyChildRootMoment
public import Complexity.Computability.LogSpaceDerandomization.HierarchyEstimatedMean

/-!
# Actual conditional child-cost reserves from normalized child roots

The finite reserve uses actual incoming children and genuine canonical requests.
Bounded routed cutoffs supply ranges for the normalized outputs; equality on true inputs
preserves the genuine canonical family. Root budgets are imposed on each lower request's
own full terminal rank and source, with fixed structural `HP.k`.
This original finite payment does not construct recursively accurate children.
-/
public section
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- Actual bounded normalized children pay the conditional reserve from their own rooted
row moments. Usage-to-rank transport, midpoint/reset transport and both ranges are derived.
The integrated allocation retains explicit vertex, call-count and source-rate costs. -/
theorem actual_conditionalChildCost_le_of_root_budgets
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (l ks km kt n : ℕ) (ss sm st : List (ZMod P)) (kb : ℕ → ℕ)
    (C : Matrix (ZMod P) (ZMod P) ℝ) (hC : ∀ x y, 0 ≤ C x y)
    (χ : ℝ → ℝ) (hχ : ∀ v, 1 ≤ v → χ v = 1)
    (h : ℕ → ℝ → ℝ) (ρ : ℝ → ℝ) (K : ℕ) (hρ : ∀ v, ρ v ∈ Set.Icc 0 1)
    (hχmono : Monotone χ) (hχ0 : ∀ v, v ≤ 1 / 2 → χ v = 0)
    (hχrange : ∀ v, χ v ∈ Set.Icc 0 1)
    (hanti : Antitone (fun i => rate (kb i)))
    (hratio : ∀ i, rate (kb i) / rate (kb (i + 1)) ≤ 16)
    {cap : ℝ} (hcap : 0 ≤ cap) (hCcap : ∀ x y, C x y ≤ cap * rate (kb 0))
    (Kc : ℕ)
    (raw prep : ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    let cutoff := fun i => routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1)
    let bounded := fun i => boundedRoutedBinCutoff χ (fun i => rate (kb i)) cap i (fun _ => 1)
    let source := gridChannel R.source ks ss
    let mid := gridChannel R.midpoint km sm
    let terminal := gridChannel R.terminal kt st
    let estimated := fun i σ r => incomingChildren HP D id Kc (bounded i)
      (raw i) (prep i) (maximum i) r σ
    let canonical := fun i σ r => canonicalRequestChild HP D id C (cutoff i) (h i) ρ K r σ
    let channelsV := fun role b suffix σ v => channels D role b suffix σ (id v)
    let CA := 2 * HP.Q HP.toHierarchyParams.atomCap
    let CB := 2 * max cap 16
    let B := max CA CB
    let scale := (Fintype.card (ZMod P) : ℝ) ^ 2 / ((P : ℝ) * rate ks) *
      HierarchyTask.residualCostCoefficient (k := HP.k) channelsV (range (n + 1)) l
        source mid terminal (fun i => rate (kb i)) CA CB
    (∀ i r, (i, r) ∈ HierarchyTask.residualErrorCalls (k := HP.k) (range (n + 1)) l
        source mid terminal (fun i => rate (kb i)) →
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains channelsV σ x)
        (fun σ y => r.terminal.retains channelsV σ y)
        (fun σ => estimated i σ r) (fun σ => canonical i σ r) ≤
      (δ / (1 + scale)) /
        (1 + (4 * B ^ ((3 : ℝ) / 4)) ^ 4 *
          ((P : ℝ) * r.source.rate)) /
        (1 + #(HierarchyTask.residualErrorCalls (k := HP.k) (range (n + 1)) l
          source mid terminal (fun i => rate (kb i))))) →
    rowNormPow 4 P (rate ks)
      (fun σ x => source.retains channelsV σ x) (fun σ y => terminal.retains channelsV σ y)
      (fun _ => HierarchyTask.conditionalChildCost channelsV (range (n + 1)) l source mid
        terminal (fun i => rate (kb i)) CA CB estimated canonical) ≤ δ := by
  extract_lets cutoff bounded source mid terminal estimated canonical channelsV CA CB B scale
  intro hroot
  have hCA : 0 ≤ CA := mul_nonneg (by norm_num) (HP.Q_nonneg _)
  have hCB : 0 ≤ CB := by dsimp only [CB]; positivity
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hbounded (i : ℕ) (v : ℝ) : bounded i v ∈ Set.Icc 0 (max cap 16) :=
    boundedRoutedBinCutoff_mem_Icc hcap (hcap.trans (le_max_left cap 16)) (le_max_left cap 16)
      hχmono hχ0 hχ hχrange (fun i => rate_pos (kb i)) hanti
      (fun i => (hratio i).trans (le_max_right _ _))
      (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) i v
  have hsource (i : ℕ) (r : HierarchyTask.Request HP.k (Fin J) (ZMod P))
      (hc : (i, r) ∈ HierarchyTask.residualErrorCalls (k := HP.k) (range (n + 1)) l
        source mid terminal (fun i => rate (kb i))) : 0 < r.source.rate := by
    simp only [HierarchyTask.residualErrorCalls, mem_union, mem_biUnion, mem_insert,
      mem_singleton, Prod.mk.injEq] at hc
    rcases hc with ⟨j, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, rfl⟩ <;>
      first | exact rate_pos ks | exact rate_pos km
  have hsub (i : ℕ) (r : HierarchyTask.Request HP.k (Fin J) (ZMod P))
      (hc : (i, r) ∈ HierarchyTask.residualErrorCalls (k := HP.k) (range (n + 1)) l
        source mid terminal (fun i => rate (kb i))) (σ : Environment P J) (y : ZMod P) :
      r.usage.retains channelsV σ y → r.terminal.retains channelsV σ y := by
    simp only [HierarchyTask.residualErrorCalls, mem_union, mem_biUnion, mem_insert,
      mem_singleton, Prod.mk.injEq] at hc
    rcases hc with ⟨j, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, rfl⟩
    · change coordinate D ⟨R.terminal, min (rate kt) (rate (kb i)), st⟩ _ y →
        coordinate D (gridChannel R.terminal (kb i) st) _ y
      rw [min_comm]
      exact coordinate_min_grid D R.terminal st (kb i) kt _ y
    · exact id
    · change coordinate D ⟨R.terminal, min (rate kt) (rate (kb i)), st⟩ _ y →
        coordinate D (gridChannel R.terminal (kb i) st) _ y
      rw [min_comm]
      exact coordinate_min_grid D R.terminal st (kb i) kt _ y
    · change coordinate D ⟨R.terminal, min (rate kt) (rate km), st⟩ _ y →
        coordinate D (gridChannel R.terminal km st) _ y
      rw [min_comm]
      exact coordinate_min_grid D R.terminal st km kt _ y
  have hcanon (i : ℕ) (r : HierarchyTask.Request HP.k (Fin J) (ZMod P))
      (hc : (i, r) ∈ HierarchyTask.residualErrorCalls (k := HP.k) (range (n + 1)) l
        source mid terminal (fun i => rate (kb i))) (σ : Environment P J) :
      canonical i σ r = canonicalRequestChild HP D id C (bounded i) (h i) ρ K r σ := by
    simp only [HierarchyTask.residualErrorCalls, mem_union, mem_biUnion, mem_insert,
      mem_singleton, Prod.mk.injEq] at hc
    rcases hc with ⟨j, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨rfl, rfl⟩
    · exact denseChild_congr_cutoff D id _ C _ _ (h i) ρ K
        (fun x y => (boundedRoutedBinCutoff_div_eq (fun i => rate_pos (kb i))
          (hC x y) (hCcap x y) i).symm) σ
    · simp only [canonical, HierarchyTask.rawRequests]
      rw [HierarchyTask.correctionAtomTask_last HP.k_pos]
      rfl
    · exact denseChild_congr_cutoff D id _ C _ _ (h i) ρ K
        (fun x y => (boundedRoutedBinCutoff_div_eq (fun i => rate_pos (kb i))
          (hC x y) (hCcap x y) i).symm) σ
    · simp only [canonical]
      rw [HierarchyTask.correctionAtomTask_last HP.k_pos]
      rfl
  refine HierarchyTask.conditionalChildCost_le_of_root_budgets (B := B) channelsV (range (n + 1)) l
    source mid terminal (fun i => rate (kb i)) hCA hCB hP (rate_pos ks) hδ estimated canonical
    hsource ?_ ?_ ?_
  · intro i r hc σ x y
    constructor
    · exact incomingChildren_mem_Icc HP D id Kc (bounded i) (hcap.trans (le_max_left cap 16))
        (hbounded i) (raw i) (prep i) (maximum i) r σ x y
    · rw [hcanon i r hc σ]
      exact canonicalRequestChild_mem_Icc HP D id C (bounded i) (h i) ρ K
        (by positivity) (hbounded i) hρ r σ x y
  · intro i r _ σ x y hy
    exact ⟨incomingChildren_zero_off_usage HP D id Kc (bounded i) (raw i) (prep i)
      (maximum i) r σ x y hy,
      canonicalRequestChild_zero_off_usage HP D id C (cutoff i) (h i) ρ K r σ x y hy⟩
  · intro i r hc
    exact (rowNormPow_mono_terminal (mul_pos hP (hsource i r hc)).le
      (hsub i r hc) (fun σ x y => estimated i σ r x y ^ (4⁻¹ : ℝ) -
        canonical i σ r x y ^ (4⁻¹ : ℝ))).trans (hroot i r hc)

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
