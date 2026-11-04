/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.TwoMask

/-!
# The four actual prefix maxima

The two deterministic conditional means and two centered noises form a concrete
row envelope. The first maximum is on terminal rank, the second on usage. All four
statistics retain the original environment and the already-added prefix i+1.
These original finite comparisons introduce no stochastic independence or accuracy premise.

## Main definitions

* `actualMeanMax`: actual deterministic discrepancy on rank or usage.
* `actualFourMax`: the sum of the two mean and two noise maxima.

## Main results

* `actual_clipped_le_fourMax`: the endpoint envelope used by the actual decoder.
* `actualFourMax_budget`: four separate moment payments combined by finite Minkowski.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- The actual deterministic conditional-mean maximum on its own mask. -/
@[expose] def actualMeanMax (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (ν : Fin 2) (i : ℕ) (σ : Environment P J) (x : ZMod P) : ℝ :=
  kthLargest 1 {y | retainedMask t (if ν = 0 then La else Lt) D st σ y}
    (fun y => |actualClippedMean HP s t Ls La Lt D ss st k G ζ Δ raw ν i x y|)

/-- Sum of the four literal row maxima, with no supplied error budget. -/
@[expose] def actualFourMax (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (i : ℕ) (σ : Environment P J) (x : ZMod P) : ℝ :=
  (actualMeanMax HP s t Ls La Lt D ss st k G ζ Δ raw 0 i σ x +
    actualMeanMax HP s t Ls La Lt D ss st k G ζ Δ raw 1 i σ x) +
  (actualNoiseMax s t Ls La Lt D ss st k G Δ raw 0 i σ x +
    actualNoiseMax s t Ls La Lt D ss st k G Δ raw 1 i σ x)

/-- Every component maximum is nonnegative, including empty masks. -/
lemma actualFourMax_nonneg (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (i : ℕ) (σ : Environment P J) (x : ZMod P) :
    0 ≤ actualFourMax HP s t Ls La Lt D ss st k G ζ Δ raw i σ x :=
  add_nonneg (add_nonneg kthLargest_nonneg kthLargest_nonneg)
    (add_nonneg kthLargest_nonneg kthLargest_nonneg)

/-- The shared four-max comparison in the actual mean/noise API. -/
theorem actual_row_max_le_fourMax (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ) (i : ℕ)
    (hz : ∀ σ x y, ¬retainedMask t Lt D st σ y → actualPrefix Δ raw i σ x y 1 = 0)
    (σ : Environment P J) (x : ZMod P) :
    kthLargest 1 {y | retainedMask t La D st σ y} (fun y =>
      clippedError (G x y / rate k)
        (genuineTarget HP s t Ls Lt D ss st k G ζ σ x y 1) (actualPrefix Δ raw i σ x y)) ≤
      actualFourMax HP s t Ls La Lt D ss st k G ζ Δ raw i σ x := by
  have hh := actual_two_mask_row_max HP s t Ls La Lt D ss st k G hG ζ
    (actualPrefix Δ raw i) hz σ x
  have hd (y : ZMod P) : |1 + G x y / rate k| = 1 + G x y / rate k :=
    abs_of_pos (by linarith [div_nonneg (hG x y) (rate_pos k).le])
  dsimp only at hh
  simp only [actualFourMax, actualMeanMax, actualClippedMean, actualNoiseMax,
    Fin.isValue, one_ne_zero, ↓reduceIte, div_one, abs_div, abs_abs, hd] at hh ⊢
  linarith

/-- Each full-rank endpoint is bounded by the concrete four-max envelope. -/
theorem actual_clipped_le_fourMax (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ) (i : ℕ)
    (hz : ∀ σ x y, ¬retainedMask t Lt D st σ y → actualPrefix Δ raw i σ x y 1 = 0)
    (σ : Environment P J) (x y : ZMod P) (hy : retainedMask t La D st σ y) :
    clippedError (G x y / rate k)
      (genuineTarget HP s t Ls Lt D ss st k G ζ σ x y 1) (actualPrefix Δ raw i σ x y) ≤
      actualFourMax HP s t Ls La Lt D ss st k G ζ Δ raw i σ x := by
  have h := abs_le_kthLargest_one {z | retainedMask t La D st σ z}
    (fun z => clippedError (G x z / rate k)
      (genuineTarget HP s t Ls Lt D ss st k G ζ σ x z 1) (actualPrefix Δ raw i σ x z)) y
    (mem_filter.mpr ⟨mem_univ _, hy⟩)
  simp only [abs_of_nonneg (clippedError_nonneg _ _ _)] at h
  exact h.trans (actual_row_max_le_fourMax HP s t Ls La Lt D ss st k G hG ζ Δ raw i hz σ x)

/-- Finite Minkowski combines the four actual maxima without a prefix-count factor.
The deterministic and noise budgets remain separate. -/
theorem actualFourMax_budget (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ) (i : ℕ)
    {N u : ℝ} (hNu : 0 ≤ N * u) (a z : Fin 2 → ℝ)
    (ha : ∀ ν, 0 ≤ a ν) (hz : ∀ ν, 0 ≤ z ν)
    (hm : ∀ ν, vertexNormPow 4 N u (retainedMask s Ls D ss)
      (actualMeanMax HP s t Ls La Lt D ss st k G ζ Δ raw ν i) ≤ (a ν) ^ 4)
    (hn : ∀ ν, vertexNormPow 4 N u (retainedMask s Ls D ss)
      (actualNoiseMax s t Ls La Lt D ss st k G Δ raw ν i) ≤ (z ν) ^ 4) :
    vertexNormPow 4 N u (retainedMask s Ls D ss)
      (actualFourMax HP s t Ls La Lt D ss st k G ζ Δ raw i) ≤
      ((a 0 + a 1) + (z 0 + z 1)) ^ 4 :=
  vertex_add_budget _ hNu (add_nonneg (ha 0) (ha 1)) (add_nonneg (hz 0) (hz 1)) _ _
    (vertex_add_budget _ hNu (ha 0) (ha 1) _ _ (hm 0) (hm 1))
    (vertex_add_budget _ hNu (hz 0) (hz 1) _ _ (hn 0) (hn 1))

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
