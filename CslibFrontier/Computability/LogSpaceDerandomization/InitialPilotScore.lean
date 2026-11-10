/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyDenseChildren
public import CslibFrontier.Computability.LogSpaceDerandomization.PilotRowStability
public import CslibFrontier.Foundations.Probability.SpectralPayment
import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.Output

/-!
# Allocated initial-pilot RAW calls followed by the actual score recipe

The initial pilot has a literal zero correction. Its direct dense bin is computed
from the stage-zero base matrix and its actual preparation, then averaged by the
full-coordinate H4 retained-pair walk. The score reads that completed matrix on the
same environment. No child oracle, accuracy certificate or independent seed is supplied.
This original finite fragment does not close later pilot iterations or detector recursion.
Its reference is the literal conditional RAW mean; identifying it with the whole base
requires bin coverage and the dense-atom hypotheses, separately from spectral accuracy.
The final single-bin theorem derives this identification for nonnegative substochastic bases.

## Main definitions

* `initialPilotRaw`: computed stage-zero initial-pilot dense bin.
* `initialPilotWalk`: actual full-coordinate completed RAW call.
* `initialPilotScore`: the upper score of that completed call.
* `initialPilotSteps`: positive finite tolerance allocation.

## Main results

* `initialPilotRaw_eq_rawSample`: correspondence with actual initial RAW requests.
* `initialPilotRaw_mean`: dense normalization derives the matrix-unit bin mean.
* `initialPilotScore_allocated`: literal conditional-mean error payment.
* `initialPilotScore_allocated_of_single_bin`: actual initial score under bin coverage.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- One initial-pilot bin, evaluated from the actual base and preparatory recipes.
The product with the zero-iteration pilot correction vanishes. The request retains
its actual bin rank, usage, role and suffix. -/
@[expose] def initialPilotRaw
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x y : ZMod P) : ℝ :=
  let endpoint := gridChannel R.terminal kt st
  let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
    ⟨.baseNormalized 0 bin, gridChannel R.source ks ss,
      gridChannel R.terminal kb st, gridChannel R.terminal (max kt kb) st⟩
  rate kb * HierarchyTask.usageRatio (channels D) endpoint r y *
    denseChild D id r cutoff h HP.ρ HP.K C σ x y

/-- The computed dense request is structurally earlier than the actual initial RAW call.
The structural iteration is fixed by HP and is independent of statistical accuracy. -/
theorem initialPilotRaw_rank_lt
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin : ℕ) :
    (HierarchyTask.baseNormalized (k := HP.k) 0 bin).rank <
      (HierarchyTask.row 0 (.pilotInput ⟨0, HP.k_pos⟩)).rank :=
  HierarchyTask.rank_lt_of_binDependency (.basePilotInput 0 bin ⟨0, HP.k_pos⟩)

/-- This is the actual first pilot RAW formula after evaluating its literal zero
correction child. The right child is unrestricted: it is multiplied by that zero.
Only the three genuine requests are inspected. -/
theorem initialPilotRaw_eq_rawSample
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks km kt kb : ℕ) (ss sm st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J)
    (child : HierarchyTask.Request HP.k (Fin J) (ZMod P) → Matrix (ZMod P) (ZMod P) ℝ)
    (hleft : child (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
      (gridChannel R.terminal kt st) (rate kb)).left = 0)
    (hdirect : child (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
      (gridChannel R.terminal kt st) (rate kb)).direct =
      denseChild (n := HP.k) D id
        ⟨.baseNormalized 0 bin, gridChannel R.source ks ss,
          gridChannel R.terminal kb st, gridChannel R.terminal (max kt kb) st⟩
        cutoff h HP.ρ HP.K C σ) :
    initialPilotRaw HP D R bin ks kt kb ss st cutoff h C σ =
      HierarchyTask.rawSample (channels D) 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
        (gridChannel R.terminal kt st) (rate kb) child := by
  funext x y
  simp only [HierarchyTask.rawRequests, gridChannel, rate_min] at hleft hdirect
  simp only [HierarchyTask.rawSample, HierarchyTask.rawPositiveSample,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests, gridChannel, rate_min]
  rw [hleft, hdirect]
  simp only [initialPilotRaw, HierarchyTask.usageRatio, gridChannel,
    Matrix.zero_apply, zero_mul, sum_const_zero, mul_zero, add_zero, sub_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- At equal bin/parent terminal rates the literal conditional mean is the true
matrix-unit bin. This uses the actual dense normalization law, not a desired-mean
hypothesis. Source rank, source suffix and terminal suffix remain explicit. -/
theorem initialPilotRaw_mean
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (hD : D ≠ 0)
    (R : RoleProfile J) (H : Horizon P) (bin ks kb : ℕ)
    (hks : ks ≤ H.maxExponent) (hkb : kb ≤ H.maxExponent)
    (ss st : List (ZMod P)) (cutoff h : ℝ → ℝ)
    (C : Matrix (ZMod P) (ZMod P) ℝ)
    (hkh : ∀ v, cutoff v ≠ 0 → h v = 1)
    {η : ℝ} (hη : 0 < η) (hρη : ∀ v, v ≤ η → HP.ρ v = 1)
    (hK : 2 * (1 + 32 / η) ≤ HP.K)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (x y : ZMod P) :
    rowSliceMean (X R.source (side P ks) (CopyPadding.identifier D ss))
      (Y R.terminal (side P kb) (CopyPadding.identifier D st))
      (initialPilotRaw HP D R bin ks kb kb ss st cutoff h C) x y =
        rate kb * cutoff (C x y / rate kb) := by
  let r : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
    ⟨.baseNormalized 0 bin, gridChannel R.source ks ss,
      gridChannel R.terminal kb st, gridChannel R.terminal kb st⟩
  have hr : Admissible r := ⟨R.source_terminal, rfl, rfl⟩
  have hm := denseChild_mean_on_terminal_event D id r hr hD Function.injective_id H
    hks rfl hkb rfl (u := kb) rfl cutoff h HP.ρ HP.K C
    (splitTerminal D id r · y) x y (fun _ hy => hy) hkh HP.ρ_nonneg HP.ρ_le_one
    hη hρη (hC x) (by simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using hC1 x) hK
  convert hm using 1 <;>
    simp only [rowSliceMean, initialPilotRaw, HierarchyTask.usageRatio, r, gridChannel,
      max_self, CorrectionRowTask.Channel.retains, channels, splitTerminal,
      coordinate, semanticSide_grid, X, Y, id_eq]

/-- Actual completed initial RAW child. All coordinates are moved by the existing
H4 graph; no nonlinear score is evaluated inside the lower walk. -/
@[expose] def initialPilotWalk
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (steps : ℕ) :=
  conditionalWalk (H4RankEnvironment.X R.source (side P ks) (CopyPadding.identifier D ss))
    (H4RankEnvironment.Y R.terminal (side P kt) (CopyPadding.identifier D st))
    (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
      (side_le P ks) (side_le P kt) (CopyPadding.identifier D ss)
      (CopyPadding.identifier D st)) (fun _ _ => steps)
    (initialPilotRaw HP D R bin ks kt kb ss st cutoff h C)

/-- The upper score actually calls the completed lower RAW function on this environment. -/
@[expose] def initialPilotScore
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (steps : ℕ)
    (σ : Environment P J) :=
  PilotRowRecipe.score HP.toHierarchyParams
    (H4RankEnvironment.Y R.terminal (side P kt) (CopyPadding.identifier D st)) (rate kt)
    (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C steps σ) σ

/-- The RAW call of the score is strictly earlier in the existing hierarchy task order. -/
theorem initialPilotScore_rank_lt
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (HierarchyTask.row (k := HP.k) 0 (.pilotInput ⟨0, HP.k_pos⟩)).rank <
      (HierarchyTask.row 0 (.score ⟨0, HP.k_pos⟩)).rank := by
  apply HierarchyTask.rank_lt_of_mem_children
  simp [HierarchyTask.children, BoundedRowTask.children]

/-- Fixed-HP score constants pay the actual completed RAW walk. The explicit input
moment is of a computed dense sample, rather than an assumed final child error.
All widths, rates and walk factors remain visible. -/
theorem initialPilotScore_error
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P) (R : RoleProfile J)
      (bin ks kt kb : ℕ) (ss st : List (ZMod P))
      (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (steps : ℕ),
    let X := H4RankEnvironment.X R.source (side P ks) (CopyPadding.identifier D ss)
    let Y := H4RankEnvironment.Y R.terminal (side P kt) (CopyPadding.identifier D st)
    let input := initialPilotRaw HP D R bin ks kt kb ss st cutoff h C
    let mean := rowSliceMean X Y input
    rowNormPow 4 P (rate ks) X Y (fun σ x y =>
      initialPilotScore HP D R bin ks kt kb ss st cutoff h C steps σ x y -
        PilotRowRecipe.score HP.toHierarchyParams Y (rate kt) mean σ x y) ≤
      (P : ℝ) * (L / rate kt) ^ 4 *
        (32 * (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps) *
          rowNormPow 4 P (rate ks) X Y input) := by
  obtain ⟨La, Lb, ha, hb, hϕ, hρ⟩ := HP.pilot_score_stability_constants
  refine ⟨La + Lb, add_nonneg ha hb, ?_⟩
  intro P J inst D R bin ks kt kb ss st cutoff h C steps X Y input mean
  have hNu : 0 ≤ (P : ℝ) * rate ks := mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hs := PilotRowRecipe.score_row_moment HP.toHierarchyParams X Y HP.ρ_nonneg
    ha hb hϕ hρ (FourthRootHierarchyParams.NormalizedRow.rank_pos HP)
    (rate_pos kt) hNu
    (initialPilotWalk HP D R bin ks kt kb ss st cutoff h C steps) (fun _ => mean)
  have hn := noise R.source R.terminal R.source_terminal (side P ks) (side P kt)
    (side_le P ks) (side_le P kt) (CopyPadding.identifier D ss)
    (CopyPadding.identifier D st) hNu steps input
  apply hs.trans
  simp only [ZMod.card]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

/-- Positive finite walk allocation for the computed lower child. The budget is the
literal finite fourth moment of the base-derived dense sample, multiplied by the
score width/rate payment. Zero input moments still receive at least one step. -/
@[expose] def initialPilotSteps
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (L : ℝ)
    (D : ZMod P) (R : RoleProfile J) (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (ε : ℝ) : ℕ :=
  max 1 (spectralWalkLength (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4))
    ((P : ℝ) * (L / rate kt) ^ 4 * 32 *
      rowNormPow 4 P (rate ks)
        (X R.source (side P ks) (CopyPadding.identifier D ss))
        (Y R.terminal (side P kt) (CopyPadding.identifier D st))
        (initialPilotRaw HP D R bin ks kt kb ss st cutoff h C)) ε 0)

/-- The allocated lower call has a real, positive walk length, even for a zero budget. -/
theorem initialPilotSteps_pos
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (L : ℝ)
    (D : ZMod P) (R : RoleProfile J) (bin ks kt kb : ℕ) (ss st : List (ZMod P))
    (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (ε : ℝ) :
    0 < initialPilotSteps HP L D R bin ks kt kb ss st cutoff h C ε :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

/-- A two-constructor allocated call: the upper score reads the actual computed RAW
walk on the same environment. No lower error premise is supplied. The reference is
the score of that bin's literal conditional mean, not a full recursive pilot theorem. -/
theorem initialPilotScore_allocated
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P) (R : RoleProfile J)
      (bin ks kt kb : ℕ) (ss st : List (ZMod P))
      (cutoff h : ℝ → ℝ) (C : Matrix (ZMod P) (ZMod P) ℝ) (ε : ℝ), 0 < ε →
    let X := H4RankEnvironment.X R.source (side P ks) (CopyPadding.identifier D ss)
    let Y := H4RankEnvironment.Y R.terminal (side P kt) (CopyPadding.identifier D st)
    let input := initialPilotRaw HP D R bin ks kt kb ss st cutoff h C
    let mean := rowSliceMean X Y input
    let steps := initialPilotSteps HP L D R bin ks kt kb ss st cutoff h C ε
    rowNormPow 4 P (rate ks) X Y (fun σ x y =>
      initialPilotScore HP D R bin ks kt kb ss st cutoff h C steps σ x y -
        PilotRowRecipe.score HP.toHierarchyParams Y (rate kt) mean σ x y) ≤ ε ^ 4 := by
  obtain ⟨L, hL, herr⟩ := initialPilotScore_error HP
  refine ⟨L, hL, ?_⟩
  intro P J inst D R bin ks kt kb ss st cutoff h C ε hε X Y input mean steps
  have hden : (1 : ℝ) < 155648 * (J + 1) * (4 : ℝ) ^ 4 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hr : 0 < 1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4) :=
    sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hm : 0 ≤ rowNormPow 4 P (rate ks) X Y input :=
    rowNormPow_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le) input
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (show 0 ≤ (P : ℝ) * (L / rate kt) ^ 4 * 32 * rowNormPow 4 P (rate ks) X Y input by
      positivity) hε 0 steps (Nat.le_max_right _ _)
  simp only [pow_zero, mul_one] at hp
  apply (herr P J D R bin ks kt kb ss st cutoff h C steps).trans
  nlinarith only [hp]

/-- If one genuine dense bin covers the base matrix, the allocated two-level call
approximates the initial pilot score of that base. The mean is derived from dense
normalization and scalar bin coverage. Later pilot iterations and general bin sums
are not part of this fragment. -/
theorem initialPilotScore_allocated_of_single_bin
    (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (P J : ℕ) [Fact P.Prime] (D : ZMod P), D ≠ 0 →
    ∀ (R : RoleProfile J) (H : Horizon P) (bin ks kb : ℕ),
    ks ≤ H.maxExponent → kb ≤ H.maxExponent →
    ∀ (ss st : List (ZMod P)) (cutoff h : ℝ → ℝ)
      (C : Matrix (ZMod P) (ZMod P) ℝ),
    (∀ v, cutoff v ≠ 0 → h v = 1) →
    ∀ η : ℝ, 0 < η → (∀ v, v ≤ η → HP.ρ v = 1) →
    2 * (1 + 32 / η) ≤ HP.K →
    (∀ x y, 0 ≤ C x y) → C *ᵥ 1 ≤ 1 →
    (∀ x y, rate kb * cutoff (C x y / rate kb) = C x y) →
    ∀ ε : ℝ, 0 < ε →
    let X := H4RankEnvironment.X R.source (side P ks) (CopyPadding.identifier D ss)
    let Y := H4RankEnvironment.Y R.terminal (side P kb) (CopyPadding.identifier D st)
    let steps := initialPilotSteps HP L D R bin ks kb kb ss st cutoff h C ε
    rowNormPow 4 P (rate ks) X Y (fun σ x y =>
      initialPilotScore HP D R bin ks kb kb ss st cutoff h C steps σ x y -
        PilotRowRecipe.score HP.toHierarchyParams Y (rate kb) C σ x y) ≤ ε ^ 4 := by
  obtain ⟨L, hL, ha⟩ := initialPilotScore_allocated HP
  refine ⟨L, hL, ?_⟩
  intro P J inst D hD R H bin ks kb hks hkb ss st cutoff h C hkh η hη hρη hK hC hC1
    hcover ε hε X Y steps
  have hm : rowSliceMean X Y (initialPilotRaw HP D R bin ks kb kb ss st cutoff h C) = C := by
    funext x y
    exact (initialPilotRaw_mean HP D hD R H bin ks kb hks hkb ss st cutoff h C hkh hη
      hρη hK hC hC1 x y).trans (hcover x y)
  have hp := ha P J D R bin ks kb kb ss st cutoff h C ε hε
  dsimp only at hp
  rw [hm] at hp
  exact hp

end Matrix.HierarchyParams.H4RankEnvironment
