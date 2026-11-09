/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests of numerical actual first-signal noise payments)

import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.FirstPayment
import all CslibFrontierTests.HierarchyRawMoment

/-! Actual capped bins, nonzero residuals, chosen steps and zero/empty boundaries. -/
set_option linter.privateModule false

open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace FirstPaymentRegression

private def binCutoff (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ) : ℝ → ℝ :=
  boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) rate (HP.k + 2) i (fun _ => 1)

private def binBound (HP : FourthRootHierarchyParams 16 1 16 32 8) : ℝ :=
  max (HP.k + 2 : ℝ) 16

private lemma bin_range (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ) (d : ℝ) :
    binCutoff HP i d ∈ Set.Icc 0 (binBound HP) := by
  apply boundedRoutedBinCutoff_mem_Icc (by positivity)
    (le_trans (by norm_num : (0 : ℝ) ≤ 16) (le_max_right _ _)) (le_max_left _ _)
    (monotone_polynomialSwitch4 (by norm_num))
    (fun t ht => polynomialSwitch4_of_le (by norm_num) ht)
    (fun t ht => polynomialSwitch4_of_ge (by norm_num) ht)
    (fun t => ⟨polynomialSwitch4_nonneg _ _ _, polynomialSwitch4_le_one _ _ _⟩)
    rate_pos rate_antitone (fun i => (adjacent_rate_ratio i).le.trans (le_max_right _ _))
    (fun _ => 1) (by intro; norm_num)

private lemma bin_one (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    binCutoff HP 0 1 = 1 := by
  have hk : (1 : ℝ) ≤ HP.k + 2 := by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith
  simp only [binCutoff, boundedRoutedBinCutoff, routedBinCutoff, Cslib.binWeight,
    rate, min_eq_right hk, ↓reduceIte, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
    pow_zero, inv_one, one_pow, mul_one]
  simpa only [one_mul, div_one] using
    (polynomialSwitch4_of_ge (α := (1 / 2 : ℝ)) (β := 1) (t := 1) (by norm_num) le_rfl)

-- This is an actual fine bin, rather than an asserted bound on an arbitrary function.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ) (d : ℝ) :
    binCutoff HP (i + 1) d ∈ Set.Icc 0 (binBound HP) := bin_range HP _ _

-- The top bin has nonzero output at one, and clips negative estimates to literal zero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    binCutoff HP 0 1 = 1 ∧ binCutoff HP 0 (-1) = 0 := by
  exact ⟨bin_one HP, boundedRoutedBinCutoff_of_neg (by positivity) (by norm_num) 0 _⟩

private theorem actual_dense_child (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (cutoff : ℝ → ℝ) (hcut : cutoff 1 = 1)
    (s t : Fin 3) (hst : s ≠ t) (ss st : List (ZMod 5)) (σ : Environment 5 3) :
    normalizedRequest 1 (fun (_ : Unit) => 0)
      (⟨HierarchyTask.baseNormalized 0 0, gridChannel s 0 ss, gridChannel t 0 st,
        gridChannel t 0 st⟩ : HierarchyTask.Request 1 (Fin 3) (ZMod 5))
      cutoff HP.ρ HP.K (fun _ _ _ => 1) (fun _ _ _ => 1) σ () () = 1 := by
  have hr : Admissible (⟨HierarchyTask.baseNormalized 0 0, gridChannel s 0 ss,
      gridChannel t 0 st, gridChannel t 0 st⟩ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) :=
    ⟨hst, rfl, rfl⟩
  have hs : side 5 0 = 5 := by norm_num [side]
  unfold normalizedRequest
  rw [dite_eq_left hr]
  dsimp only
  simp only [DenseRowRecipe.normalized, coordinate, gridChannel,
    semanticSide_grid, hs, full_retains, ↓reduceIte]
  norm_num [rate, rowGate, kthLargest, not_le.mpr (_root_.big_K HP),
    CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le, hcut]

-- The complete signed residual is one; its actual product contribution is Q(1)>0.
-- All three rank coordinates remain present and both copied suffixes are nonempty.
theorem actual_bin_residual_one (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 3) :
    rawIncomingNormalized HP 1 (fun (_ : Unit) => 0) threeRoles 0 0 0 0 0 0 [1] [2] [3]
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 (binCutoff HP 0)
      (fun (_ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) _ _ _ => 1)
      (fun _ _ _ _ => 1) (fun _ _ _ => 0) σ () () = 1 := by
  have he : rawIncomingNormalized (k := 1) HP 1 (fun (_ : Unit) => 0) threeRoles
      0 0 0 0 0 0 [1] [2] [3] (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2
      (binCutoff HP 0) (fun _ _ _ _ => 1) (fun _ _ _ _ => 1) (fun _ _ _ => 0) σ () () =
      rawIncomingNormalized (k := 1) HP 1 (fun (_ : Unit) => 0) threeRoles
      0 0 0 0 0 0 [1] [2] [3] (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2
      (fun _ => 1) (fun _ _ _ _ => 1) (fun _ _ _ _ => 1) (fun _ _ _ => 0) σ () () := by
    simp only [rawIncomingNormalized, HierarchyTask.rawSample, HierarchyTask.rawPositiveSample,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests,
      show HierarchyTask.correctionAtomTask (k := 1) 0 false (Fin.last 1) =
        .row 0 (.normalized 0) from rfl]
    dsimp only [threeRoles]
    simp only [gridChannel, min_self]
    have hd := actual_dense_child HP (binCutoff HP 0) (bin_one HP) 0 2 (by decide) [1] [3] σ
    have hb := actual_dense_child HP (binCutoff HP 0) (bin_one HP) 1 2 (by decide) [2] [3] σ
    have hd' := actual_dense_child HP (fun _ => 1) rfl 0 2 (by decide) [1] [3] σ
    have hb' := actual_dense_child HP (fun _ => 1) rfl 1 2 (by decide) [2] [3] σ
    dsimp only [gridChannel] at hd hb hd' hb'
    simp only [Fintype.sum_unique]
    rw [hd, hb, hd', hb']
  exact he.trans (_root_.actual_residual_one HP σ)

private def firstInput (HP : FourthRootHierarchyParams 16 1 16 32 8) (_j : ℕ) :=
  rawIncomingNormalized HP 1 id threeRoles 0 0 0 0 0 0 [1] [2] [3]
    (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 6 (binCutoff HP 0)
    (fun (_ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) σ _ y =>
      if (σ 1).1 0 = 0 ∧ y = 0 then 1 else 0)
    (fun _ _ _ _ => 1) (fun _ _ _ => 0)

private def firstSteps (HP : FourthRootHierarchyParams 16 1 16 32 8) (ε : ℝ) (j : ℕ) :=
  spectralWalkLength (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4))
    ((rate 0)⁻¹ ^ 4 * 32 * firstSignalPayment HP 5 6 0 0 0 0 (binBound HP))
    ε (dyadicSlack 4 (j - 1))

private def firstWalk (HP : FourthRootHierarchyParams 16 1 16 32 8) (ε : ℝ) (j : ℕ) :=
  conditionalWalk (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
    (retainedMask 2 (side 5 0) 1 [3])
    (graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0)
      (side_le 5 0) (side_le 5 0) (fun x => CopyPadding.identifier 1 [1] x)
      (fun y => CopyPadding.identifier 1 [3] y)) (fun _ _ => firstSteps HP ε j) (firstInput HP j)

-- Two statistical precisions use the same Request HP.k child family. The walk lengths
-- vary with precision; telescoping still recovers the corresponding completed child.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (ε : ℝ)
    (σ : Environment 5 3) (x y : ZMod 5) :
    actualPrefix (firstSignalIncrement (firstWalk HP ε) 0 (fun _ _ _ _ => 7))
        (fun _ _ _ _ => 0) 0 σ x y 0 = firstWalk HP ε 1 σ x y / rate 0 ∧
    actualPrefix (firstSignalIncrement (firstWalk HP ε) 0 (fun _ _ _ _ => 7))
        (fun _ _ _ _ => 0) 2 σ x y 0 = firstWalk HP ε 3 σ x y / rate 0 := by
  constructor <;> exact actualPrefix_firstSignalIncrement _ _ _ _ (by intros; rfl) _ _ _ _

-- Actual i=2 noise uses child budget 3 and the chosen finite steps, with real capped bins,
-- unequal role/copy identifiers, dense bases and a nonzero raw column on the full field.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {ε : ℝ} (hε : 0 < ε) :
    rowNormPow 4 5 (rate 0) (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask 2 (side 5 0) 1 [3])
      (actualNoiseEntry (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [3] 0
        (fun _ _ => 0) (firstSignalIncrement (firstWalk HP ε) 0 (fun _ _ _ _ => 7))
        (fun _ _ _ _ => 0) 0 2) ≤ (ε * (64 : ℝ)⁻¹ ^ dyadicSlack 4 2) ^ 4 := by
  exact actualFirstSignal_noise_le_dyadic HP.k_pos HP
    (by have := _root_.big_K HP; omega) 1 threeRoles
    (zeroHorizon (P := 5)) 0 0 0 0 0 0 (side 5 0) (by decide) (by decide)
    [1] [2] [3] 6 (by decide) (binCutoff HP 0)
    (le_trans (by norm_num : (0 : ℝ) ≤ 16) (le_max_right _ _)) (bin_range HP 0)
    (fun _ _ σ _ y => if (σ 1).1 0 = 0 ∧ y = 0 then 1 else 0)
    (fun _ _ _ _ _ => 1) (fun _ _ _ _ => 0)
    (firstSteps HP ε) (fun _ _ => 0) (by intros; rfl) (fun _ _ _ _ => 7)
    (fun _ _ _ _ => 0) (by intros; rfl) 2 4 hε (by rfl)

-- Genuine narrower usage: at P=5 the side is ceil(5/2)=3, so the importance
-- is 1/(3/5)^4, not the nominal inverse rate 16. Copy suffixes remain arbitrary.
example (y : ZMod 5) :
    HierarchyTask.usageRatio (channels 1) (gridChannel (2 : Fin 3) 0 [3])
      (⟨HierarchyTask.baseNormalized 0 0, gridChannel 0 0 [1], gridChannel 2 1 [3],
        gridChannel 2 1 [3]⟩ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) y = 625 / 81 := by
  rw [usageRatio_grid 1 _ _ 0 1 rfl rfl]
  norm_num [side, Nat.ceilDiv_eq_add_pred_div]

-- The coarse payment's width and coefficient remain inspectable even at full rates.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (CB : ℝ) :
    firstSignalPayment HP 5 2 0 0 0 0 CB =
      5120 * ((2 * CB) ^ 4 + HP.K ^ 3 * (2 * HP.Q HP.toHierarchyParams.atomCap) ^ 4 *
        2 * (2 * CB) ^ 4 + (2 * HP.Q HP.toHierarchyParams.atomCap) ^ 4) := by
  norm_num [firstSignalPayment, gridMass, rate, side]
  ring

-- The shared logarithmic API has an exact regression at r=1/2: ceil(log_(1/2)(1/2))=1.
example : spectralWalkLength (1 / 2) 1 1 0 = 1 := by
  norm_num only [spectralWalkLength, pow_zero, mul_one, one_pow, one_add_one_eq_two]
  rw [Real.logb_self_eq_one_iff.mpr ⟨by norm_num, by norm_num, by norm_num⟩]
  norm_num

-- Zero coefficient pays exactly zero, including zero tolerance; the logarithmic theorem
-- deliberately requires positive tolerance for arbitrary positive coefficients.
example (r : ℝ) (steps : ℕ) : (0 : ℝ) * r ^ (2 * steps) = 0 := zero_mul _

-- Empty sources cost zero even with an arbitrary, fully correlated table.
example (F : Bool → Unit → Unit → ℝ) :
    rowNormPow 4 5 (rate 1) (fun _ _ => False) (fun _ _ => True) F = 0 := by
  simp [rowNormPow]

end FirstPaymentRegression
