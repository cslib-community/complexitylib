/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual second deterministic envelopes)
import Complexity.Foundations.Probability.NormalizedAtomRows.SecondEnvelope

/-! Width, coupled spectator errors, and exact zero/empty edges for B1. -/
set_option linter.privateModule false
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- A maximum repeated at two endpoints really costs width two. Dropping width is false.
example :
    rowNormPow 4 2 1 (fun (_ : Unit) (_ : Bool) => True) (fun _ _ => True)
      (fun _ _ _ => (1 : ℝ)) = 2 ∧
    rowNormPow 4 2 1 (fun (_ : Unit) (_ : Bool) => True) (fun _ _ => True)
      (fun _ _ y => if y then (1 : ℝ) else 0) = 1 := by
  norm_num [rowNormPow, Fintype.sum_bool, Finset.expect]

-- The reusable maximum moment includes the empty rank exactly.
example : |kthLargest 1 (∅ : Finset Bool) (fun y => |if y then (7 : ℝ) else -3|)| ^ 4 = 0 := by
  simp [kthLargest]

-- Empty conditioning contributes zero despite a nonzero raw error.
example : rowNormPow 4 2 1 (fun (_ : Bool) (_ : Bool) => True) (fun _ _ => False)
    (fun _ x y => min 1 (|(3 : ℝ)| * rowSliceMean
      (fun (_ : Bool) (_ : Bool) => True) (fun _ _ => False) (fun _ _ _ => 7) x y)) = 0 := by
  simp [rowNormPow, rowSliceMean]

private def spectatorRaw (σ : Environment 5 3) : Matrix (ZMod 5) (ZMod 5) ℝ :=
  fun _ y => if y = 0 then (if (σ 1).1 0 = 0 then 1 else 2) else 0
private def baseFrame : Frame 5 4 1 := Classical.choice inferInstance
private def low : Environment 5 3 := fun _ => (0, baseFrame)
private def high : Environment 5 3 := fun _ => (1, baseFrame)

-- Same Ω, nonempty suffixes and a free spectator: the raw child is positive and nonconstant.
example : spectatorRaw low 0 0 = 1 ∧ spectatorRaw high 0 0 = 2 ∧
    spectatorRaw high 0 1 = 0 := by
  norm_num [spectatorRaw, low, high]

private lemma error_eq (σ : Environment 5 3) (x y : ZMod 5) :
    preparationError threeRoles 1 [3] 0 1 0 spectatorRaw (fun _ _ => 0) σ x y =
      spectatorRaw σ x y := by
  have hnonneg : 0 ≤ spectatorRaw σ x y := by unfold spectatorRaw; split_ifs <;> norm_num
  simp [preparationError, rate, abs_of_nonneg hnonneg]

-- B1 is positive at endpoint zero and exactly zero at endpoint one. Spectators are averaged.
example : 1 / 4 ≤ secondMeanEnvelope threeRoles 1 [1] [3] 0 0 0 1 0 (1 / 4)
    spectatorRaw (fun _ _ => 0) 0 0 ∧
    secondMeanEnvelope threeRoles 1 [1] [3] 0 0 0 1 0 (1 / 4)
      spectatorRaw (fun _ _ => 0) 0 1 = 0 := by
  have hs : side 5 0 = 5 := by norm_num [side]
  have hraw (σ : Environment 5 3) : (1 : ℝ) ≤ spectatorRaw σ 0 0 := by
    simp only [spectatorRaw, ↓reduceIte]
    split_ifs <;> norm_num
  have hm : (1 : ℝ) ≤ 𝔼 σ : Environment 5 3, spectatorRaw σ 0 0 := by
    calc
      _ = 𝔼 _σ : Environment 5 3, (1 : ℝ) := (Fintype.expect_const _).symm
      _ ≤ _ := expect_le_expect fun σ _ => hraw σ
  simp only [secondMeanEnvelope, rowSliceMean, error_eq, hs, retainedMask, full_retains,
    and_self, filter_true]
  constructor
  · rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    exact le_min (by norm_num) (by linarith)
  · norm_num [spectatorRaw]

-- The actual width 5 and inverse rank rate are visible even for narrower usage.
set_option backward.isDefEq.respectTransparency false in
example : rowNormPow 4 5 (rate 0) (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
    (retainedMask 2 (side 5 1) 1 [3])
    (fun _ => secondMeanEnvelope threeRoles 1 [1] [3] 0 0 1 1 0 (1 / 4)
      spectatorRaw (fun _ _ => 0)) ≤
    5 * (|(1 / 4 : ℝ)| * (1 + 0) / rate 0) ^ 4 *
      rowNormPow 4 5 (rate 0) (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
        (retainedMask 2 (side 5 0) 1 [3]) spectatorRaw := by
  have hb := secondMeanEnvelope_moment threeRoles 1 [1] [3] 0 0 1 (by decide)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0) (1 / 4)
    spectatorRaw (fun _ _ => 0) (N := 5) (u := rate 0) (mul_nonneg (by norm_num) (rate_pos 0).le)
  simpa only [sub_zero, threeRoles, Nat.cast_ofNat] using hb

-- Exact zero raw error is still zero with unequal usage, nonempty suffixes and D=0.
example (G : Matrix (ZMod 5) (ZMod 5) ℝ) :
    secondMeanEnvelope threeRoles 0 [1, 2] [3] 0 1 2 3 4 7 (fun _ => G) G 0 0 = 0 := by
  simp

-- The actual clipped second coordinate uses B1 built from these raw errors, with genuine
-- cutoff/rho regularity. The first coordinate and its target are retained in the same prefix.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K) :
    ∃ Lh Lρ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧
      let T := fun (_ : ℕ) σ x y => selectedPreparation HP 1 threeRoles [3] 0
        spectatorRaw σ x y
      let H := fun j => conditionalWalk (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
        (retainedMask 2 (side 5 0) 1 [3])
        (fun _ _ => (⟨id, fun _ => rfl⟩ : RotationMap _ Unit)) (fun _ _ => j) (T j)
      actualClippedMean HP (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [3]
        0 (fun _ _ => 0) (1 / 4)
        (firstSignalIncrement (fun _ => spectatorRaw) 0 (secondSignalIncrement H (1 / 4)))
        (fun _ _ _ _ => 0) 1 2 0 0 ≤
        secondMeanEnvelope threeRoles 1 [1] [3] 0 0 0 Lh Lρ (1 / 4)
          spectatorRaw (fun _ _ => 0) 0 0 := by
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := preparation_stability_constants HP
  refine ⟨Lh, Lρ, hLh, hLρ, ?_⟩
  exact actualSelectedSecondSignal_mean_le_envelope HP hK 1 threeRoles 0 0 0 (by decide)
    [1] [3] (fun _ => spectatorRaw)
    (fun _ _ _ => (⟨id, fun _ => rfl⟩ : RotationMap _ Unit)) (fun j _ _ => j)
    (fun _ => spectatorRaw) hLρ hh hρ (1 / 4) (fun _ _ => 0) 2 0 0

-- A width-free replacement is false, rather than merely absent from the statement.
example : ¬ rowNormPow 4 2 1 (fun (_ : Unit) (_ : Bool) => True) (fun _ _ => True)
      (fun _ _ _ => (1 : ℝ)) ≤
    rowNormPow 4 2 1 (fun (_ : Unit) (_ : Bool) => True) (fun _ _ => True)
      (fun _ _ y => if y then (1 : ℝ) else 0) := by
  norm_num [rowNormPow, Fintype.sum_bool, Finset.expect]

-- An error outside usage can dominate the FULL rank. Replacing that max by usage loses it.
example : kthLargest 1 (univ : Finset Bool) (fun y => |if y then (0 : ℝ) else 3|) = 3 ∧
    kthLargest 1 ({true} : Finset Bool) (fun y => |if y then (0 : ℝ) else 3|) = 0 := by
  constructor
  · apply le_antisymm
    · apply kthLargest_le (by norm_num : (0 : ℝ) ≤ 3)
      intro y _
      cases y <;> norm_num
    · have hm := abs_le_kthLargest_one (univ : Finset Bool)
        (fun y => if y then (0 : ℝ) else 3) false (mem_univ _)
      norm_num only [Bool.false_eq_true, ↓reduceIte,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at hm
      exact hm
  · apply le_antisymm
    · apply kthLargest_le le_rfl
      intro y hy
      simp only [mem_singleton] at hy
      subst y
      norm_num
    · exact kthLargest_nonneg
