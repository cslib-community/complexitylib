/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests of supported actual preparation histories)

import Complexity.Foundations.Probability.HierarchySupportedPreparation
import all ComplexityTests.PolynomialBudgetHistory

/-! The actual early preparation walk is zero while its canonical target is nonzero.
Its second deterministic statistic is paid from a nonzero first mean and zero first noise. -/

set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open PolynomialBudgetHistory
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ Lh Lρ : ℝ, 0 ≤ Lh ∧ 0 ≤ Lρ ∧
    let F := fun i (_ : Environment 5 3) => if 2 ≤ i then base else 0
    let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
    let Δ := firstSignalIncrement F 0
      (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) (HP.η / 4))
    (List.range (Nat.log2 2 + 1)).mapM (fun i =>
      (data HP).complete 2 (request HP) ((data HP).binPreparation 0 (request HP) (F (i + 1)))
        (dyadicSlack (Nat.log2 2 + 1) i)) = some W ∧
    0 < actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
      1 [1] [2, 3] 0 base (HP.η / 4) Δ 0 1 0 0 0 ∧
    rowNormPow 4 5 (rate 0) (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask (2 : Fin 3) (side 5 0) 1 [2, 3])
      (fun _ x y => actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
        1 [1] [2, 3] 0 base (HP.η / 4) Δ 0 1 0 x y) ≤
      8 * (2 * HP.K) * (|HP.η / 4| * preparationRelativeConstant HP Lh Lρ) ^ 4 * (1 / 16) := by
  obtain ⟨Lh, Lρ, hLh, hLρ, hh, hρ⟩ := preparation_stability_constants HP
  refine ⟨Lh, Lρ, hLh, hLρ, ?_⟩
  dsimp only
  let F := fun i (_ : Environment 5 3) => if 2 ≤ i then base else 0
  let W : List (Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) := [0, fun _ => base]
  let Δ := firstSignalIncrement F 0
    (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) (HP.η / 4))
  have hret (τ : Environment 5 3) (role : Fin 3) (su : List (ZMod 5)) (v : ZMod 5) :
      retainedMask role (side 5 0) 1 su τ v := by
    simpa only [retainedMask, gridChannel, CorrectionRowTask.Channel.retains, channels,
      semanticSide_grid] using full τ role su v
  have hmean : rowNormPow 4 5 (request HP).source.rate
      (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask (2 : Fin 3) (side 5 0) 1 [2, 3])
      (fun _ x y => actualClippedMean HP 0 2 (side 5 0) (side 5 0) (side 5 0)
        1 [1] [2, 3] 0 base (HP.η / 4) Δ 0 0 0 x y) ≤ 1 / 16 := by
    simp only [Δ, actualClippedMean_first_prefix_eq, F, show ¬2 ≤ 1 by decide, ↓reduceIte]
    norm_num [rowNormPow, rowSliceMean, hret, base, Matrix.one_apply, request, gridChannel,
      rate]
    have he (x y : ZMod 5) :
        |min 1 (|if x = y then (1 : ℝ) else 0| / (1 + if x = y then 1 else 0))| ^ 4 =
        if x = y then (1 / 16 : ℝ) else 0 := by
      split_ifs <;> norm_num
    simp_rw [he]
    norm_num
  have hnoise : rowNormPow 4 5 (request HP).source.rate
      (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask (2 : Fin 3) (side 5 0) 1 [2, 3])
      (actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0)
        1 [1] [2, 3] 0 base Δ 0 0 0) ≤ 0 := by
    change rowNormPow 4 5 (request HP).source.rate _ _ (fun σ x y =>
      actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0)
        1 [1] [2, 3] 0 base Δ 0 0 0 σ x y) ≤ 0
    simp only [Δ, actualNoiseEntry_first_prefix _ _ _ _ _ _ _ _ F 0 base _ 0
      (by intros; rfl), F, show ¬2 ≤ 1 by decide, ↓reduceIte]
    norm_num [rowNormPow, rowSliceMean, hret]
  refine ⟨by simpa only [F, W] using preparation_walks HP, ?_, ?_⟩
  · have he := (actual_preparation_edges HP (0 : ZMod 5) 1 (by decide)).2.2.1
    change 0 < actualClippedMean _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ => 0) _ _ _ _
    rw [he]
    exact div_pos HP.η_pos (by norm_num)
  · have hb := (data HP).initialSecondSignal_relative_mean_moment 2 0 0 0 le_rfl
      (request HP) threeRoles 0 [1] [2, 3] rfl rfl rfl rfl F W
      (preparation_walks HP)
      (by intro x y; simp only [data, base, Matrix.one_apply]; split_ifs <;> norm_num)
      hLh hLρ hh hρ (HP.η / 4) 0 (by decide) hmean hnoise
    simpa only [data, request, gridChannel, threeRoles, add_zero, Nat.cast_ofNat, F, W] using hb
