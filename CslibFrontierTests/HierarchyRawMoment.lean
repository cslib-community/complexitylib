/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual hierarchy input moments)
import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyRawMoment
import CslibFrontierTests.HierarchyCutoffs

/-! Nonzero products, shared randomness, normalization and actual-child regressions. -/
set_option linter.privateModule false
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

-- Caps and ranges alone cannot bound an unnormalized moment independently of width.
-- The identity has entry bound one and one entry per row/column, yet moment n at N=u=1.
example (n : ℕ) :
    rowNormPow 4 1 1 (fun (_ : Unit) (_ : Fin n) => True) (fun _ _ => True)
      (fun _ => (1 : Matrix (Fin n) (Fin n) ℝ)) = n := by
  simp [rowNormPow, Matrix.one_apply, expect_eq_sum_div_card, abs_ite, ite_pow]

example (n : ℕ) (x : Fin n) :
    #{y | (1 : Matrix (Fin n) (Fin n) ℝ) x y ≠ 0} = 1 ∧
      #{y | (1 : Matrix (Fin n) (Fin n) ℝ) y x ≠ 0} = 1 := by
  have hr : ({y | (1 : Matrix (Fin n) (Fin n) ℝ) x y ≠ 0} : Finset _) = {x} := by
    ext y
    simp [Matrix.one_apply, eq_comm]
  have hc : ({y | (1 : Matrix (Fin n) (Fin n) ℝ) y x ≠ 0} : Finset _) = {x} := by
    ext y
    simp [Matrix.one_apply]
  simp [hr, hc]

example (n : ℕ) (x y : Fin n) : |(1 : Matrix (Fin n) (Fin n) ℝ) x y| ≤ 1 := by
  by_cases h : x = y <;> simp [Matrix.one_apply, h]

-- Both factors depend on the same random bit, and their product is nonconstant and nonzero.
example :
    rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => ∑ _ : Unit, (if σ then (1 : ℝ) else 2) *
        (if σ then (1 : ℝ) else 2)) = 257 / 2 := by
  norm_num [rowNormPow, expect_eq_sum_div_card, Fintype.sum_bool]

example :
    rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => ∑ _ : Unit, (if σ then (1 : ℝ) else 2) *
        (if σ then (1 : ℝ) else 2)) ≤
      16 * rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
        (fun σ _ _ => if σ then 1 else 2) := by
  have h := rowNormPow_product_le
    (X := fun (_ : Bool) (_ : Unit) => True)
    (Z := fun (_ : Bool) (_ : Unit) => True) (Y := fun _ _ => True)
    (A := fun σ _ _ => if σ then (1 : ℝ) else 2)
    (B := fun σ _ _ => if σ then (1 : ℝ) else 2)
    (K := 1) (Kc := 1) (CA := 2) (N := 1) (u := 1) (f := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro σ x z; cases σ <;> norm_num)
    (by intro σ x _; exact (card_filter_le _ _).trans (by simp))
    (by intro σ z _; exact (card_filter_le _ _).trans (by simp))
  norm_num at h ⊢
  exact h

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem big_K (HP : FourthRootHierarchyParams 16 1 16 32 8) : 1 < HP.K := by
  have h := HP.gate
  have hnonneg : 0 ≤ 32 * (HP.k : ℝ) / HP.η :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) HP.η_pos.le
  have hh : (1 : ℝ) < HP.K := by linarith
  exact_mod_cast hh

-- Arbitrary earlier estimates need no desired output certificate for actual range/support.
-- The parameter assumptions are inhabited by the library's fourth-root hierarchy witness.
example : Nonempty (FourthRootHierarchyParams 16 1 16 32 8) :=
  Matrix.FourthRootHierarchyParams.nonempty (by norm_num) (by norm_num)

-- Literal zero base survives the complete actual substitution, even with nonzero children.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    incomingChildren HP 1 (fun (_ : Unit) => 0) 2 (fun _ => 1)
      (fun (_ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) _ _ _ => 7)
      (fun _ _ _ _ => 3) (fun _ _ _ => 1)
      ⟨.row 0 (.correction 0), gridChannel 0 0 [1], gridChannel 1 0 [2],
        gridChannel 1 0 [2]⟩ σ () () = 0 := rfl

-- Actual selected incoming correction, on a full P=5 rank environment with a spectator.
-- The row rank is the hierarchy's real K, rather than a replacement rank of two.
private theorem actual_positive_child (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin 3) (hst : s ≠ t) (ss st : List (ZMod 5)) (σ : Environment 5 3) :
    correctionRequest 1 (fun (_ : Unit) => 0)
      (⟨.row 0 (.normalized 0), gridChannel s 0 ss, gridChannel t 0 st,
        gridChannel t 0 st⟩ : HierarchyTask.Request 1 (Fin 3) (ZMod 5))
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K 2 (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => 0) σ () () = HP.Q 1 := by
  have hr : Admissible (⟨.row 0 (.normalized 0), gridChannel s 0 ss,
      gridChannel t 0 st, gridChannel t 0 st⟩ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) :=
    ⟨hst, rfl, rfl⟩
  have hs : side 5 0 = 5 := by norm_num [side]
  have hcap := HP.toHierarchyParams.atomCutoff_eq (by norm_num : (0:ℝ) ≤ 1)
    (by have := Nat.cast_nonneg (α := ℝ) HP.k; linarith)
  unfold correctionRequest
  rw [dite_eq_left hr]
  dsimp only
  simp only [CorrectionRowRecipe.normalized, coordinate, gridChannel,
    semanticSide_grid, hs, full_retains, ↓reduceIte]
  have hτ : HP.incomingCutoff 0 = 1 :=
    HP.incomingCutoff_one (by rw [HP.τ₀_eq]; norm_num)
  norm_num [rate, rowGate, kthLargest, not_le.mpr (big_K HP), incomingGate,
    CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le, hτ,
    HP.γ_one 0 (by norm_num), hcap]


example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    0 < correctionRequest 1 (fun (_ : Unit) => 0)
      (⟨.row 0 (.normalized 0), gridChannel 0 0 [1], gridChannel 1 0 [2],
        gridChannel 1 0 [2]⟩ : HierarchyTask.Request 1 (Fin 3) (ZMod 5))
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K 2 (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ => 0) σ () () := by
  rw [actual_positive_child HP 0 1 (by decide)]
  exact CutoffRegression.Q_one_pos HP

private theorem actual_dense_child (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin 3) (hst : s ≠ t) (ss st : List (ZMod 5)) (σ : Environment 5 3) :
    normalizedRequest 1 (fun (_ : Unit) => 0)
      (⟨HierarchyTask.baseNormalized 0 0, gridChannel s 0 ss, gridChannel t 0 st,
        gridChannel t 0 st⟩ : HierarchyTask.Request 1 (Fin 3) (ZMod 5))
      (fun _ => 1) HP.ρ HP.K (fun _ _ _ => 1) (fun _ _ _ => 1) σ () () = 1 := by
  have hr : Admissible (⟨HierarchyTask.baseNormalized 0 0, gridChannel s 0 ss,
      gridChannel t 0 st, gridChannel t 0 st⟩ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) :=
    ⟨hst, rfl, rfl⟩
  have hs : side 5 0 = 5 := by norm_num [side]
  unfold normalizedRequest
  rw [dite_eq_left hr]
  dsimp only
  simp only [DenseRowRecipe.normalized, coordinate, gridChannel,
    semanticSide_grid, hs, full_retains, ↓reduceIte]
  norm_num [rate, rowGate, kthLargest, not_le.mpr (big_K HP),
    CorrectionRowRecipe.normalizer, HP.ρ_one 0 HP.η_pos.le]

-- The complete signed residual is one; its actual product contribution is Q(1)>0.
-- All three rank coordinates remain present and both copied suffixes are nonempty.
theorem actual_residual_one (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 3) :
    rawIncomingNormalized HP 1 (fun (_ : Unit) => 0) threeRoles 0 0 0 0 0 0 [1] [2] [3]
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 (fun _ => 1)
      (fun (_ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) _ _ _ => 1)
      (fun _ _ _ _ => 1) (fun _ _ _ => 0) σ () () = 1 := by
  have hs : side 5 0 = 5 := by norm_num [side]
  have ht : HierarchyTask.correctionAtomTask (k := 1) 0 false (Fin.last 1) =
      .row 0 (.normalized 0) := rfl
  simp only [rawIncomingNormalized, HierarchyTask.rawSample, HierarchyTask.rawPositiveSample,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests, ht]
  dsimp only [threeRoles]
  simp only [gridChannel, min_self]
  have hd := actual_dense_child HP 0 2 (by decide) [1] [3] σ
  have hb := actual_dense_child HP 1 2 (by decide) [2] [3] σ
  have ha := actual_positive_child HP 0 1 (by decide) [1] [2] σ
  have hn := actual_positive_child HP 0 2 (by decide) [1] [3] σ
  dsimp only [gridChannel] at hd hb ha hn
  simp only [Fintype.sum_unique]
  rw [hd, hb, ha, hn]
  have hside : semanticSide 5 1 = 5 := by
    simpa only [rate, pow_zero, inv_one, one_pow, hs] using semanticSide_grid 5 0
  norm_num [HierarchyTask.usageRatio, CorrectionRowTask.Channel.retains, channels,
    gridChannel, threeRoles, semanticSide_grid, hs, full_retains, rate, hside, ZMod.val_lt]

-- The actual signed sample has a nonzero integrated input moment, not just a positive atom.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rowNormPow 4 1 1
      (X (0 : Fin 3) (side 5 0) (fun (_ : Unit) => CopyPadding.identifier 1 [1] 0))
      (Y (2 : Fin 3) (side 5 0) (fun (_ : Unit) => CopyPadding.identifier 1 [3] 0))
      (rawIncomingNormalized HP 1 (fun (_ : Unit) => 0) threeRoles
        0 0 0 0 0 0 [1] [2] [3] (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2
        (fun _ => 1) (fun (_ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) _ _ _ => 1)
        (fun _ _ _ _ => 1) (fun _ _ _ => 0)) = 1 := by
  have hs : side 5 0 = 5 := by norm_num [side]
  have heq : rawIncomingNormalized HP 1 (fun (_ : Unit) => 0) threeRoles
      0 0 0 0 0 0 [1] [2] [3] (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2
      (fun _ => 1) (fun (_ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) _ _ _ => 1)
      (fun _ _ _ _ => 1) (fun _ _ _ => 0) = fun _ _ _ => 1 := by
    funext σ x y
    cases x
    cases y
    exact actual_residual_one HP σ
  rw [heq]
  norm_num [rowNormPow, X, Y, hs, full_retains, ZMod.val_lt]

-- A consumer unfolds only the explicit lower-child payment, never the final input norm.
theorem actual_budget (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    incomingMomentBudget HP 1 (fun (_ : Unit) => 0) threeRoles 0 0 0 0 0 0 [1] [2] [3]
      2 (fun _ => 1) (fun (_ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) _ _ _ => 1)
      (fun _ _ _ _ => 1) (fun _ _ _ => 0) 1 1 =
      64 * (1 + (HP.K : ℝ) ^ 3 * (2 * HP.Q HP.toHierarchyParams.atomCap) ^ 4 * 2 +
        |HP.Q 1| ^ 4) := by
  have hs : side 5 0 = 5 := by norm_num [side]
  have ht : HierarchyTask.correctionAtomTask (k := 1) 0 false (Fin.last 1) =
      .row 0 (.normalized 0) := rfl
  have hd := actual_dense_child HP 0 2 (by decide) [1] [3]
  have hb := actual_dense_child HP 1 2 (by decide) [2] [3]
  have hn := actual_positive_child HP 0 2 (by decide) [1] [3]
  dsimp only [gridChannel] at hd hb hn
  norm_num only [rate, pow_zero, inv_one, one_pow] at hd hb hn
  unfold incomingMomentBudget
  simp only [HierarchyTask.rawRequests, ht, incomingChildren, threeRoles, gridChannel,
    min_self]
  have hside : semanticSide 5 1 = 5 := by
    simpa only [rate, pow_zero, inv_one, one_pow, hs] using semanticSide_grid 5 0
  norm_num [rowNormPow, Fintype.sum_unique, hd, hb, hn, HierarchyTask.usageRatio,
    CorrectionRowTask.Channel.retains, channels, semanticSide_grid, hs, full_retains,
    rate, hside, ZMod.val_lt]

-- Complete actual-noise client: the only payment is the evaluated lower-child budget.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let a := fun (_ : Unit) => CopyPadding.identifier (1 : ZMod 5) [1] 0
    let b := fun (_ : Unit) => CopyPadding.identifier (1 : ZMod 5) [3] 0
    let F := rawIncomingNormalized HP 1 (fun (_ : Unit) => 0) threeRoles
      0 0 0 0 0 0 [1] [2] [3] (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2
      (fun _ => 1) (fun (_ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) _ _ _ => 1)
      (fun _ _ _ _ => 1) (fun _ _ _ => 0)
    let G := graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0)
      (side_le 5 0) (side_le 5 0) a b
    rowNormPow 4 1 1 (X (0 : Fin 3) (side 5 0) a) (Y 2 (side 5 0) b)
      (fun σ x y => conditionalWalk (X (0 : Fin 3) (side 5 0) a)
        (Y 2 (side 5 0) b) G (fun _ _ => 1) F σ x y -
        rowSliceMean (X (0 : Fin 3) (side 5 0) a) (Y 2 (side 5 0) b) F x y) ≤
      32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)) ^ 2 *
        (64 * (1 + (HP.K : ℝ) ^ 3 * (2 * HP.Q HP.toHierarchyParams.atomCap) ^ 4 * 2 +
          |HP.Q 1| ^ 4)) := by
  have h := rawIncomingNormalized_noise_le_lower HP
    (lt_trans (by decide : 0 < 1) (big_K HP)) 1 (fun (_ : Unit) => 0) threeRoles
    0 0 0 0 0 0 [1] [2] [3] 2 (by decide) (fun _ => 1)
    (fun (_ : HierarchyTask.Request 1 (Fin 3) (ZMod 5)) _ _ _ => 1)
    (fun _ _ _ _ => 1) (fun _ _ _ => 0) (N := 1) (u := 1) (by norm_num) (by norm_num) 1
  dsimp only at h
  rw [actual_budget] at h
  exact h

end
