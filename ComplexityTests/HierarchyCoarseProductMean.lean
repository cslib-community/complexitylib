/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of signed hierarchy domination and clipped products)
import Complexity.Foundations.Probability.HierarchyCoarseProductMean
import all ComplexityTests.HierarchyTerminalMean

/-!
The non-unit finite hierarchy has positive E and EC and genuine signed cancellation.
The old correlated/reset-source terminal clients remain imported. Supplied-history
execution below is explicitly distinct from simultaneous recursive compression.
No positive-precision joint fixed-charge allocation is asserted.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace CoarseProductMeanRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private def B := TerminalMeanRegression.smallData HP
private def r := TerminalMeanRegression.request HP
private def E := TerminalMeanRegression.smallE HP
private def G := HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
  (canonicalChannel id (rate 1)) (rate 1) (B HP).base

-- Cancellation is real: the positive input is strictly larger than the final residual.
-- The structural ramp-gap bound, rather than coefficient one, supplies domination.
example (x : ZMod 5) :
    0 < E HP x x ∧ 0 < (E HP * (B HP).base) x x ∧
    G HP x x < ((B HP).base + E HP * (B HP).base) x x ∧
    ((B HP).base + E HP * (B HP).base) x x ≤
      max 1 (((HP.k : ℝ) + 1) / HP.θ) * G HP x x := by
  have he := TerminalMeanRegression.small_correction_pos HP x
  change 0 < E HP x x at he
  have heq : E HP = HP.toHierarchyParams.correction
      (canonicalChannel id (rate 1)) (canonicalChannel id (rate 1))
      (rate 1) (B HP).base := HP.toHierarchyParams.correctionIter_last _ _ _ _
  have hm : (E HP * (B HP).base) x x = rate 1 * E HP x x := by
    simp only [B, TerminalMeanRegression.smallData, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_apply, smul_eq_mul]
  refine ⟨he, by rw [hm]; exact mul_pos (rate_pos 1) he, ?_, ?_⟩
  · rw [G, HP.toHierarchyParams.residual_eq, ← heq]
    simp only [Matrix.add_apply, Matrix.sub_apply]
    linarith
  · have h := HP.toHierarchyParams.correctionInput_last_le_residual
      (canonicalChannel id (rate 1)) (canonicalChannel id (rate 1)) (rate_pos 1)
      (TerminalMeanRegression.small_nonneg HP) (TerminalMeanRegression.small_mass HP)
      (TerminalMeanRegression.small_stage HP) x x
    exact h

-- The genuine normalized signed target is used at both the coarse boundary and fine edge.
-- The bin importance and density in residualProductMean have not been stripped off.
example (i : ℕ) (hi : i ∈ (B HP).bins) (hiH : i ≤ SourceRegression.horizon.maxExponent)
    (x y : ZMod 5) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual (r HP).source
      (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate i)
    (B HP).residualProductMean i (r HP) ((B HP).residualCanonicalChild i Q.left)
      ((B HP).residualCanonicalChild i Q.right) x y ≤
      max 1 (((HP.k : ℝ) + 1) / HP.θ) * G HP x y := by
  exact (B HP).residualProductMean_canonical_le_residual 1
    (by ext j; simp [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data]; omega)
    rfl rfl rfl (by norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data]) SourceRegression.horizon
    (r HP) 0 2 (by decide) 2 1 [1] [2, 3] rfl rfl (by decide) (by decide)
    (TerminalMeanRegression.small_nonneg HP) (TerminalMeanRegression.small_mass HP)
    (TerminalMeanRegression.small_stage HP) i hi hiH x y

-- A zero base gives an actual zero correction/input/residual, not arbitrary target agreement.
example : HP.toHierarchyParams.correctionInput (canonicalChannel id (rate 1))
    (canonicalChannel id (rate 1)) (rate 1) (0 : Matrix (ZMod 5) (ZMod 5) ℝ) HP.k = 0 ∧
    HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (0 : Matrix (ZMod 5) (ZMod 5) ℝ) = 0 := by
  have hz : HP.toHierarchyParams.correction (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (0 : Matrix (ZMod 5) (ZMod 5) ℝ) = 0 := by
    ext x y
    have h := (HP.toHierarchyParams.isCorrectionSeq_correctionIter
      (X := canonicalChannel id (rate 1)) (Y := canonicalChannel id (rate 1))
      (C := (0 : Matrix (ZMod 5) (ZMod 5) ℝ))
      (rate_pos 1) (by intros; rfl)).le_mul
        (f := 0) (by intros; rfl) le_rfl (by simp) HP.k x y
    have hn := (HP.toHierarchyParams.isCorrectionSeq_correctionIter
      (X := canonicalChannel id (rate 1)) (Y := canonicalChannel id (rate 1))
      (C := (0 : Matrix (ZMod 5) (ZMod 5) ℝ))
      (rate_pos 1) (by intros; rfl)).nonneg HP.k x y
    rw [HP.toHierarchyParams.correctionIter_last] at h hn
    simp only [mul_zero] at h
    exact le_antisymm h hn
  simp [correctionInput, HP.toHierarchyParams.residual_eq, hz]

-- Rounded nontrivial density: one power at the coarse boundary, with no field width loss.
example : (rate 0 * (rate 1 / gridMass 5 1)) *
    (gridMass 5 1 / gridMass 5 (max 1 0)) / rate 1 = (625 / 81 : ℝ) ∧
    (rate 1 * (rate 1 / gridMass 5 1)) *
      (gridMass 5 1 / gridMass 5 (max 1 1)) / rate 1 = (625 / 1296 : ℝ) := by
  norm_num [rate, gridMass, side, Nat.ceilDiv_eq_add_pred_div]

-- The fine edge keeps the narrower reset-right usage mass, rather than replacing
-- rounded masses by nominal rates. Ordinary fine decay is a separate comparison.
example : (rate 2 * (rate 1 / gridMass 5 1)) *
    (gridMass 5 1 / gridMass 5 (max 1 2)) / rate 1 = (625 / 4096 : ℝ) ∧
    (rate 2 / gridMass 5 1) ^ 4 * (gridMass 5 1 / gridMass 5 2) =
      (625 / 20736 : ℝ) ^ 4 * (81 / 16) := by
  norm_num [rate, gridMass, side, Nat.ceilDiv_eq_add_pred_div]

-- A conditional successful-call client at two unequal budgets. Both factors may
-- depend on every common environment coordinate. This does not construct recursive
-- availability; the successful evaluations, unlike the supplied-history test, are premises.
private def Q := HierarchyTask.rawRequests (k := HP.k) 0 1 .residual (r HP).source
  (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate 1)
example (M k : ℕ) (ζ floor : ℝ)
    (L R : Fin 2 → Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (hL : ∀ j, (B HP).evaluate ((B HP).binBudget (M + j.val) 1 (r HP))
      (Q HP).left = some (.row (L j)))
    (hR : ∀ j, (B HP).compressedBin ((B HP).binBudget (M + j.val) 1 (r HP))
      1 k ζ floor (Q HP).right = some (R j))
    (εL εR : Fin 2 → ℝ)
    (hEL : ∀ j, rootDistPow 4 5 (r HP).source.rate
      (fun σ x => (r HP).source.retains (channels (B HP).padding) σ x)
      (fun σ z => (BudgetData.midpoint (r HP)).retains (channels (B HP).padding) σ z)
      (L j) ((B HP).residualCanonicalChild 1 (Q HP).left) ≤ εL j ^ 4)
    (hER : ∀ j, rootDistPow 4 5 (r HP).terminal.rate
      (fun σ z => (BudgetData.midpoint (r HP)).retains (channels (B HP).padding) σ z)
      (fun σ y => (Q HP).right.usage.retains (channels (B HP).padding) σ y)
      (R j) ((B HP).residualCanonicalChild 1 (Q HP).right) ≤ εR j ^ 4) :
    let A := fun j => (B HP).residualProductMean 1 (r HP) (L j) (R j)
    let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
    let pay := fun j => (512 * (3 * K + 3) ^ 3) * (625 / 1296) * 33554432 *
      ((2 * (B HP).binCap) * HP.K * εL j ^ 4 +
        (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ * 16 * εR j ^ 4)
    rowNormPow 4 5 (r HP).source.rate
      (fun σ x => (r HP).source.retains (channels (B HP).padding) σ x)
      (fun σ y => (r HP).terminal.retains (channels (B HP).padding) σ y)
      (fun _ x y => min 1 (|A 0 x y - A 1 x y| / (rate 1 + G HP x y))) ≤
      8 * (pay 0 + pay 1) := by
  have hθ : HP.θ ≤ (1 / 2 : ℝ) := by
    have h := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at h
    linarith
  have hl (d : ℝ) (hd : d ≤ HP.θ) : (B HP).cutoff 1 d = 0 := by
    change boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) rate 1 1
      (fun _ => 1) d = 0
    exact boundedRoutedBinCutoff_eq_zero (by norm_num)
      (fun v hv => polynomialSwitch4_of_le (by norm_num) hv) rate_pos rate_antitone
      (hd.trans hθ) 1 (fun _ => 1)
  have h := (B HP).residualProduct_parent_clipped_pair_le 1
    (by ext j; simp [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data]; omega)
    rfl rfl rfl (by norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data]) SourceRegression.horizon
    (fun j : Fin 2 => M + j.val) 1 k 2 1 ζ floor (r HP)
    (by change (0 : Fin 3) ≠ 2; decide) rfl rfl rfl
    (by decide) (by decide) (by simp [B, TerminalMeanRegression.smallData,
      TerminalMeanRegression.data, ProductMeanRegression.data, PolynomialBudgetHistory.data])
    (by decide) (TerminalMeanRegression.small_nonneg HP) (TerminalMeanRegression.small_mass HP)
    (TerminalMeanRegression.small_stage HP) hl L R hL hR εL εR hEL hER
  dsimp only at h ⊢
  convert h using 1 <;>
    norm_num [B, r, G, TerminalMeanRegression.smallData, TerminalMeanRegression.request,
      TerminalMeanRegression.data, ProductMeanRegression.data, PolynomialBudgetHistory.data,
      gridChannel, gridMass, side, Nat.ceilDiv_eq_add_pred_div, rate]; ring

-- Literal equal-budget paired execution requires no recursive child availability.
example (d : ℕ) : (B HP).pairedSample (fun _ _ => none) 0 d .residual (r HP)
    (some 1) = some 0 := by
  simp [BudgetData.pairedSample, LogSpaceEstimation.lastBudget]

end CoarseProductMeanRegression
