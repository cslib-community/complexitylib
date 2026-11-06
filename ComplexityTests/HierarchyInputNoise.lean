/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of positive-only actual INPUT noise)
import Complexity.Foundations.Probability.HierarchyInputNoise
import all ComplexityTests.HierarchyInputProduct

/-!
# Finite production noise on genuine requested INPUT one

The inherited P=5 fixture has E₁>0 and E₁*C>0, actual normalized children,
a nonconstant direct perturbation, inherited suffixes, reset-right source and
unequal rates/budgets. Supplied histories establish execution, not recursive IH.
The finite endpoint allowances below are computed moments, not a target-noise
assumption or a uniform precision-decay allocation.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace InputNoiseRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private abbrev B := InputProductRegression.data HP
private abbrev idx := InputProductRegression.iteration HP
private abbrev req := InputProductRegression.request HP
private abbrev hist := InputProductRegression.history HP
private abbrev G := InputProductRegression.G HP
private def X : Environment 5 3 → ZMod 5 → Prop :=
  NormalizedMoments.retainedMask 0 (side 5 1) (B HP).padding [1]
private def Y : Environment 5 3 → ZMod 5 → Prop :=
  NormalizedMoments.retainedMask 2 (side 5 0) (B HP).padding [2, 3]
private lemma nu : 0 ≤ (5 : ℝ) * (req HP).source.rate :=
  mul_nonneg (by norm_num) (rate_pos 1).le

private lemma samples (m : ℕ) (bin : Option ℕ) :
    ∃ A, (B HP).sample (hist HP) m (.input (idx HP)) (req HP) bin = some A := by
  by_cases hm : m = 0
  · subst m; exact ⟨0, (B HP).sample_zero _ _ _ _⟩
  cases bin with
  | none => simp [BudgetData.sample, hm]
  | some b =>
    simp only [BudgetData.sample, hm, ↓reduceIte]
    exact ⟨_, (B HP).positiveSample_of_rows (hist HP) m b (.input (idx HP)) (req HP)
      (InputProductRegression.child HP) (by intros; exact InputProductRegression.rows HP _ _)⟩

/-- Computed finite endpoint fourth roots retain the actual denominator and masks. -/
private def e (_i m : ℕ) (bin : Option ℕ) : ℝ :=
  (rowNormPow 4 5 (req HP).source.rate (X HP) (Y HP) (fun σ x y =>
    (((B HP).sample (hist HP) m (.input (idx HP)) (req HP) bin).getD 0 σ x y -
      (B HP).inputCanonicalRay (idx HP) (req HP) bin σ x y) / (rate 0 + G HP x y))) ^
        ((4 : ℝ)⁻¹)
private lemma e_nonneg (i m : ℕ) (bin : Option ℕ) : 0 ≤ e HP i m bin :=
  Real.rpow_nonneg (rowNormPow_nonneg (nu HP) _) _
private lemma endpoint (i m : ℕ) (bin : Option ℕ) :
    rowNormPow 4 5 (req HP).source.rate (X HP) (Y HP) (fun σ x y =>
      (((B HP).sample (hist HP) m (.input (idx HP)) (req HP) bin).getD 0 σ x y -
        (B HP).inputCanonicalRay (idx HP) (req HP) bin σ x y) / (rate 0 + G HP x y)) ≤
      e HP i m bin ^ 4 := by
  exact le_of_eq (Real.rpow_inv_natCast_pow (rowNormPow_nonneg (nu HP) _)
    (by decide : (4 : ℕ) ≠ 0)).symm

-- Complete actual production first-channel decoder consumer at positive precision.
-- The allowance is finite, request-specific, and computed from endpoint errors.
example (i : ℕ) (hi : i < Nat.log2 64 + 1)
    (second : Environment 5 3 → ZMod 5 → ℕ → ZMod 5 → ℝ) :
    rowNormPow 4 5 (req HP).source.rate (X HP) (Y HP)
      (NormalizedMoments.actualNoiseEntry 0 2 (side 5 1) (side 5 0) (side 5 0)
        (B HP).padding [1] [2, 3] 0 (G HP)
        (NormalizedMoments.firstSignalIncrement
          ((B HP).rawFirstPrefixes (hist HP) 64 (.input (idx HP)) (req HP)) 0 second) 0 0 i) ≤
      (B HP).inputFiniteNoisePayment (idx HP) 64 (req HP) 0 2 (by decide)
        1 0 [1] [2, 3] (G HP) (i + 1) (e HP) := by
  apply (B HP).rawFirstPrefixes_input_finite_noise (idx HP) (hist HP) 64 (req HP)
    0 2 (by decide) 1 0 [1] [2, 3] rfl rfl rfl
    (fun _ _ bin _ _ => ⟨fun _ => samples HP _ bin, fun _ => samples HP _ bin⟩)
    (G HP) (InputProductRegression.G_nonneg HP) second i hi (e HP) (e_nonneg HP)
  intro l _ bin _ m _ _
  exact endpoint HP l m bin

-- Supplied-history RAW really executes; this does not establish evaluate availability.
example : ∃ A, (B HP).raw (hist HP) 64 (.input (idx HP)) (req HP) = some A := by
  apply (B HP).raw_available (hist HP) 64 (.input (idx HP)) (req HP)
    0 2 (by decide) 1 0 [1] [2, 3] rfl rfl
  intro j _ bin _
  dsimp only
  intro _
  exact ⟨samples HP _ bin, samples HP _ bin⟩

-- Active/exhausted boundary keeps the WHOLE positive reference, not a negative E.
example :
    (B HP).inputBoundaryCoefficient 64 32 (req HP) (some 0) = 1 ∧
    (B HP).pairedSample (hist HP) 64 32 (.input (idx HP)) (req HP) (some 0) =
      (B HP).sample (hist HP) 32 (.input (idx HP)) (req HP) (some 0) := by
  have hf : LogSpaceEstimation.lastBudget 64 32 (B HP).slack
      ((B HP).sampleScale (req HP) (some 0)) = 32 := by
    norm_num [InputProductRegression.data, PolynomialBudgetHistory.data,
      BudgetData.sampleScale, req, InputProductRegression.request,
      LaterInputMeanRegression.request, ProductMeanRegression.request,
      PolynomialBudgetHistory.request, gridChannel, rate,
      LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  have hc : LogSpaceEstimation.lastBudget 64 (2 * 32) (B HP).slack
      ((B HP).sampleScale (req HP) (some 0)) = 0 := by
    unfold LogSpaceEstimation.lastBudget; omega
  obtain ⟨A, hA⟩ := samples HP 32 (some 0)
  simp [BudgetData.inputBoundaryCoefficient, BudgetData.pairedSample, hf, hc,
    BudgetData.sample_zero, hA]

-- Before the boundary the semantic term cancels, but actual endpoint errors are separate.
example : (B HP).inputSemanticGroupInput (idx HP) 64 8 (req HP) = 0 :=
  (B HP).inputSemanticGroupInput_eq_zero_of_two_mul_lt (idx HP) 64 8 (req HP) (by decide)

-- Full exhaustion pays no own-root accuracy at zero and makes no history calls.
example : (B HP).inputEndpointRootSum 64 64 (req HP) (e HP 0) = 0 ∧
    (B HP).decodedGroupInput (hist HP) 64 64 (.input (idx HP)) (req HP) = 0 :=
  ⟨(B HP).inputEndpointRootSum_eq_zero_of_le 64 64 (req HP) _ le_rfl,
    (B HP).decodedGroupInput_input_eq_zero_of_le (idx HP) (hist HP) 64 64 (req HP) le_rfl⟩

-- No bin list can secretly insert the residual negative correction.
example : none ∉ (B HP).rays (.input (idx HP)) := by simp [BudgetData.rays]

-- Empty positive bins have no semantic or endpoint cost, unlike residual rays.
example (B' : BudgetData HP 5) (hb : B'.bins = ∅) (M d : ℕ) :
    B'.inputSemanticGroupInput (idx HP) M d (req HP) = 0 ∧
    B'.inputEndpointRootSum M d (req HP) (e HP 0) = 0 := by
  constructor
  · funext σ x y; simp [BudgetData.inputSemanticGroupInput, BudgetData.rays, hb]
  · simp [BudgetData.inputEndpointRootSum, hb]

-- The actual input-one endpoint consumes the previously derived own-root product
-- transport, with nonzero direct error; positive endpoint moments are not free.
example (m : ℕ) : ∃ A,
    (B HP).positiveSample (hist HP) m 0 (.input (idx HP)) (req HP) = some A ∧
    rowNormPow 4 5 (req HP).source.rate (InputProductRegression.X HP)
      (fun _ _ => True) (fun σ x y =>
        (A σ x y - (B HP).inputCanonicalRay (idx HP) (req HP) (some 0) σ x y) /
          ((req HP).terminal.rate + G HP x y)) ≤ InputProductRegression.payment HP :=
  InputProductRegression.executed_bound HP m

-- At the active/exhausted boundary all finite positive canonical rays survive.
-- Their conditional mean is G=C+E₁*C>0, even with exact positive endpoint children.
private lemma boundary (σ : Environment 5 3) (x y : ZMod 5) :
    (B HP).inputSemanticGroupInput (idx HP) 64 32 (req HP) σ x y =
      ∑ b ∈ (B HP).bins, (B HP).inputCanonicalRay (idx HP) (req HP) (some b) σ x y := by
  have hlog : Real.logb 2 (1 / 16 : ℝ) = -4 := by
    rw [one_div, Real.logb_inv, show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
      Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  have hend (bin : ℕ) (hb : bin ∈ (B HP).bins) :
      LogSpaceEstimation.lastBudget 64 32 (B HP).slack
        ((B HP).sampleScale (req HP) (some bin)) = 32 := by
    have hbin : bin = 0 ∨ bin = 1 := by
      simpa only [InputProductRegression.data, PolynomialBudgetHistory.data,
        mem_insert, mem_singleton] using hb
    rcases hbin with rfl | rfl <;>
      norm_num [InputProductRegression.data, PolynomialBudgetHistory.data,
        BudgetData.sampleScale, req, InputProductRegression.request,
        LaterInputMeanRegression.request, ProductMeanRegression.request,
        PolynomialBudgetHistory.request, gridChannel, rate,
        LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, hlog]
  have hc (bin : ℕ) : LogSpaceEstimation.lastBudget 64 (2 * 32) (B HP).slack
      ((B HP).sampleScale (req HP) (some bin)) = 0 := by
    unfold LogSpaceEstimation.lastBudget; omega
  simp only [BudgetData.inputSemanticGroupInput, BudgetData.rays, List.append_nil,
    List.map_map, Function.comp_def, sum_map_toList]
  apply sum_congr rfl
  intro b hb
  rw [hend b hb, hc]
  norm_num

example (x : ZMod 5) :
    0 < rowSliceMean
      (fun σ x => (req HP).source.retains (channels (B HP).padding) σ x)
      (fun σ y => (req HP).terminal.retains (channels (B HP).padding) σ y)
      ((B HP).inputSemanticGroupInput (idx HP) 64 32 (req HP)) x x := by
  have hid : (B HP).inputSemanticGroupInput (idx HP) 64 32 (req HP) =
      fun σ x y => ∑ b ∈ (B HP).bins,
        (B HP).inputCanonicalRay (idx HP) (req HP) (some b) σ x y := by
    funext σ x y; exact boundary HP σ x y
  rw [hid]
  have hm := LaterInputMeanRegression.canonical_mean HP x x
  change rowSliceMean
    (fun σ x => (req HP).source.retains (channels (B HP).padding) σ x)
    (fun σ y => (req HP).terminal.retains (channels (B HP).padding) σ y)
    (fun σ x y => ∑ b ∈ (B HP).bins,
    (B HP).inputCanonicalRay (idx HP) (req HP) (some b) σ x y) x x = G HP x x at hm
  rw [hm]
  have he := LaterInputMeanRegression.correction_one HP x
  change 0 < (B HP).base x x + (LaterInputMeanRegression.E HP * (B HP).base) x x
  rw [show LaterInputMeanRegression.E HP * (B HP).base = LaterInputMeanRegression.E HP
    from Matrix.mul_one _, he, show (B HP).base x x = 1 from Matrix.one_apply_eq x]
  linarith only [CutoffRegression.Q_one_pos HP]

-- Equal exhausted endpoints execute no child calls, even with unavailable history.
example : (B HP).pairedSample (fun _ _ => none) 64 64 (.input (idx HP))
    (req HP) (some 0) = some 0 := by
  have hz (d : ℕ) (hd : 64 ≤ d) : LogSpaceEstimation.lastBudget 64 d (B HP).slack
      ((B HP).sampleScale (req HP) (some 0)) = 0 := by
    unfold LogSpaceEstimation.lastBudget; omega
  simp only [BudgetData.pairedSample, hz 64 le_rfl, hz (2 * 64) (by omega), ↓reduceIte]

end InputNoiseRegression
