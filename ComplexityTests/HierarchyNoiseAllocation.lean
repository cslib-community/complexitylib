/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of literal endpoint noise allocation)
import Complexity.Foundations.Probability.HierarchyNoiseAllocation
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import all ComplexityTests.HierarchyEndpointNoise

/-!
The growing zero-bin extension has ratio-16 ranks and exact zero positive
endpoints: no unsupported bin horizon or recursive success is inferred. Its
negative ray retains positive unequal endpoints and positive precision. The
counterexample concerns the c748 count envelope over these extensions only;
a common horizon for all exhausted listed bins is not asserted. The nonzero executed
fixture below reuses the genuine-reference family, not a fabricated canonical IH.
Execution fixtures adapt Samuel Schlesinger's whole-environment tests.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace NoiseAllocationRegression

private def zeroData (HP : FourthRootHierarchyParams 16 1 16 32 8) : BudgetData HP 5 :=
  { PolynomialBudgetHistory.data HP with
    cutoff := fun _ _ => 0
    binCap := 0
    binCap_nonneg := le_rfl
    cutoff_bounds := fun _ _ => ⟨le_rfl, le_rfl⟩ }

private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) :=
  RawNoiseSplitRegression.request HP

-- Every added bin is literally exhausted at BOTH endpoints, so there is no
-- positive-bin success or accuracy/horizon premise. The negative endpoints
-- remain 63 and 62. The source/terminal request is admissible, at positive precision.
private theorem exhausted_geometry (HP : FourthRootHierarchyParams 16 1 16 32 8) (n : ℕ) :
    let B := {zeroData HP with bins := (range n).image (fun i => i + 64)}
    Admissible (request HP) ∧ 0 < B.requestPrecision 64 (request HP) ∧
      LogSpaceEstimation.lastBudget 64 1 B.slack (B.sampleScale (request HP) none) = 63 ∧
      LogSpaceEstimation.lastBudget 64 2 B.slack (B.sampleScale (request HP) none) = 62 ∧
      ∀ i ∈ B.bins, ∀ d,
        LogSpaceEstimation.lastBudget 64 d B.slack (B.sampleScale (request HP) (some i)) = 0 := by
  dsimp only
  refine ⟨⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · norm_num [requestPrecision, LogSpaceEstimation.precision, zeroData,
      PolynomialBudgetHistory.data, request, RawNoiseSplitRegression.request,
      PolynomialBudgetHistory.request, gridChannel, rate]
  · rw [sampleScale_none_eq_zero]; rfl
  · rw [sampleScale_none_eq_zero]; rfl
  · intro i hi d
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    have hscale := sampleScale_grid
      ({zeroData HP with bins := (range n).image (fun i => i + 64)} : BudgetData HP 5)
      (request HP) 0 (j + 64) rfl rfl
    rw [hscale]
    apply LogSpaceEstimation.lastBudget_eq_zero_of_cutoff_le
    simp only [LogSpaceEstimation.scaleCutoff, zeroData, PolynomialBudgetHistory.data,
      Int.natCast_zero, zero_sub, Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast,
      show (4 : ℤ).natAbs = 4 from rfl]
    omega

-- Even an arbitrary history is never consulted by these exhausted added bins.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (n : ℕ)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5)) :
    let B := {zeroData HP with bins := (range n).image (fun i => i + 64)}
    ∀ i ∈ B.bins, ∀ d,
      B.sample history (LogSpaceEstimation.lastBudget 64 d B.slack
        (B.sampleScale (request HP) (some i))) .residual (request HP) (some i) = some 0 := by
  dsimp only
  intro i hi d
  rw [(exhausted_geometry HP n).2.2.2.2 i hi d]
  exact sample_zero _ _ _ _ _

-- The production walk length is unchanged by these zero-bin extensions.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (n M d : ℕ) :
    let B := {zeroData HP with bins := (range n).image (fun i => i + 64)}
    B.steps M (request HP) d = (zeroData HP).steps M (request HP) d := by
  dsimp only
  have hm := magnitude_eq_of_zero_binCap
    ({zeroData HP with bins := (range n).image (fun i => i + 64)} : BudgetData HP 5)
    (request HP) rfl
  have hm' := (zeroData HP).magnitude_eq_of_zero_binCap (request HP) rfl
  simp only [steps, hm, hm']
  rfl

-- The entire uncompleted RAW input is also unchanged: each new positive ray
-- is exactly zero, for every history, at every group slack.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (n d : ℕ)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5)) :
    let B := {zeroData HP with bins := (range n).image (fun i => i + 64)}
    let D := {zeroData HP with bins := ∅}
    B.decodedGroupInput history 64 d .residual (request HP) =
      D.decodedGroupInput history 64 d .residual (request HP) := by
  dsimp only
  let B : BudgetData HP 5 :=
    {zeroData HP with bins := (range n).image (fun i => i + 64)}
  funext σ x y
  have hz : ((B.bins.toList.map some).map (fun bin =>
      ((B.sample history (LogSpaceEstimation.lastBudget 64 d B.slack
        (B.sampleScale (request HP) bin)) .residual (request HP) bin).getD 0 σ x y) -
      ((B.sample history (LogSpaceEstimation.lastBudget 64 (2 * d) B.slack
        (B.sampleScale (request HP) bin)) .residual (request HP) bin).getD 0 σ x y))).sum = 0 := by
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨bin, hb, rfl⟩ := List.mem_map.mp hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' : i ∈ B.bins := mem_toList.mp hi
    rw [(exhausted_geometry HP n).2.2.2.2 i hi' d,
      (exhausted_geometry HP n).2.2.2.2 i hi' (2 * d)]
    simp [B.sample_zero]
  change ((B.rays .residual).map _).sum = _
  simp only [rays, List.map_append, List.sum_append] at *
  rw [hz, zero_add]
  simp only [decodedGroupInput, rays, Finset.toList_empty,
    List.map_nil, List.nil_append]
  rfl

-- The displayed count is exactly the number of listed bins, including those
-- with two zero endpoints; it is not an additional geometric parameter.
example (n : ℕ) :
    (#((range n).image (fun i => i + 64)) : ℝ) + 1 = (n : ℝ) + 1 := by
  rw [card_image_of_injective _ (fun a b h => Nat.add_right_cancel h), card_range]

-- This is a finite numerical-envelope obstruction with the unchanged literal
-- allocator coefficient and genuine nominal positive-endpoint precision factors.
-- It does not assert actual error is large or scalar own-request IH insufficient.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let B := zeroData HP
    let r := request HP
    let q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        r.terminal, r.terminal⟩
    ∃ n : ℕ,
      32 * ((5 : ℝ) ^ 2 / (5 * r.source.rate) *
        ({B with bins := (range n).image (fun i => i + 64)}).magnitude r ^ 4) <
      128 * ((n : ℝ) + 1) ^ 3 *
        (((2 : ℝ) ^ (-B.requestPrecision 63 q)) ^ 4 +
          ((2 : ℝ) ^ (-B.requestPrecision 62 q)) ^ 4) := by
  dsimp only
  exact (zeroData HP).exists_count_envelope_gt_allocator
    (request HP) rfl 64 _ (by positivity)

-- The charge may be fixed first, then a budget with positive parent precision,
-- then the exhausted bin family. This numerical failure is not peculiar to A=0.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℝ) (M : ℕ)
    (hp : 0 < ({ zeroData HP with rankCharge := A }).requestPrecision M (request HP)) :
    let B := {zeroData HP with rankCharge := A}
    let r := request HP
    let q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        r.terminal, r.terminal⟩
    0 < B.requestPrecision M r ∧ ∃ n : ℕ,
      32 * ((5 : ℝ) ^ 2 / (5 * r.source.rate) *
        ({B with bins := (range n).image (fun i => i + M)}).magnitude r ^ 4) <
      128 * ((n : ℝ) + 1) ^ 3 *
        (((2 : ℝ) ^ (-B.requestPrecision (M - 1) q)) ^ 4 +
          ((2 : ℝ) ^ (-B.requestPrecision (M - 2) q)) ^ 4) := by
  dsimp only
  exact ⟨hp, exists_count_envelope_gt_allocator
    {zeroData HP with rankCharge := A} (request HP) rfl M _ (by positivity)⟩

-- Apply the new payment to actual unequal endpoints with the genuine canonical
-- reference. F may be the nonconstant/nonzero H4 indicator in RawNoiseSplit.
-- e is an explicit endpoint obligation, not a claim that supplied histories satisfy IH.
private theorem executed_payment (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (F : Environment 5 3 → ℝ) (e : ℕ → Option ℕ → ℝ)
    (he0 : ∀ m bin, 0 ≤ e m bin)
    (he : ∀ bin ∈ (RawNoiseSplitRegression.data HP).rays .residual,
      ∀ m, 0 < m →
      rowNormPow 4 5 1 (fun _ _ => True) (fun _ _ => True)
        (fun σ x y => ((RawNoiseSplitRegression.data HP).sample
          (RawNoiseSplitRegression.history F) m .residual (request HP) bin).getD 0 σ x y -
          (RawNoiseSplitRegression.data HP).residualCanonicalRay (request HP) bin σ x y) ≤
        e m bin ^ 4) :
    rowNormPow 4 5 1 (fun _ _ => True) (fun _ _ => True)
      (fun (σ : Environment 5 3) (x y : ZMod 5) => -F σ -
        rowSliceMean (fun _ _ => True) (fun _ _ => True)
        (fun σ _ _ => -F σ) x y) ≤ 16 * (e 63 none + e 62 none) ^ 4 := by
  have h := (RawNoiseSplitRegression.data HP).residualTransportedGroupInput_centered_minkowski_le
    (RawNoiseSplitRegression.history F) 64 1 (request HP)
    (fun _ _ => True) (fun _ _ => True) (by norm_num [request,
      RawNoiseSplitRegression.request, PolynomialBudgetHistory.request, gridChannel, rate])
    (fun _ _ => 1) e he0 (by
      simpa only [request, RawNoiseSplitRegression.request, PolynomialBudgetHistory.request,
        gridChannel, rate, pow_zero, inv_one, one_pow, Nat.cast_ofNat] using he)
  have hin := (RawNoiseSplitRegression.data HP).decodedGroupInput_eq_transported_of_two_mul_lt
    (RawNoiseSplitRegression.history F) 64 1 (request HP) (by decide)
  have hin' : (RawNoiseSplitRegression.data HP).residualTransportedGroupInput
      (RawNoiseSplitRegression.history F) 64 1 (request HP) = (fun σ _ _ => -F σ) :=
    hin.symm.trans (by simpa only [request] using RawNoiseSplitRegression.actual_input HP F)
  rw [hin'] at h
  simpa only [show (request HP).source.rate = 1 by
    norm_num [request, RawNoiseSplitRegression.request, PolynomialBudgetHistory.request,
      gridChannel, rate],
    show (RawNoiseSplitRegression.data HP).bins = ∅ from rfl,
    image_empty, insert_empty_eq, sum_singleton, div_one, inv_one,
    show (fun _ : ZMod 5 × ZMod 5 => (1 : ℝ)) = (1 : ZMod 5 × ZMod 5 → ℝ) from rfl,
    norm_one, one_pow, mul_one,
    show (RawNoiseSplitRegression.data HP).sampleScale (request HP) none = 0 from
      RawNoiseSplitRegression.scale HP,
    show (RawNoiseSplitRegression.data HP).slack = 1 from rfl,
    show LogSpaceEstimation.lastBudget 64 1 1 0 = 63 from rfl,
    show LogSpaceEstimation.lastBudget 64 (2 * 1) 1 0 = 62 from rfl,
    show ¬(63 : ℕ) = 0 from by decide, show ¬(62 : ℕ) = 0 from by decide,
    ↓reduceIte, Nat.cast_ofNat] using h

-- A nonconstant genuine-reference transported input has nonzero centered error.
-- The new consumer is checked for that SAME input, with its endpoint obligations
-- exposed. It is not a canonical recursively accurate history witness.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ F : Environment 5 3 → ℝ,
      (fun (σ : Environment 5 3) (x y : ZMod 5) => -F σ -
        rowSliceMean (fun _ _ => True) (fun _ _ => True) (fun σ _ _ => -F σ) x y) ≠ 0 ∧
      ∀ e : ℕ → Option ℕ → ℝ, (∀ m bin, 0 ≤ e m bin) →
        (∀ bin ∈ (RawNoiseSplitRegression.data HP).rays .residual, ∀ m, 0 < m →
          rowNormPow 4 5 1 (fun _ _ => True) (fun _ _ => True)
            (fun σ x y => ((RawNoiseSplitRegression.data HP).sample
              (RawNoiseSplitRegression.history F) m .residual (request HP) bin).getD 0 σ x y -
              (RawNoiseSplitRegression.data HP).residualCanonicalRay (request HP) bin σ x y) ≤
                e m bin ^ 4) →
        rowNormPow 4 5 1 (fun _ _ => True) (fun _ _ => True)
          (fun (σ : Environment 5 3) (x y : ZMod 5) => -F σ -
            rowSliceMean (fun _ _ => True) (fun _ _ => True) (fun σ _ _ => -F σ) x y) ≤
              16 * (e 63 none + e 62 none) ^ 4 := by
  have hframe : Nonempty (Frame 5 4 1) := Frame.nonempty (by decide)
  let frame : Frame 5 4 1 := Classical.choice hframe
  let σ₀ : Environment 5 3 := fun _ => (fun _ => 0, frame)
  let σ₁ : Environment 5 3 := fun _ => (fun _ => 1, frame)
  let F : Environment 5 3 → ℝ := fun σ => if (σ 1).1 0 = 0 then 1 else 0
  refine ⟨F, ?_, executed_payment HP F⟩
  intro hz
  have h₀ := congrFun (congrFun (congrFun hz σ₀) 0) 0
  have h₁ := congrFun (congrFun (congrFun hz σ₁) 0) 0
  norm_num only [F, σ₀, σ₁, one_ne_zero, ↓reduceIte, neg_zero, Pi.zero_apply] at h₀ h₁
  linarith

end NoiseAllocationRegression
