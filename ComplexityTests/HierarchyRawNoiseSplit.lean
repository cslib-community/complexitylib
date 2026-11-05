/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of semantic and transported RAW inputs)
import Complexity.Foundations.Probability.HierarchyRawNoiseSplit
import all ComplexityTests.PolynomialBudgetHistory

/-!
The actual once-negative residual ray at two unequal POSITIVE endpoints need not
cancel. This is a counterexample to cancellation from availability, not to the
own-request-IH salary or to the estimator. The supplied history is not asserted to
be a recursively accurate evaluator. The full-rate fixture adapts Samuel
Schlesinger's execution tests. Production completion and its steps are unchanged.
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
namespace RawNoiseSplitRegression

private def data (HP : FourthRootHierarchyParams 16 1 16 32 8) : BudgetData HP 5 :=
  { PolynomialBudgetHistory.data HP with bins := ∅ }
private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  { PolynomialBudgetHistory.request HP with task := .residual 0 }
private def history {k : ℕ} (F : Environment 5 3 → ℝ) (m : ℕ)
    (_ : HierarchyTask.Request k (Fin 3) (ZMod 5)) : Option (BudgetValue 5) :=
  some (.row (fun σ _ _ => if m = 63 then F σ else 0))

private lemma sample (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (F : Environment 5 3 → ℝ) (m : ℕ) :
    (data HP).sample (history F) m .residual (request HP) none =
      some (fun σ _ _ => if m = 63 then -F σ else 0) := by
  by_cases hm : m = 0
  · subst m
    simp only [BudgetData.sample, ↓reduceIte]
    rfl
  · simp only [BudgetData.sample, hm, ↓reduceIte, BudgetData.row, history,
      Option.bind_some, BudgetValue.row?]
    apply congrArg some
    funext σ x y
    have hf (τ : Environment 5 3) (role : Fin 3) (suffix : List (ZMod 5)) (v : ZMod 5) :
        (gridChannel role 0 suffix).retains (channels (1 : ZMod 5)) τ v :=
      PolynomialBudgetHistory.full τ role suffix v
    have hu : HierarchyTask.usageRatio (channels (1 : ZMod 5)) (request HP).terminal
        (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (request HP).source,
          (request HP).terminal, (request HP).terminal⟩ :
            HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) y = 1 := by
      simp [HierarchyTask.usageRatio, request, PolynomialBudgetHistory.request, hf]
    simp only [data, request, PolynomialBudgetHistory.request, PolynomialBudgetHistory.data,
      BudgetData.midpoint, gridChannel, rate, pow_zero, inv_one, one_pow, min_self] at *
    rw [hu]
    split_ifs <;> ring

private lemma scale (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).sampleScale (request HP) none = 0 := by
  exact (data HP).sampleScale_none_eq_zero _

private lemma actual_input (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (F : Environment 5 3 → ℝ) :
    (data HP).decodedGroupInput (history F) 64 1 .residual (request HP) =
      (fun σ _ _ => -F σ) := by
  funext σ x y
  simp only [decodedGroupInput, BudgetData.rays,
    show (data HP).bins = ∅ from rfl, toList_empty, List.map_nil,
    List.nil_append, List.map_cons, List.sum_cons, List.sum_nil, add_zero, scale]
  change ((data HP).sample (history F) 63 .residual (request HP) none).getD 0 σ x y -
    ((data HP).sample (history F) 62 .residual (request HP) none).getD 0 σ x y = _
  simp [sample]

-- Both endpoints are positive, precision is positive, and the semantic part is
-- exactly zero. The actual transported perturbation is nevertheless the full -F.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (F : Environment 5 3 → ℝ) :
    LogSpaceEstimation.lastBudget 64 1 (data HP).slack
        ((data HP).sampleScale (request HP) none) = 63 ∧
      LogSpaceEstimation.lastBudget 64 2 (data HP).slack
        ((data HP).sampleScale (request HP) none) = 62 ∧
      0 < (data HP).requestPrecision 64 (request HP) ∧
      (data HP).residualSemanticGroupInput 64 1 (request HP) = 0 ∧
      (data HP).residualTransportedGroupInput (history F) 64 1 (request HP) =
        (fun σ _ _ => -F σ) := by
  refine ⟨?_, ?_, ?_, (data HP).residualSemanticGroupInput_eq_zero_of_two_mul_lt
    64 1 (request HP) (by decide), ?_⟩
  · rw [scale]; rfl
  · rw [scale]; rfl
  · norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision, data,
      PolynomialBudgetHistory.data, request, PolynomialBudgetHistory.request,
      gridChannel, rate]
  · rw [← (data HP).decodedGroupInput_eq_transported_of_two_mul_lt (history F)
      64 1 (request HP) (by decide)]
    exact actual_input HP F

-- The new decomposition is used on the actual sample, not merely its signature.
-- With F=1 this disproves the tempting positive-endpoint cancellation inference.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).decodedGroupInput (history (fun _ => 1)) 64 1 .residual (request HP) ≠ 0 := by
  have hframe : Nonempty (Frame 5 4 1) := Frame.nonempty (by decide)
  intro hz
  rw [actual_input] at hz
  have hv := congrFun (congrFun (congrFun hz
    (fun _ => (0, Classical.choice hframe))) 0) 0
  norm_num at hv

-- A concrete nonconstant full H4 environment input has nonzero centered noise
-- before completion. This asserts neither a nonzero post-walk moment nor IH.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ F : Environment 5 3 → ℝ,
      (fun σ x y =>
        (data HP).decodedGroupInput (history F) 64 1 .residual (request HP) σ x y -
          rowSliceMean (NormalizedMoments.retainedMask 0 (side 5 0) (data HP).padding [1])
            (NormalizedMoments.retainedMask 2 (side 5 0) (data HP).padding [2, 3])
            ((data HP).decodedGroupInput (history F) 64 1 .residual (request HP)) x y) ≠ 0 := by
  have hframe : Nonempty (Frame 5 4 1) := Frame.nonempty (by decide)
  let frame : Frame 5 4 1 := Classical.choice hframe
  let σ₀ : Environment 5 3 := fun _ => (fun _ => 0, frame)
  let σ₁ : Environment 5 3 := fun _ => (fun _ => 1, frame)
  let F : Environment 5 3 → ℝ := fun σ => if (σ 1).1 0 = 0 then 1 else 0
  refine ⟨F, ?_⟩
  intro hz
  have h₀ := congrFun (congrFun (congrFun hz σ₀) 0) 0
  have h₁ := congrFun (congrFun (congrFun hz σ₁) 0) 0
  rw [actual_input] at h₀ h₁
  norm_num only [F, σ₀, σ₁, one_ne_zero, ↓reduceIte, neg_zero,
    Pi.zero_apply] at h₀ h₁
  linarith

-- The ACTUAL full-terminal decoder statistic consumes the split budget. This
-- checks the production H4 consumer; it does not assert nonzero completed noise.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (F : Environment 5 3 → ℝ)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    let D := data HP
    let r := request HP
    rowNormPow 4 5 r.source.rate
      (NormalizedMoments.retainedMask 0 (side 5 0) D.padding [1])
      (NormalizedMoments.retainedMask 2 (side 5 0) D.padding [2, 3])
      (actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0) D.padding [1] [2, 3] 0 G
        (firstSignalIncrement (D.rawFirstPrefixes (history F) 64 .residual r) 0
          (fun _ _ _ _ => 0)) 0 0 6) ≤
      8 * (D.rawRelativeNoiseBudget 64 r 0 2 (by decide) 0 0 [1] [2, 3]
        (fun i => D.residualSemanticGroupInput 64 (dyadicSlack 7 i) r) G 7 +
      D.rawRelativeNoiseBudget 64 r 0 2 (by decide) 0 0 [1] [2, 3]
        (fun i => D.residualTransportedGroupInput (history F) 64 (dyadicSlack 7 i) r) G 7) := by
  dsimp only
  apply ((data HP).rawFirstPrefixes_decoded_noise (history F) 64 (request HP)
    0 2 (by decide) 0 0 [1] [2, 3] rfl rfl rfl ?_ G hG (fun _ _ _ _ => 0)
    6 (by decide)).trans
  · exact (data HP).rawRelativeNoiseBudget_residual_split_le (history F) 64
      (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl G 7
  · intro j _ bin hb
    have hbin : bin = none := by
      simpa only [BudgetData.rays, show (data HP).bins = ∅ from rfl, toList_empty,
        List.map_nil, List.nil_append, List.mem_singleton] using hb
    subst bin
    dsimp only
    intro _
    constructor <;> intro _ <;> exact ⟨_, sample HP F _⟩

-- Exhaustion is literal, even for the deliberately budget-dependent history.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (F : Environment 5 3 → ℝ) :
    (data HP).decodedGroupInput (history F) 64 64 .residual (request HP) = 0 :=
  (data HP).decodedGroupInput_eq_zero_of_le _ _ _ _ (by decide)

end RawNoiseSplitRegression
