/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual dyadic RAW conditional means)
import Complexity.Foundations.Probability.HierarchyDyadicRawPayment
import all ComplexityTests.HierarchyJointSignedMean
import all ComplexityTests.HierarchyRawExecution

/-!
The non-unit three-bin residual has positive E and EC and strict signed subtraction.
Its paid client now consumes actual RAW, with conditional recursive calls and scalar
IH, plus explicit positive endpoint budgets. The supplied-history execution below
really computes 6+6-1, including its common walks. Endpoint positivity is not inferred
from parent activity, and exhausted endpoints retain literal zero.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace DyadicRawRegression
open JointSignedRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ)

example (M : ℕ) (hpositive : 0 < (B HP A).requestPrecision M (r HP))
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) →
      Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℝ)
    (hrows : ∀ i ∈ (B HP A).bins,
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history ((B HP A).binBudget M i (r HP)) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      BudgetData.row history ((B HP A).childBudget M) q = some (child 0 q))
    (hdirect : ∀ i ∈ (B HP A).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).direct
      (B HP A).compressedBin ((B HP A).binBudget M i (r HP)) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ (B HP A).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).left
      (B HP A).evaluate ((B HP A).binBudget M i (r HP)) q = some (.row (child i q)))
    (hright : ∀ i ∈ (B HP A).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).right
      (B HP A).compressedBin ((B HP A).binBudget M i (r HP)) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      (B HP A).evaluate ((B HP A).childBudget M) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ (B HP A).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).direct
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((B HP A).binBudget M i (r HP)) q ^ 4)
    (hIL : ∀ i ∈ (B HP A).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).left
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((B HP A).binBudget M i (r HP)) q ^ 4)
    (hIR : ∀ i ∈ (B HP A).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate i)).right
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child i q) ((B HP A).residualCanonicalChild i q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q))
          ((B HP A).binBudget M i (r HP)) q ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP A).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP A).padding) σ y)
        (child 0 q) ((B HP A).residualCanonicalChild 0 q) ≤
        (fun m q => (2 : ℝ) ^ (-(B HP A).requestPrecision m q)) ((B HP A).childBudget M) q ^ 4)
    (hfixedD : BudgetData.residualDirectRootCost HP (B HP A).binCap *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * A) ≤ 1 / 4)
    (hfixedP : BudgetData.residualProductNegativeRootCost HP (B HP A).binCap *
      (2 : ℝ) ^ (1 / 16 - 32 * (A : ℝ)) ≤ 3 / 4)
    (hlive : ∀ i ∈ (B HP A).bins, 0 < (B HP A).binBudget M i (r HP))
    (hnlive : 0 < (B HP A).childBudget M)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ (B HP A).rays .residual,
      let d := Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d (B HP A).slack
        ((B HP A).sampleScale (r HP) bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) (B HP A).slack
        ((B HP A).sampleScale (r HP) bin)
      f ≠ c → (0 < f → ∃ T, (B HP A).sample history f .residual (r HP) bin = some T) ∧
        (0 < c → ∃ T, (B HP A).sample history c .residual (r HP) bin = some T)) :
    0 < (B HP A).requestPrecision M (r HP) ∧
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (B HP A).base
    ∃ executed, (B HP A).raw history M .residual (r HP) = some executed ∧
      rowNormPow 4 5 (r HP).source.rate
        (fun σ x => (r HP).source.retains (channels (B HP A).padding) σ x)
        (fun σ y => (r HP).terminal.retains (channels (B HP A).padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => (r HP).source.retains (channels (B HP A).padding) σ x)
          (fun σ y => (r HP).terminal.retains (channels (B HP A).padding) σ y)
          executed x y - G x y| /
            (rate 1 + G x y))) ≤
        ((2 : ℝ) ^ (-(B HP A).requestPrecision M (r HP))) ^ 4 := by
  refine ⟨hpositive, ?_⟩
  have hbins : (B HP A).bins = range (2 + 1) := by
    ext j
    simp [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data]
  have hθ : HP.θ ≤ (1 / 2 : ℝ) := by
    have h := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at h
    linarith
  have hkh (i : ℕ) (_hi : i ∈ (B HP A).bins) (v : ℝ)
      (hv : (B HP A).cutoff i v ≠ 0) : (B HP A).auxiliary i v = 1 :=
    HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      i (fun _ => 1) hv
  have hl (i : ℕ) (_hi : i ∈ (B HP A).bins) (d : ℝ) (hd : d ≤ HP.θ) :
      (B HP A).cutoff i d = 0 :=
    boundedRoutedBinCutoff_eq_zero (by norm_num)
      (fun v hv => polynomialSwitch4_of_le (by norm_num) hv) rate_pos rate_antitone
      (hd.trans hθ) i (fun _ => 1)
  have hk : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  exact (B HP A).raw_residual_clipped_joint_le 2 hbins rfl rfl rfl
    (by norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data])
    SourceRegression.horizon (by decide) M 2 1 (r HP) (by change (0 : Fin 3) ≠ 2; decide) rfl rfl
    (by decide) (by decide) (TerminalMeanRegression.small_nonneg HP)
    (TerminalMeanRegression.small_mass HP) (TerminalMeanRegression.small_stage HP)
    (by
      intro z y
      by_cases h : z = y
      · right
        norm_num [B, TerminalMeanRegression.smallData, h, rate]
      · left
        norm_num [B, TerminalMeanRegression.smallData, h, rate])
    hkh hl hk history child depth ζ floor
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN
    rfl (Nat.cast_nonneg A) hfixedD hfixedP
    0 2 (by decide) [1] [2, 3] rfl rfl rfl hlive hnlive hcalls

end DyadicRawRegression

namespace DyadicRawExecutionRegression
open RawExecutionRegression

-- Actual supplied history, not an assumed conditional mean or a desired output.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ R, (data HP).raw history 2 .residual (request HP) = some R ∧
      ∀ x y, rowSliceMean
        (X (0 : Fin 3) (side 5 0) (CopyPadding.identifier (data HP).padding [1]))
        (Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier (data HP).padding [2, 3])) R x y =
        rowSliceMean
          (X (0 : Fin 3) (side 5 0) (CopyPadding.identifier (data HP).padding [1]))
          (Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier (data HP).padding [2, 3]))
          (fun _ _ _ => 11) x y := by
  have hpos (i : ℕ) (_ : i ∈ (data HP).bins) :
      0 < (data HP).binBudget 2 i (request HP) := by
    change 0 < LogSpaceEstimation.lastBudget 2 1 1
      ⌊Real.logb 2 ((rate 0) / (rate 0))⌋
    norm_num [rate, LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  have hneg : 0 < (data HP).childBudget 2 := by change 0 < (1 : ℕ); decide
  have hp (i : ℕ) (_ : i ∈ (data HP).bins) :
      ∃ T, (data HP).positiveSample history ((data HP).binBudget 2 i (request HP))
        i .residual (request HP) = some T := ⟨_, positive HP _ i⟩
  have hn : ∃ T, BudgetData.row history ((data HP).childBudget 2)
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (request HP).source,
        { (request HP).terminal with rate := (BudgetData.midpoint (request HP)).rate },
        { (request HP).terminal with rate :=
          (min ((request HP).terminal.rate) ((BudgetData.midpoint (request HP)).rate)) }⟩ =
        some T := ⟨_, rfl⟩
  have hfinite : (data HP).finiteInput history 2 .residual (request HP) =
      some (fun _ _ _ => 11) := by
    rw [(data HP).finiteInput_residual_decoded history 2 (request HP) hpos hneg hp hn]
    congr 1
    funext σ x y
    simp only [scale, sample, BudgetData.rays, List.map_append, List.map_map,
      Function.comp_def]
    norm_num [data, PolynomialBudgetHistory.data, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff]
  apply (data HP).raw_residual_mean_finiteInput history 2 (request HP)
    0 2 (by decide) 0 0 [1] [2, 3] rfl rfl _ hpos hneg hp hn _ hfinite
  intro i _ bin _
  dsimp only
  intro _
  exact ⟨fun _ => ⟨_, sample HP _ bin⟩, fun _ => ⟨_, sample HP _ bin⟩⟩

-- No child availability at all is needed in equal exhausted groups.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).pairedSample (fun _ _ => none) 0 8 .residual (request HP) none = some 0 := by
  simp [BudgetData.pairedSample, LogSpaceEstimation.lastBudget]

-- Positive and negative rays retain their different endpoint budgets.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ) :
    let D := JointSignedRegression.B HP A
    let r := JointSignedRegression.r HP
    LogSpaceEstimation.lastBudget 64 1 D.slack (D.sampleScale r (some 0)) = 59 ∧
    LogSpaceEstimation.lastBudget 64 1 D.slack (D.sampleScale r (some 1)) = 63 ∧
    LogSpaceEstimation.lastBudget 64 2 D.slack (D.sampleScale r (some 1)) = 62 ∧
    LogSpaceEstimation.lastBudget 64 1 D.slack (D.sampleScale r none) = 63 := by
  dsimp only
  rw [(JointSignedRegression.B HP A).sampleScale_grid (JointSignedRegression.r HP) 1 0 rfl rfl,
    (JointSignedRegression.B HP A).sampleScale_grid (JointSignedRegression.r HP) 1 1 rfl rfl,
    (JointSignedRegression.B HP A).raw_negative_budget]
  norm_num [JointSignedRegression.B, TerminalMeanRegression.smallData,
    TerminalMeanRegression.data, ProductMeanRegression.data, PolynomialBudgetHistory.data,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, BudgetData.childBudget]

-- Exhausted RAW has a nonzero deficit against the supplied canonical rays/target.
-- The signed identity retains that deficit; it does not infer zero canonical error.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ R, (data HP).raw (fun _ _ => none) 0 .residual (request HP) = some R ∧
      ∀ x y, rowSliceMean
        (X (0 : Fin 3) (side 5 0) (CopyPadding.identifier (data HP).padding [1]))
        (Y (2 : Fin 3) (side 5 0) (CopyPadding.identifier (data HP).padding [2, 3]))
        R x y - 11 = -11 := by
  have hc : ∀ i < Nat.log2 0 + 1, ∀ bin ∈ (data HP).rays .residual,
      let d := dyadicSlack (Nat.log2 0 + 1) i
      let f := LogSpaceEstimation.lastBudget 0 d (data HP).slack
        ((data HP).sampleScale (request HP) bin)
      let c := LogSpaceEstimation.lastBudget 0 (2 * d) (data HP).slack
        ((data HP).sampleScale (request HP) bin)
      f ≠ c → (0 < f → ∃ T, (data HP).sample (fun _ _ => none) f .residual
        (request HP) bin = some T) ∧
        (0 < c → ∃ T, (data HP).sample (fun _ _ => none) c .residual
          (request HP) bin = some T) := by
    intro i _ bin _
    simp [LogSpaceEstimation.lastBudget]
  obtain ⟨F, _, hr, hm⟩ := (data HP).raw_prefix_signed_deficit (fun _ _ => none)
    0 .residual (request HP) 0 2 (by decide) 0 0 [1] [2, 3] rfl rfl hc
    0 (by decide) (fun _ _ _ _ => 1) (fun _ _ => 11)
  refine ⟨_, hr, ?_⟩
  intro x y
  have hh := hm x y
  norm_num only [Nat.log2_zero, zero_add, LogSpaceEstimation.lastBudget,
    Nat.zero_sub, ↓reduceIte] at hh ⊢
  convert hh using 1
  simp only [rowSliceMean, BudgetData.rays, data, PolynomialBudgetHistory.data,
    List.map_append, List.map_map, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.sum_append, Function.comp_def, Finset.sum_map_toList]
  norm_num only [sum_insert, sum_singleton, mem_singleton, zero_ne_one, not_false_eq_true,
    neg_add_rev, neg_zero, add_zero]
  rw [expect_neg_distrib]
  ring

-- Literal zero samples differ from successful budget-zero supplied-history leaves.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).sample history 0 .residual (request HP) (some 0) = some 0 ∧
    (data HP).positiveSample history 0 0 .residual (request HP) = some (fun _ _ _ => 6) :=
  ⟨(data HP).sample_zero history .residual (request HP) (some 0), positive HP 0 0⟩

-- The charge is fixed before the field and every bin through the full horizon.
-- All endpoint budgets and parent precision are eventually positive together.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (A₀ : ℕ) :
    ∃ A : ℕ, A₀ ≤ A ∧ ∀ n ks ka : ℕ,
      ∃ (P : ℕ) (hP : P.Prime), let : Fact P.Prime := ⟨hP⟩
      ∃ (H : Horizon P) (D : BudgetData HP P)
        (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
        D.rankCharge = A ∧ D.binCap = 16 ∧ D.bins = range (H.maxExponent + 1) ∧
        max n (max ks ka) ≤ H.maxExponent ∧
        BudgetData.residualDirectRootCost HP D.binCap *
          (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * A) ≤ 1 / 4 ∧
        BudgetData.residualProductNegativeRootCost HP D.binCap *
          (2 : ℝ) ^ (1 / 16 - 32 * (A : ℝ)) ≤ 3 / 4 ∧
        ∃ M₀ : ℕ, ∀ M ≥ M₀,
          0 < D.requestPrecision M r ∧
          (∀ i ∈ D.bins, 0 < D.binBudget M i r) ∧ 0 < D.childBudget M := by
  obtain ⟨A, hA, hd, hp⟩ :=
    BudgetData.exists_residualJoint_charge (HP := HP) 16 (by norm_num) A₀
  refine ⟨A, hA, ?_⟩
  intro n ks ka
  obtain ⟨P, hP, _, _, H, hH, _⟩ :=
    exists_bounded_depth_prime (max n (max ks ka) + 1) 0 (by positivity)
  let : Fact P.Prime := ⟨hP⟩
  let D := ProductAllocationRegression.data HP P A H.maxExponent
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.residual 0, gridChannel 0 ks [1], gridChannel 2 ka [2, 3], gridChannel 2 ka [2, 3]⟩
  obtain ⟨M₁, hM₁⟩ := D.grid_precision_eventually_pos ks ka r rfl rfl
  obtain ⟨M₂, hM₂⟩ := D.raw_endpoint_budgets_eventually_pos r
  refine ⟨P, hP, H, D, r, rfl, rfl, rfl, ?_, hd, hp, max M₁ M₂, ?_⟩
  · rw [hH]
    omega
  · intro M hM
    exact ⟨hM₁ M ((le_max_left _ _).trans hM), hM₂ M ((le_max_right _ _).trans hM)⟩

end DyadicRawExecutionRegression
