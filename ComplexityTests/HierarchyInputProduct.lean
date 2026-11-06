/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of executed later actual relative product transport)
import Complexity.Foundations.Probability.HierarchyInputProduct
import Complexity.Foundations.Probability.HierarchyCorrectionStability
import all ComplexityTests.HierarchyLaterInputMean
import all ComplexityTests.HierarchyCanonicalRange
import all ComplexityTests.HierarchyProductMean
import all ComplexityTests.PolynomialBudgetHistory

/-!
# Later actual INPUT execution with supplied histories

Requested input one has genuine positive E₁ and E₁*C. The left normalized child
uses actual RAW/own-source PREP and the final pilot maximum. Unequal channels,
inherited suffixes and the reset-right call are retained. The direct error is the
nonconstant indicator of column zero. These are supplied histories, not recursive IH.
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
namespace InputProductRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private def data := PolynomialBudgetHistory.data HP
private def iteration := LaterInputMeanRegression.iteration HP
private def request := LaterInputMeanRegression.request HP
private def calls := HierarchyTask.rawRequests 0 0 (.input (iteration HP))
  (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
  ((data HP).binRate 0)
private lemma admissible : Admissible (calls HP).left := by
  exact ⟨by change (0 : Fin 3) ≠ 1; decide, rfl, rfl⟩
private def reference := (data HP).residualCanonicalChild 0
private def child (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :=
  if q = (calls HP).direct then fun σ x y => reference HP q σ x y + if y = 0 then 1 else 0
  else reference HP q
private lemma different :
    (calls HP).direct ≠ (calls HP).left ∧ (calls HP).right ≠ (calls HP).left ∧
      (calls HP).right ≠ (calls HP).direct := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have ht := congrArg HierarchyTask.Request.task h
    change HierarchyTask.baseNormalized 0 0 = .row 0 (.normalized ⟨0, HP.k_pos⟩) at ht
    contradiction
  · intro h
    have ht := congrArg HierarchyTask.Request.task h
    change HierarchyTask.baseNormalized 0 0 = .row 0 (.normalized ⟨0, HP.k_pos⟩) at ht
    contradiction
  · intro h
    have ht := congrArg (fun q => q.source.role) h
    change (1 : Fin 3) = 0 at ht
    contradiction
private lemma left : reference HP (calls HP).left =
    sourceChild HP 1 id (calls HP).left (admissible HP) (data HP).base 0 := by
  funext σ
  exact (data HP).actualInput_left_reference 0 (iteration HP) 0 rfl
    (request HP) (admissible HP) σ
private lemma dense (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
    (hq : q.task = HierarchyTask.baseNormalized 0 0) : reference HP q =
      denseChild 1 id q ((data HP).cutoff 0) ((data HP).auxiliary 0)
        HP.ρ HP.K (data HP).base := by
  funext σ
  unfold reference BudgetData.residualCanonicalChild canonicalRequestChild
  rw [hq]
  rfl
private lemma dense_range (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
    (hq : q.task = HierarchyTask.baseNormalized 0 0) (σ : Environment 5 3) (x y : ZMod 5) :
    reference HP q σ x y ∈ Set.Icc 0 32 := by
  rw [dense HP q hq]
  unfold denseChild
  convert normalizedRequest_mem_Icc HP 1 q _ (by norm_num : (0 : ℝ) ≤ 16)
    ((data HP).cutoff_bounds 0) _ _ σ x y using 1; norm_num
private lemma left_range (σ : Environment 5 3) (x y : ZMod 5) :
    reference HP (calls HP).left σ x y ∈ Set.Icc 0 (data HP).atomCap := by
  rw [left HP]
  exact correctionRequest_mem_Icc HP 1 id _ _ _ _ _ σ x y
private lemma full (σ : Environment 5 3) (y : ZMod 5) :
    (calls HP).direct.usage.retains (channels (1 : ZMod 5)) σ y ∧
    (calls HP).right.usage.retains (channels (1 : ZMod 5)) σ y ∧
    (BudgetData.midpoint (request HP)).retains (channels (1 : ZMod 5)) σ y := by
  have hc : (calls HP).direct.usage = gridChannel 2 0 [2, 3] ∧
      (calls HP).right.usage = gridChannel 2 0 [2, 3] := by
    norm_num [calls, HierarchyTask.rawRequests, data, PolynomialBudgetHistory.data,
      request, LaterInputMeanRegression.request, ProductMeanRegression.request,
      PolynomialBudgetHistory.request, BudgetData.midpoint, gridChannel, rate]
  rw [hc.1, hc.2]
  exact ⟨PolynomialBudgetHistory.full σ 2 [2, 3] y,
    PolynomialBudgetHistory.full σ 2 [2, 3] y, PolynomialBudgetHistory.full σ 1 [] y⟩

-- Genuine RAW/PREP and FINAL pilot maximum are supplied at the child's literal budget.
private def actualHistory (_m : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :
    Option (BudgetValue 5) :=
  if q.task = .row 0 (.input ⟨0, HP.k_pos⟩) then
    some (.row (fun _ => stageRaw HP 1 id (calls HP).left (admissible HP) (data HP).base 0))
  else if q.task = .row 0 (.preparation ⟨0, HP.k_pos⟩) then
    some (.row (sourcePreparation HP 1 id (calls HP).left (admissible HP) (data HP).base 0))
  else some (.vector (fun _ => stageMaximum HP 1 id
    (calls HP).left (admissible HP) (data HP).base))
private lemma normalized (m : ℕ) :
    (data HP).normalized (actualHistory HP) m (calls HP).left false ⟨0, HP.k_pos⟩ =
      some (reference HP (calls HP).left) := by
  rw [left HP]
  unfold H4RankEnvironment.sourceChild
  simp [BudgetData.normalized, BudgetData.row, vector, actualHistory,
    data, PolynomialBudgetHistory.data, BudgetValue.row?, BudgetValue.vector?]

private def history (m : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :=
  if q = (calls HP).left then
    ((data HP).normalized (actualHistory HP) m q false ⟨0, HP.k_pos⟩).map BudgetValue.row
  else some (.row (child HP q))
private lemma rows (m : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :
    BudgetData.row (history HP) m q = some (child HP q) := by
  by_cases h : q = (calls HP).left
  · subst q
    simp only [history, ↓reduceIte, normalized HP, Option.map_some, BudgetData.row,
      Option.bind_some, BudgetValue.row?, child, Ne.symm (different HP).1, ↓reduceIte]
  · simp only [BudgetData.row, history, h, ↓reduceIte, Option.bind_some, BudgetValue.row?]

private def G := (data HP).canonicalPreparationInput false (iteration HP) (request HP)
private lemma G_nonneg (x y : ZMod 5) : 0 ≤ G HP x y :=
  ((data HP).canonicalPreparationInput_range false (iteration HP) (request HP)
    (by exact rate_pos 0) (ProductMeanRegression.nonneg HP)
    (ProductMeanRegression.mass HP) (by intro x y; exact ProductMeanRegression.stage_bound HP x y)
    x y).1
private def KD : ℝ := 4 * (33 : ℝ) ^ ((3 : ℝ) / 4)
private def KP : ℝ := 4 * ((5 : ℝ) * (data HP).atomCap * 32) ^ ((3 : ℝ) / 4)
private def X := fun σ x => (request HP).source.retains (channels (1 : ZMod 5)) σ x
private def Z := fun σ z => (BudgetData.midpoint (request HP)).retains
  (channels (1 : ZMod 5)) σ z
private def U := fun σ y => (calls HP).right.usage.retains (channels (1 : ZMod 5)) σ y
private def payment : ℝ :=
  8 * (KD ^ 4 * rootDistPow 4 5 (request HP).source.rate (X HP) (U HP)
      (child HP (calls HP).direct) (reference HP (calls HP).direct) +
    KP HP ^ 4 * (16384 * (32 * 5 * rootDistPow 4 5 (request HP).source.rate (X HP) (Z HP)
      (child HP (calls HP).left) (reference HP (calls HP).left) +
      (data HP).atomCap * 5 * (1 / (request HP).source.rate) *
        rootDistPow 4 5 1 (Z HP) (U HP)
          (child HP (calls HP).right) (reference HP (calls HP).right))))

private lemma weights (y : ZMod 5) :
    (data HP).binRate 0 * HierarchyTask.usageRatio (channels (1 : ZMod 5))
      (request HP).terminal (calls HP).direct y = 1 ∧
    (data HP).binRate 0 * HierarchyTask.usageRatio (channels (1 : ZMod 5))
      (request HP).terminal (calls HP).right y *
      ((BudgetData.midpoint (request HP)).rate /
        (dens {σ : Environment 5 3 |
          (BudgetData.midpoint (request HP)).retains (channels (1 : ZMod 5)) σ y} : ℝ)) = 1 := by
  have ht (σ : Environment 5 3) : (request HP).terminal.retains
      (channels (1 : ZMod 5)) σ y := PolynomialBudgetHistory.full σ 2 [2, 3] y
  simp only [HierarchyTask.usageRatio, (fun σ => (full HP σ y).1), (fun σ => (full HP σ y).2.1),
    (fun σ => (full HP σ y).2.2), ht, filter_true, dens_univ]
  norm_num [data, PolynomialBudgetHistory.data, BudgetData.midpoint, request,
    LaterInputMeanRegression.request, ProductMeanRegression.request,
    PolynomialBudgetHistory.request, gridChannel, rate]

-- This is an executed later POSITIVE sample relative bound, from the three actual
-- own-domain rooted errors. It assumes no parent accuracy and subtracts no E ray.
private lemma executed_bound (m : ℕ) : ∃ A,
    (data HP).positiveSample (history HP) m 0
      (.input (iteration HP)) (request HP) = some A ∧
    rowNormPow 4 5 (request HP).source.rate (X HP) (fun _ _ => True)
      (fun σ x y => (A σ x y - HierarchyTask.rawPositiveSample (channels (1 : ZMod 5))
        0 0 (.input (iteration HP)) (request HP).source (BudgetData.midpoint (request HP))
        (request HP).terminal ((data HP).binRate 0) (fun q => reference HP q σ) x y) /
          ((request HP).terminal.rate +
            (data HP).canonicalPreparationInput false (iteration HP) (request HP) x y)) ≤
      payment HP := by
  have hterm : (request HP).terminal.rate = 1 := by norm_num [request,
    LaterInputMeanRegression.request, ProductMeanRegression.request,
    PolynomialBudgetHistory.request, gridChannel, rate]
  have hmid : (BudgetData.midpoint (request HP)).rate = 1 := hterm
  have hpad : (data HP).padding = 1 := rfl
  have hcap : 0 ≤ (data HP).atomCap := mul_nonneg (by norm_num) (HP.Q_nonneg _)
  have hcoef (x y : ZMod 5) :
      |(1 : ℝ) / (1 + G HP x y)| ≤ 1 := by
    have hc := G_nonneg HP x y
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hw := weights HP
  have h := (data HP).positiveSample_input_genuine_relative_le (history HP) m 0
    (iteration HP) (request HP) (child HP) 0 rfl (fun _ _ => True)
    (fun x y => (request HP).terminal.rate + G HP x y) KD (KP HP)
    33 (data HP).atomCap 32 (mul_nonneg (by norm_num) (HP.Q_nonneg _)) (by norm_num)
    5 5 5 (rate_pos 1) (rate_pos 0)
    (by intros; exact rows HP _ _)
    (by
      dsimp only
      intro σ x y
      change child HP (calls HP).direct σ x y ∈ Set.Icc 0 33 ∧
        reference HP (calls HP).direct σ x y ∈ Set.Icc 0 33
      have hb := dense_range HP (calls HP).direct rfl σ x y
      simp only [child, ↓reduceIte]
      split_ifs <;> exact ⟨⟨by linarith [hb.1], by linarith [hb.2]⟩, ⟨hb.1, by linarith [hb.2]⟩⟩)
    (by
      dsimp only
      intro σ x z
      change child HP (calls HP).left σ x z ∈ Set.Icc 0 (data HP).atomCap ∧
        reference HP (calls HP).left σ x z ∈ Set.Icc 0 (data HP).atomCap
      have hb := left_range HP σ x z
      simp only [child, Ne.symm (different HP).1, ↓reduceIte]
      exact ⟨hb, hb⟩)
    (by
      dsimp only
      intro σ z y
      change child HP (calls HP).right σ z y ∈ Set.Icc 0 32 ∧
        reference HP (calls HP).right σ z y ∈ Set.Icc 0 32
      have hb := dense_range HP (calls HP).right rfl σ z y
      simp only [child, (different HP).2.2, ↓reduceIte]
      exact ⟨hb, hb⟩)
    (by dsimp only; intro σ x y hy; exact (hy (full HP σ y).1).elim)
    (by dsimp only; intro σ z y hy; exact (hy (full HP σ y).2.1).elim)
    (by dsimp only; intro σ x z hz; exact (hz (full HP σ z).2.2).elim)
    (by dsimp only; intro σ x; exact ⟨card_le_univ _, card_le_univ _⟩)
    (by dsimp only; intro σ z _; exact card_le_univ _)
    (by dsimp only; intro σ z _; exact card_le_univ _)
    (by
      intro x y
      rw [hterm, hpad]
      change |((data HP).binRate 0 * HierarchyTask.usageRatio (channels 1)
        (request HP).terminal (calls HP).direct y) / (1 + G HP x y)| * _ ≤ _
      rw [(hw y).1]
      exact (mul_le_mul_of_nonneg_right (hcoef x y) (by positivity)).trans_eq (one_mul _))
    (by
      intro x y
      rw [hterm, hpad]
      change |((data HP).binRate 0 * HierarchyTask.usageRatio (channels 1)
        (request HP).terminal (calls HP).right y *
        ((BudgetData.midpoint (request HP)).rate /
          (dens {τ : Environment 5 3 | (BudgetData.midpoint (request HP)).retains
            (channels 1) τ y} : ℝ))) / (1 + G HP x y)| * _ ≤ _
      rw [(hw y).2]
      exact (mul_le_mul_of_nonneg_right (hcoef x y)
        (by positivity)).trans_eq (one_mul _))
  unfold payment
  unfold InputProductRegression.X InputProductRegression.Z InputProductRegression.U
  simpa only [hpad, hmid, reference, calls, HierarchyTask.rawRequests, X, Z, U, Nat.cast_ofNat, G]
      using h

-- Unequal positive per-bin budgets, positive precision and inherited source/reset.
example : (data HP).binBudget 64 0 (request HP) = 63 ∧
    (data HP).binBudget 64 1 (request HP) = 59 ∧
    (calls HP).left.source = gridChannel 0 1 [1] ∧
    (calls HP).right.source = gridChannel 1 0 [] ∧
    0 < (data HP).requestPrecision 63 (calls HP).left := by
  have hlog : Real.logb 2 (1 / 16 : ℝ) = -4 := by
    rw [one_div, Real.logb_inv, show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
      Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  norm_num [data, PolynomialBudgetHistory.data, BudgetData.binBudget,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, request, calls,
    LaterInputMeanRegression.request,
    ProductMeanRegression.request, PolynomialBudgetHistory.request, iteration,
    LaterInputMeanRegression.iteration, HierarchyTask.rawRequests,
    BudgetData.midpoint, midpointRole, gridChannel, rate, BudgetData.requestPrecision,
      LogSpaceEstimation.precision, Real.logb_inv,
    hlog]

-- The direct output has actual nonzero error, even though supplied actual children
-- are exact. This is distinct from the initial correction-zero product fixture.
example (σ : Environment 5 3) (x y : ZMod 5) :
    child HP (calls HP).direct σ x y - reference HP (calls HP).direct σ x y =
      (if y = 0 then 1 else 0) := by
  simp only [child, ↓reduceIte]
  ring

-- Successful literal execution differs from the genuine random reference by the column indicator.
-- Its left and right product is present and identical in both samples; only direct
-- error is introduced. This is an execution fixture, not a canonical identity alone.
example : ∃ A,
    (data HP).positiveSample (history HP) ((data HP).binBudget 64 0 (request HP)) 0
      (.input (iteration HP)) (request HP) = some A ∧
    ∀ σ x y, A σ x y - HierarchyTask.rawPositiveSample (channels (1 : ZMod 5))
      0 0 (.input (iteration HP)) (request HP).source (BudgetData.midpoint (request HP))
      (request HP).terminal ((data HP).binRate 0) (fun q => reference HP q σ) x y =
        (if y = 0 then 1 else 0) := by
  refine ⟨_, (data HP).positiveSample_of_rows (history HP) _ 0
    (.input (iteration HP)) (request HP) (child HP) (by intros; exact rows HP _ _), ?_⟩
  intro σ x y
  change HierarchyTask.rawPositiveSample (channels (1 : ZMod 5)) 0 0
    (.input (iteration HP)) (request HP).source (BudgetData.midpoint (request HP))
    (request HP).terminal ((data HP).binRate 0) (fun q => child HP q σ) x y - _ =
      (if y = 0 then 1 else 0)
  have hcalls : HierarchyTask.rawRequests 0 0 (.input (iteration HP))
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0) = calls HP := rfl
  simp only [HierarchyTask.rawPositiveSample, hcalls]
  simp only [child, Ne.symm (different HP).1, (different HP).2.2, ↓reduceIte]
  have hw := (weights HP y).1
  split_ifs <;> nlinarith only [hw]

-- Genuine canonical E and E*C remain positive at the SAME requested iterate.
example (x : ZMod 5) :
    0 < LaterInputMeanRegression.E HP x x ∧
    0 < (LaterInputMeanRegression.E HP * (data HP).base) x x := by
  have he := LaterInputMeanRegression.correction_one HP x
  rw [show LaterInputMeanRegression.E HP * (data HP).base =
    LaterInputMeanRegression.E HP from Matrix.mul_one _, he]
  exact ⟨CutoffRegression.Q_one_pos HP, CutoffRegression.Q_one_pos HP⟩

-- Direct perturbation is nonconstant; its zero-column slice has genuine error.
example (σ : Environment 5 3) (x : ZMod 5) :
    child HP (calls HP).direct σ x 0 - reference HP (calls HP).direct σ x 0 = 1 ∧
    child HP (calls HP).direct σ x 1 - reference HP (calls HP).direct σ x 1 = 0 := by
  simp [child]

-- The same consumer accepts arbitrary positive fine/coarse endpoints.
example (fine coarse : ℕ) :
    ∃ Af Ac, (data HP).positiveSample (history HP) fine 0 (.input (iteration HP))
      (request HP) = some Af ∧
      (data HP).positiveSample (history HP) coarse 0 (.input (iteration HP))
      (request HP) = some Ac := by
  obtain ⟨Af, hfine, _⟩ := executed_bound HP fine
  obtain ⟨Ac, hcoarse, _⟩ := executed_bound HP coarse
  exact ⟨Af, Ac, hfine, hcoarse⟩

-- Both genuine positive dyadic endpoints execute before the paired subtraction.
-- The supplied history is stationary in budget, so their difference is zero;
-- each endpoint still has the nonzero direct error checked above.
private lemma paired (M d : ℕ)
    (hf : 0 < LogSpaceEstimation.lastBudget M d (data HP).slack
      ((data HP).sampleScale (request HP) (some 0)))
    (hc : 0 < LogSpaceEstimation.lastBudget M (2 * d) (data HP).slack
      ((data HP).sampleScale (request HP) (some 0))) :
    (data HP).pairedSample (history HP) M d (.input (iteration HP))
      (request HP) (some 0) = some 0 := by
  have hp (m : ℕ) := (data HP).positiveSample_of_rows (history HP) m 0
    (.input (iteration HP)) (request HP) (child HP) (by intros; exact rows HP _ _)
  unfold BudgetData.pairedSample
  dsimp only
  split_ifs
  · rfl
  · simp [BudgetData.sample, Nat.ne_of_gt hf, Nat.ne_of_gt hc, hp]

-- A concrete unequal positive dyadic pair, independent of binBudget M.
example : (data HP).pairedSample (history HP) 64 8 (.input (iteration HP))
    (request HP) (some 0) = some 0 := by
  apply paired HP
  all_goals norm_num [data, PolynomialBudgetHistory.data, BudgetData.sampleScale,
    request, LaterInputMeanRegression.request, ProductMeanRegression.request,
    PolynomialBudgetHistory.request, gridChannel, rate, LogSpaceEstimation.lastBudget,
    LogSpaceEstimation.scaleCutoff]

example (σ : Environment 5 3) (x : ZMod 5) :
    reference HP (calls HP).direct σ x 0 ^ (4⁻¹ : ℝ) <
      child HP (calls HP).direct σ x 0 ^ (4⁻¹ : ℝ) := by
  have hb := dense_range HP (calls HP).direct rfl σ x 0
  simp only [child, ↓reduceIte]
  exact Real.rpow_lt_rpow hb.1 (lt_add_one _) (by norm_num)

-- The actual denominator retains G=C+E₁*C, rather than the pilot input or residual.
example (x : ZMod 5) : G HP x x = 1 + HP.Q 1 := by
  change (data HP).base x x + (LaterInputMeanRegression.E HP * (data HP).base) x x = _
  rw [show LaterInputMeanRegression.E HP * (data HP).base =
    LaterInputMeanRegression.E HP from Matrix.mul_one _,
    LaterInputMeanRegression.correction_one HP,
    show (data HP).base x x = 1 from Matrix.one_apply_eq x]

end InputProductRegression
