/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of executed later pilot relative product transport)
import Complexity.Foundations.Probability.HierarchyPilotProduct
import Complexity.Foundations.Probability.HierarchyCorrectionStability
import all ComplexityTests.HierarchyPilotMean
import all ComplexityTests.HierarchyPilotCanonicalAlignment
import all ComplexityTests.HierarchyProductMean
import all ComplexityTests.PolynomialBudgetHistory

/-!
# Later pilot execution with supplied histories

Requested input one has genuine positive E_1 and E_1*C. Its source rate is 1/16,
terminal/midpoint rate one, source suffix [1], terminal suffix [2,3], and reset-right
suffix empty. The direct output is shifted by one, while the pilot normalized child
is computed from supplied genuine RAW, own-source PREP and current maximum one.
The histories certify literal successful execution, not recursive availability.
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
namespace PilotProductRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private def data := PolynomialBudgetHistory.data HP
private def iteration := PilotCanonicalAlignmentRegression.iteration HP
private def request := PilotCanonicalAlignmentRegression.request HP
private def calls := HierarchyTask.rawRequests 0 0 (.pilotInput (iteration HP))
  (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
  ((data HP).binRate 0)
private lemma admissible : Admissible (calls HP).left := by
  exact ⟨by change (0 : Fin 3) ≠ 1; decide, rfl, rfl⟩
private def reference := (data HP).pilotInputReference 0 (iteration HP) 0
  (request HP) (admissible HP)
private def child (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :=
  if q = (calls HP).direct then fun σ x y => reference HP q σ x y + 1 else reference HP q
private lemma different :
    (calls HP).direct ≠ (calls HP).left ∧ (calls HP).right ≠ (calls HP).left ∧
      (calls HP).right ≠ (calls HP).direct := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have ht := congrArg HierarchyTask.Request.task h
    change HierarchyTask.baseNormalized 0 0 = .row 0 (.pilotNormalized ⟨0, HP.k_pos⟩) at ht
    contradiction
  · intro h
    have ht := congrArg HierarchyTask.Request.task h
    change HierarchyTask.baseNormalized 0 0 = .row 0 (.pilotNormalized ⟨0, HP.k_pos⟩) at ht
    contradiction
  · intro h
    have ht := congrArg (fun q => q.source.role) h
    change (1 : Fin 3) = 0 at ht
    contradiction
private lemma left : reference HP (calls HP).left =
    pilotChild HP 1 id (calls HP).left (admissible HP) (data HP).base 0 := by
  change (if (calls HP).left = (calls HP).left then _ else _) = _
  simp only [↓reduceIte]
  rfl
private lemma dense (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
    (hq : q ≠ (calls HP).left) : reference HP q =
      denseChild 1 id q ((data HP).cutoff 0) ((data HP).auxiliary 0)
        HP.ρ HP.K (data HP).base := by
  change (if q = (calls HP).left then _ else _) = _
  simp only [hq, ↓reduceIte]
  rfl
private lemma dense_range (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
    (hq : q ≠ (calls HP).left) (σ : Environment 5 3) (x y : ZMod 5) :
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
      request, PilotCanonicalAlignmentRegression.request, ProductMeanRegression.request,
      PolynomialBudgetHistory.request, BudgetData.midpoint, gridChannel, rate]
  rw [hc.1, hc.2]
  exact ⟨PolynomialBudgetHistory.full σ 2 [2, 3] y,
    PolynomialBudgetHistory.full σ 2 [2, 3] y, PolynomialBudgetHistory.full σ 1 [] y⟩

-- Genuine RAW/PREP and CURRENT maximum are supplied at the child's literal budget.
private def pilotHistory (_m : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :
    Option (BudgetValue 5) :=
  if q.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) then
    some (.row (fun _ => pilotRaw HP 1 id (calls HP).left (admissible HP) (data HP).base 0))
  else if q.task = .row 0 (.pilotPreparation ⟨0, HP.k_pos⟩) then
    some (.row (pilotPreparation HP 1 id (calls HP).left (admissible HP) (data HP).base 0))
  else some (.vector (fun _ => PilotTask.value HP.toHierarchyParams
    (stageSource 1 id (calls HP).left (admissible HP)) (splitTerminal 1 id (calls HP).left)
    (calls HP).left.terminal.rate (data HP).base (.maximum 1)))
private lemma normalized (m : ℕ) :
    (data HP).normalized (pilotHistory HP) m (calls HP).left true ⟨0, HP.k_pos⟩ =
      some (reference HP (calls HP).left) := by
  rw [left HP]
  unfold H4RankEnvironment.pilotChild
  simp [BudgetData.normalized, BudgetData.row, vector, pilotHistory,
    data, PolynomialBudgetHistory.data, BudgetValue.row?, BudgetValue.vector?]

private def history (m : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :=
  if q = (calls HP).left then
    ((data HP).normalized (pilotHistory HP) m q true ⟨0, HP.k_pos⟩).map BudgetValue.row
  else some (.row (child HP q))
private lemma rows (m : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) :
    BudgetData.row (history HP) m q = some (child HP q) := by
  by_cases h : q = (calls HP).left
  · subst q
    simp only [history, ↓reduceIte, normalized HP, Option.map_some, BudgetData.row,
      Option.bind_some, BudgetValue.row?, child, Ne.symm (different HP).1, ↓reduceIte]
  · simp only [BudgetData.row, history, h, ↓reduceIte, Option.bind_some, BudgetValue.row?]

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
    PilotCanonicalAlignmentRegression.request, ProductMeanRegression.request,
    PolynomialBudgetHistory.request, gridChannel, rate]

-- This is an executed later POSITIVE sample relative bound, from the three actual
-- own-domain rooted errors. It assumes no parent accuracy and subtracts no E ray.
example : ∃ A,
    (data HP).positiveSample (history HP) ((data HP).binBudget 64 0 (request HP)) 0
      (.pilotInput (iteration HP)) (request HP) = some A ∧
    rowNormPow 4 5 (request HP).source.rate (X HP) (fun _ _ => True)
      (fun σ x y => (A σ x y - HierarchyTask.rawPositiveSample (channels (1 : ZMod 5))
        0 0 (.pilotInput (iteration HP)) (request HP).source (BudgetData.midpoint (request HP))
        (request HP).terminal ((data HP).binRate 0) (fun q => reference HP q σ) x y) /
          ((request HP).terminal.rate + (data HP).base x y)) ≤ payment HP := by
  have hterm : (request HP).terminal.rate = 1 := by norm_num [request,
    PilotCanonicalAlignmentRegression.request, ProductMeanRegression.request,
    PolynomialBudgetHistory.request, gridChannel, rate]
  have hmid : (BudgetData.midpoint (request HP)).rate = 1 := hterm
  have hpad : (data HP).padding = 1 := rfl
  have hcap : 0 ≤ (data HP).atomCap := mul_nonneg (by norm_num) (HP.Q_nonneg _)
  have hcoef (x y : ZMod 5) :
      |(1 : ℝ) / (1 + (data HP).base x y)| ≤ 1 := by
    have hc : 0 ≤ (data HP).base x y := by
      exact ProductMeanRegression.nonneg HP x y
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hw := weights HP
  have h := (data HP).positiveSample_pilot_genuine_relative_le (history HP) 64 0
    (iteration HP) (request HP) (child HP) 0 rfl (admissible HP) (fun _ _ => True)
    (fun x y => (request HP).terminal.rate + (data HP).base x y) KD (KP HP)
    33 (data HP).atomCap 32 (mul_nonneg (by norm_num) (HP.Q_nonneg _)) (by norm_num)
    5 5 5 (rate_pos 1) (rate_pos 0)
    (by intros; exact rows HP _ _)
    (by
      dsimp only
      intro σ x y
      change child HP (calls HP).direct σ x y ∈ Set.Icc 0 33 ∧
        reference HP (calls HP).direct σ x y ∈ Set.Icc 0 33
      have hb := dense_range HP _ (different HP).1 σ x y
      simp only [child, ↓reduceIte]
      exact ⟨⟨by linarith [hb.1], by linarith [hb.2]⟩, ⟨hb.1, by linarith [hb.2]⟩⟩)
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
      have hb := dense_range HP _ (different HP).2.1 σ z y
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
        (request HP).terminal (calls HP).direct y) / (1 + (data HP).base x y)| * _ ≤ _
      rw [(hw y).1]
      exact (mul_le_mul_of_nonneg_right (hcoef x y) (by positivity)).trans_eq (one_mul _))
    (by
      intro x y
      rw [hterm, hpad]
      change |((data HP).binRate 0 * HierarchyTask.usageRatio (channels 1)
        (request HP).terminal (calls HP).right y *
        ((BudgetData.midpoint (request HP)).rate /
          (dens {τ : Environment 5 3 | (BudgetData.midpoint (request HP)).retains
            (channels 1) τ y} : ℝ))) / (1 + (data HP).base x y)| * _ ≤ _
      rw [(hw y).2]
      exact (mul_le_mul_of_nonneg_right (hcoef x y)
        (by positivity)).trans_eq (one_mul _))
  unfold payment
  unfold PilotProductRegression.X PilotProductRegression.Z PilotProductRegression.U
  simpa only [hpad, hmid, reference, calls, HierarchyTask.rawRequests, X, Z, U, Nat.cast_ofNat]
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
    PilotCanonicalAlignmentRegression.request, PilotCanonicalAlignmentRegression.calls,
    ProductMeanRegression.request, PolynomialBudgetHistory.request, iteration,
    PilotCanonicalAlignmentRegression.iteration, HierarchyTask.rawRequests,
    BudgetData.midpoint, midpointRole, gridChannel, rate, BudgetData.requestPrecision,
      LogSpaceEstimation.precision, Real.logb_inv,
    hlog]

-- The direct output has actual nonzero error, even though supplied pilot children
-- are exact. This is distinct from the initial correction-zero product fixture.
example (σ : Environment 5 3) (x y : ZMod 5) :
    child HP (calls HP).direct σ x y - reference HP (calls HP).direct σ x y = 1 := by
  simp only [child, ↓reduceIte]
  ring

-- Successful literal execution differs from the genuine random reference by one.
-- Its left and right product is present and identical in both samples; only direct
-- error is introduced. This is an execution fixture, not a canonical identity alone.
example : ∃ A,
    (data HP).positiveSample (history HP) ((data HP).binBudget 64 0 (request HP)) 0
      (.pilotInput (iteration HP)) (request HP) = some A ∧
    ∀ σ x y, A σ x y - HierarchyTask.rawPositiveSample (channels (1 : ZMod 5))
      0 0 (.pilotInput (iteration HP)) (request HP).source (BudgetData.midpoint (request HP))
      (request HP).terminal ((data HP).binRate 0) (fun q => reference HP q σ) x y = 1 := by
  refine ⟨_, (data HP).positiveSample_of_rows (history HP) _ 0
    (.pilotInput (iteration HP)) (request HP) (child HP) (by intros; exact rows HP _ _), ?_⟩
  intro σ x y
  change HierarchyTask.rawPositiveSample (channels (1 : ZMod 5)) 0 0
    (.pilotInput (iteration HP)) (request HP).source (BudgetData.midpoint (request HP))
    (request HP).terminal ((data HP).binRate 0) (fun q => child HP q σ) x y - _ = 1
  have hcalls : HierarchyTask.rawRequests 0 0 (.pilotInput (iteration HP))
      (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0) = calls HP := rfl
  simp only [HierarchyTask.rawPositiveSample, hcalls]
  simp only [child, Ne.symm (different HP).1, (different HP).2.2, ↓reduceIte]
  have hw := (weights HP y).1
  nlinarith only [hw]

-- Genuine canonical E and E*C remain positive at the SAME requested iterate.
example (x : ZMod 5) :
    0 < PilotCanonicalAlignmentRegression.E HP x x ∧
    0 < (PilotCanonicalAlignmentRegression.E HP * (data HP).base) x x := by
  have he := PilotCanonicalAlignmentRegression.pilot_correction_one HP x
  rw [show PilotCanonicalAlignmentRegression.E HP * (data HP).base =
    PilotCanonicalAlignmentRegression.E HP from Matrix.mul_one _, he]
  exact ⟨CutoffRegression.Q_one_pos HP, CutoffRegression.Q_one_pos HP⟩

-- Nonzero fourth-root discrepancy on every pair, including retained source pairs.
-- The integrated rooted payment is left explicit rather than assigned an invented value.
example (σ : Environment 5 3) (x y : ZMod 5) :
    reference HP (calls HP).direct σ x y ^ (4⁻¹ : ℝ) <
      child HP (calls HP).direct σ x y ^ (4⁻¹ : ℝ) := by
  have hb := dense_range HP _ (different HP).1 σ x y
  simp only [child, ↓reduceIte]
  exact Real.rpow_lt_rpow hb.1 (lt_add_one _) (by norm_num)

end PilotProductRegression
