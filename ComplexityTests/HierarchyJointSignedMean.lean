/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of joint signed residual mean allocation)
import Complexity.Foundations.Probability.HierarchyJointSignedMean
import all ComplexityTests.HierarchyCoarseProductMean

/-!
Charge precedes arbitrary growing prime horizons and all source/terminal/bin
exponents. Both direct quarter and product-plus-negative three quarters use
literal own-request precision, with eventual positive precision. The concrete
three-bin consumer has positive E and EC, non-unit base and zero targets.
Successful calls and IH remain supplied hypotheses, not joint recursive availability.
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
namespace JointSignedRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8) (A : ℕ)
private def B : BudgetData HP 5 :=
  {TerminalMeanRegression.smallData HP with bins := range 3, rankCharge := A}
private def r := TerminalMeanRegression.request HP

-- The negative payment derives its bound even at a genuinely cancelling non-unit input.
example (x : ZMod 5) :
    0 < TerminalMeanRegression.smallE HP x x ∧
    HP.toHierarchyParams.correction (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (B HP A).base x x ≤
    max 1 (((HP.k : ℝ) + 1) / HP.θ) *
      HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
        (canonicalChannel id (rate 1)) (rate 1) (B HP A).base x x := by
  exact ⟨TerminalMeanRegression.small_correction_pos HP x,
    HP.toHierarchyParams.correction_le_residual _ _ (rate_pos 1)
      (TerminalMeanRegression.small_nonneg HP) (TerminalMeanRegression.small_mass HP)
      (TerminalMeanRegression.small_stage HP) x x⟩

-- The product correction is positive and the signed subtraction is strict on the
-- same non-unit base used by the executed consumer below.
example (x : ZMod 5) :
    0 < (TerminalMeanRegression.smallE HP * (B HP A).base) x x ∧
    HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (B HP A).base x x <
      ((B HP A).base + TerminalMeanRegression.smallE HP * (B HP A).base) x x := by
  have he := TerminalMeanRegression.small_correction_pos HP x
  have hm : (TerminalMeanRegression.smallE HP * (B HP A).base) x x =
      rate 1 * TerminalMeanRegression.smallE HP x x := by
    simp only [B, TerminalMeanRegression.smallData, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_apply, smul_eq_mul]
  refine ⟨by rw [hm]; exact mul_pos (rate_pos 1) he, ?_⟩
  rw [HP.toHierarchyParams.residual_eq, ← HP.toHierarchyParams.correctionIter_last]
  change ((B HP A).base - TerminalMeanRegression.smallE HP +
    TerminalMeanRegression.smallE HP * (B HP A).base) x x < _
  simp only [Matrix.add_apply, Matrix.sub_apply]
  linarith

-- The guards of the concrete consumer can be fixed first, and positive parent
-- precision follows at every sufficiently large budget; successful calls remain separate.
example (A₀ : ℕ) : ∃ A : ℕ, A₀ ≤ A ∧
    BudgetData.residualDirectRootCost HP (B HP A).binCap *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * A) ≤ 1 / 4 ∧
    BudgetData.residualProductNegativeRootCost HP (B HP A).binCap *
      (2 : ℝ) ^ (1 / 16 - 32 * (A : ℝ)) ≤ 3 / 4 ∧
    ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < (B HP A).requestPrecision M (r HP) := by
  obtain ⟨A, ha, hd, hp⟩ :=
    BudgetData.exists_residualJoint_charge (HP := HP) 16 (by norm_num) A₀
  exact ⟨A, ha, hd, hp, (B HP A).grid_precision_eventually_pos 2 1 (r HP) rfl rfl⟩

-- The physical normalization can be non-unit even at a zero target.
example : rowNormPow 4 1 1 (fun (_ : Unit) (_ : Unit) => True)
    (fun _ _ => True) (fun _ _ _ => min 1 (|(1 : ℝ)| / (16 + 0))) =
      (1 / 16 : ℝ) ^ 4 := by
  norm_num [rowNormPow]

-- The coarse direct/product call and once-negative request pay different actual budgets.
example : (B HP A).binBudget 64 0 (r HP) = 59 ∧ (B HP A).childBudget 64 = 63 := by
  have hscale : ⌊Real.logb 2 ((B HP A).binRate 0 / (r HP).terminal.rate)⌋ = 4 := by
    change (B HP A).sampleScale (r HP) (some 0) = 4
    rw [(B HP A).sampleScale_grid (r HP) 1 0 rfl rfl]
    norm_num
  simp only [BudgetData.binBudget, hscale, BudgetData.childBudget,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
    ProductMeanRegression.data, PolynomialBudgetHistory.data]

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
      (2 : ℝ) ^ (1 / 16 - 32 * (A : ℝ)) ≤ 3 / 4) :
    0 < (B HP A).requestPrecision M (r HP) ∧
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (B HP A).base
    ∃ executed, (B HP A).finiteInput history M .residual (r HP) = some executed ∧
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
  exact (B HP A).finiteInput_residual_clipped_joint_le 2 hbins rfl rfl rfl
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

-- This is the concrete non-unit base, with positive E/EC above, on the actual common seed.
example (σ : Environment 5 3) (z y : ZMod 5) :
    (B HP A).residualCanonicalChild 0
      (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual (r HP).source
        (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate 0)).right σ z y = 0 := by
  exact (B HP A).residualCanonicalRight_zero_of_lt rfl rfl 0 1 (r HP)
    (TerminalMeanRegression.small_stage HP) (by decide) σ z y

-- Boundary and fine-bin left coefficients are retained. Strict coarse removal is exact.
example : (if 1 ≤ 0 then (2 : ℝ) * 16 else 0) = 0 ∧
    (if 1 ≤ 1 then (2 : ℝ) * 16 else 0) = 32 ∧
    (if 1 ≤ 2 then (2 : ℝ) * 16 else 0) = 32 := by norm_num

-- Zero and the threshold endpoint have zero actual cutoff; active boundary/fine
-- matrix scales retain their nonzero canonical cutoff.
example : (B HP A).cutoff 0 (0 / (B HP A).binRate 0) = 0 ∧
    (B HP A).cutoff 0 ((rate 0 / 2) / (B HP A).binRate 0) = 0 := by
  constructor
  · apply (B HP A).residual_cutoff_zero_of_le_half rfl rfl
    exact div_nonneg (rate_pos 0).le (by norm_num)
  · exact (B HP A).residual_cutoff_zero_of_le_half rfl rfl 0 _ le_rfl

-- Exhausted budgets are covered by the general loss bound as well as active ones.
example : (B HP A).binBudget 0 2 (r HP) = 0 := by
  simp only [BudgetData.binBudget, LogSpaceEstimation.lastBudget, Nat.zero_sub]

-- A perfectly mask-correlated table has the predicted smaller parent mean.
example : rowSliceMean (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
    (fun σ _ _ => if σ then (1 : ℝ) else 0) () () = 1 / 2 := by
  norm_num [rowSliceMean, Finset.expect, Fintype.sum_bool]

-- The two offset sides have a count-free bound even on a growing horizon.
example (n a : ℕ) :
    (∑ i ∈ range (n + 1), (2 : ℝ) ^ (-3 * |(i : ℝ) - a| / 4)) ≤
      2 / (1 - (2 : ℝ) ^ (-3 / 4 : ℝ)) :=
  sum_two_rpow_offset_le _ _

-- The same draw determines usage and error: conditioning on usage gives one,
-- while the larger parent slice above gives one half. No independent error is used.
example : rowSliceMean (fun (_ : Bool) (_ : Unit) => True) (fun σ _ => σ = true)
    (fun σ _ _ => if σ then (1 : ℝ) else 0) () () = 1 := by
  have hc : ({x ∈ ({false, true} : Finset Bool) | x = true}).card = 1 := by decide
  norm_num [rowSliceMean, Finset.expect, hc,
    show (Finset.univ : Finset Bool) = {false, true} from by decide]

-- The coefficient retains the literal rounded masses on the fine bin.
example : (256 * (2 * (B HP A).binCap) ^ 3) *
    ((rate 2 / rate 1) ^ 4 * (gridMass 5 1 / gridMass 5 (max 1 2))) =
      (81 / 512 : ℝ) * (B HP A).binCap ^ 3 := by
  norm_num [gridMass, side, rate, Nat.ceilDiv_eq_add_pred_div]
  ring


-- The common charge precedes the field, full bin horizon, source/terminal exponents
-- and positive precision. Literal allowances pay both parts; no children are invented.
example (A₀ : ℕ) : ∃ A : ℕ, A₀ ≤ A ∧
    ∀ (n ks ka : ℕ), ka ≤ ks →
    ∃ (P : ℕ) (hP : P.Prime),
      let : Fact P.Prime := ⟨hP⟩
      ∃ (H : Horizon P) (D : BudgetData HP P)
        (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
        D.rankCharge = A ∧ D.binCap = 16 ∧ D.bins = range (H.maxExponent + 1) ∧
        max n (max ks ka) ≤ H.maxExponent ∧
        r.source.rate = rate ks ∧ r.terminal.rate = rate ka ∧
        r.source.suffix = [1] ∧ r.terminal.suffix = [2, 3] ∧
        (∀ x y, D.base x y ≤ rate ka) ∧
        ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < D.requestPrecision M r ∧
          let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (BudgetData.midpoint r) r.terminal (D.binRate i))
          let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (BudgetData.midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (BudgetData.midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
          let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
          let ε := fun m q => (2 : ℝ) ^ (-D.requestPrecision m q)
          (∑ i ∈ D.bins, (min
      (F * ((D.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (D.binBudget M i r) (Q i).direct ^ 4)
      ((256 * (2 * D.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
        ε (D.binBudget M i r) (Q i).direct ^ 4)) ^ (4⁻¹ : ℝ)) ≤
            (2 : ℝ) ^ (-D.requestPrecision M r) / 4 ∧
          (F * ε (D.childBudget M) neg ^ 4) ^ (4⁻¹ : ℝ) +
            (∑ i ∈ D.bins, (min ((F / rate ka) *
      ((D.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * D.binCap else 0) * HP.K * ε (D.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (D.binBudget M i r) (Q i).right ^ 4)))
              ((1 / rate ka) ^ 4 *
      (4 * ((D.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * D.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((D.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * D.binCap else 0) * HP.K * ε (D.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) *
          ε (D.binBudget M i r) (Q i).right ^ 4)))) ^ (4⁻¹ : ℝ)) ≤
            3 * (2 : ℝ) ^ (-D.requestPrecision M r) / 4 := by
  obtain ⟨A, hA₀, hd, hp⟩ :=
    BudgetData.exists_residualJoint_charge (HP := HP) 16 (by norm_num) A₀
  refine ⟨A, hA₀, ?_⟩
  intro n ks ka hka
  obtain ⟨P, hP, _, _, H, hH, _⟩ :=
    exists_bounded_depth_prime (max n (max ks ka) + 1) 0 (by positivity)
  let : Fact P.Prime := ⟨hP⟩
  let D : BudgetData HP P :=
    {ProductAllocationRegression.data HP P A H.maxExponent with
      base := rate ka • (1 : Matrix (ZMod P) (ZMod P) ℝ)}
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.residual 0, gridChannel 0 ks [1], gridChannel 2 ka [2, 3], gridChannel 2 ka [2, 3]⟩
  change BudgetData.residualDirectRootCost HP D.binCap *
    (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * D.rankCharge) ≤ 1 / 4 at hd
  change BudgetData.residualProductNegativeRootCost HP D.binCap *
    (2 : ℝ) ^ (1 / 16 - 32 * D.rankCharge) ≤ 3 / 4 at hp
  have hn : max n (max ks ka) ≤ H.maxExponent := by rw [hH]; omega
  have ha : ka ≤ H.maxExponent := (le_max_right ks ka).trans ((le_max_right _ _).trans hn)
  have hi (i : ℕ) (hib : i ∈ D.bins) : i ≤ H.maxExponent := by
    change i ∈ range (H.maxExponent + 1) at hib
    have hh := mem_range.mp hib
    omega
  obtain ⟨M₀, hM₀⟩ := D.grid_precision_eventually_pos ks ka r rfl rfl
  refine ⟨P, hP, H, D, r, rfl, rfl, rfl, hn, rfl, rfl, rfl, rfl, ?_, M₀, ?_⟩
  · intro x y
    by_cases h : x = y
    · simp [D, h]
    · simp [D, h, (rate_pos ka).le]
  · intro M hM
    refine ⟨hM₀ M hM, ?_, ?_⟩
    · have hh := D.residualDirect_min_sum_salary H M ks ka ha hi r rfl rfl rfl rfl
      have hf := mul_le_mul_of_nonneg_right hd
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-D.requestPrecision M r))
      dsimp only [BudgetData.residualDirectRootCost] at hf
      exact hh.trans (by convert hf using 1 <;> ring)
    · exact D.residualProduct_negative_sum_le H M ks ka ha hi r rfl rfl rfl rfl
        hka (Nat.cast_nonneg A) hp

end JointSignedRegression
