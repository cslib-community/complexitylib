/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of canonical active bins in the signed consumer)
import Complexity.Foundations.Probability.HierarchyActiveBins
import all ComplexityTests.HierarchyCoarseProductMean

/-!
A non-unit genuine residual has positive E and EC, strict direct/negative
cancellation, and zero off-diagonal targets. The complete conditional family
uses literal own-request precision allowances and positive parent precision.
Successful supplied rows and actual calls are hypotheses, not constructed
recursive availability. The three-bin consumer contains strict coarse, boundary
and fine calls. Different budgets and reset-right sources remain literal. Growing
prime horizons and source/terminal exponents are chosen after a fixed charge;
eventual positive precision is checked, without a general fixed-charge accuracy claim.
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
namespace ActiveBinsRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
private def B : BudgetData HP 5 :=
  {TerminalMeanRegression.smallData HP with bins := range 3}
private def r := TerminalMeanRegression.request HP

-- The negative payment derives its bound even at a genuinely cancelling non-unit input.
example (x : ZMod 5) :
    0 < TerminalMeanRegression.smallE HP x x ∧
    HP.toHierarchyParams.correction (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (B HP).base x x ≤
    max 1 (((HP.k : ℝ) + 1) / HP.θ) *
      HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
        (canonicalChannel id (rate 1)) (rate 1) (B HP).base x x := by
  exact ⟨TerminalMeanRegression.small_correction_pos HP x,
    HP.toHierarchyParams.correction_le_residual _ _ (rate_pos 1)
      (TerminalMeanRegression.small_nonneg HP) (TerminalMeanRegression.small_mass HP)
      (TerminalMeanRegression.small_stage HP) x x⟩

-- The physical normalization can be non-unit even at a zero target.
example : rowNormPow 4 1 1 (fun (_ : Unit) (_ : Unit) => True)
    (fun _ _ => True) (fun _ _ _ => min 1 (|(1 : ℝ)| / (16 + 0))) =
      (1 / 16 : ℝ) ^ 4 := by
  norm_num [rowNormPow]

-- The coarse direct/product call and once-negative request pay different actual budgets.
example : (B HP).binBudget 64 0 (r HP) = 59 ∧ (B HP).childBudget 64 = 63 := by
  have hscale : ⌊Real.logb 2 ((B HP).binRate 0 / (r HP).terminal.rate)⌋ = 4 := by
    change (B HP).sampleScale (r HP) (some 0) = 4
    rw [(B HP).sampleScale_grid (r HP) 1 0 rfl rfl]
    norm_num
  simp only [BudgetData.binBudget, hscale, BudgetData.childBudget,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff]
  norm_num [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
    ProductMeanRegression.data, PolynomialBudgetHistory.data]

-- This family retains all successful-call hypotheses. It does not infer them from IH.
example (M : ℕ) (hpositive : 0 < (B HP).requestPrecision M (r HP))
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) →
      Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → ℝ)
    (hrows : ∀ i ∈ (B HP).bins,
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        BudgetData.row history ((B HP).binBudget M i (r HP)) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      BudgetData.row history ((B HP).childBudget M) q = some (child 0 q))
    (hdirect : ∀ i ∈ (B HP).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate i)).direct
      (B HP).compressedBin ((B HP).binBudget M i (r HP)) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ (B HP).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate i)).left
      (B HP).evaluate ((B HP).binBudget M i (r HP)) q = some (.row (child i q)))
    (hright : ∀ i ∈ (B HP).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate i)).right
      (B HP).compressedBin ((B HP).binBudget M i (r HP)) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      (B HP).evaluate ((B HP).childBudget M) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ (B HP).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate i)).direct
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP).padding) σ y)
        (child i q) ((B HP).residualCanonicalChild i q) ≤ (fun m q => (2 : ℝ) ^ (-(B
        HP).requestPrecision m q)) ((B HP).binBudget M i (r HP)) q ^ 4)
    (hIL : ∀ i ∈ (B HP).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate i)).left
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP).padding) σ y)
        (child i q) ((B HP).residualCanonicalChild i q) ≤ (fun m q => (2 : ℝ) ^ (-(B
        HP).requestPrecision m q)) ((B HP).binBudget M i (r HP)) q ^ 4)
    (hIR : ∀ i ∈ (B HP).bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate i)).right
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP).padding) σ y)
        (child i q) ((B HP).residualCanonicalChild i q) ≤ (fun m q => (2 : ℝ) ^ (-(B
        HP).requestPrecision m q)) ((B HP).binBudget M i (r HP)) q ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      rootDistPow 4 5 q.source.rate
        (fun σ x => q.source.retains (channels (B HP).padding) σ x)
        (fun σ y => q.usage.retains (channels (B HP).padding) σ y)
        (child 0 q) ((B HP).residualCanonicalChild 0 q) ≤ (fun m q => (2 : ℝ) ^ (-(B
        HP).requestPrecision m q)) ((B HP).childBudget M) q ^ 4) :
    0 < (B HP).requestPrecision M (r HP) ∧
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual (r HP).source
        (BudgetData.midpoint (r HP))
        (r HP).terminal ((B HP).binRate i))
    let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), (r HP).source,
        { (r HP).terminal with rate := (BudgetData.midpoint (r HP)).rate },
        { (r HP).terminal with rate := min (r HP).terminal.rate (BudgetData.midpoint (r HP)).rate
        }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let d := fun i => F *
      (((B HP).binRate i * (gridMass 5 1 / gridMass 5 (max 1 i))) / rate 1) *
        (fun m q => (2 : ℝ) ^ (-(B HP).requestPrecision m q)) ((B HP).binBudget M i (r HP)) (Q
        i).direct ^ 4
    let pc := fun i => (F / rate 1) *
      (((B HP).binRate i * ((r HP).terminal.rate / gridMass 5 1)) *
        (gridMass 5 1 / gridMass 5 (max 1 i)) * 33554432 *
        ((if 1 ≤ i then 2 * (B HP).binCap else 0) * HP.K * (fun m q => (2 : ℝ) ^ (-(B
          HP).requestPrecision m q)) ((B
        HP).binBudget M i (r HP)) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            ((r HP).terminal.rate / (r HP).source.rate) * (fun m q => (2 : ℝ) ^ (-(B
        HP).requestPrecision m q)) ((B HP).binBudget M i (r HP)) (Q i).right ^ 4))
    let po := fun i => (1 / rate 1) ^ 4 *
      (4 * (((B HP).binRate i * ((r HP).terminal.rate / gridMass 5 1)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * (B HP).binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      (((B HP).binRate i * ((r HP).terminal.rate / gridMass 5 1)) *
        (gridMass 5 1 / gridMass 5 (max 1 i)) * 33554432 *
        ((if 1 ≤ i then 2 * (B HP).binCap else 0) * HP.K * (fun m q => (2 : ℝ) ^ (-(B
          HP).requestPrecision m q)) ((B
        HP).binBudget M i (r HP)) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            ((r HP).terminal.rate / (r HP).source.rate) * (fun m q => (2 : ℝ) ^ (-(B
        HP).requestPrecision m q)) ((B HP).binBudget M i (r HP)) (Q i).right ^ 4))
    let p := fun i => min (pc i) (po i)
    let ne := F * (fun m q => (2 : ℝ) ^ (-(B HP).requestPrecision m q)) ((B HP).childBudget M) neg
        ^ 4
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
      (canonicalChannel id (rate 1)) (rate 1) (B HP).base
    ∃ executed, (B HP).finiteInput history M .residual (r HP) = some executed ∧
      rowNormPow 4 5 (r HP).source.rate
        (fun σ x => (r HP).source.retains (channels (B HP).padding) σ x)
        (fun σ y => (r HP).terminal.retains (channels (B HP).padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => (r HP).source.retains (channels (B HP).padding) σ x)
          (fun σ y => (r HP).terminal.retains (channels (B HP).padding) σ y)
          executed x y - G x y| /
            (rate 1 + G x y))) ≤
        (ne ^ (4⁻¹ : ℝ) + ∑ i ∈ (B HP).bins, d i ^ (4⁻¹ : ℝ) +
          ∑ i ∈ (B HP).bins, p i ^ (4⁻¹ : ℝ)) ^ 4 := by
  refine ⟨hpositive, ?_⟩
  have hbins : (B HP).bins = range (2 + 1) := by
    ext j
    simp [B, TerminalMeanRegression.smallData, TerminalMeanRegression.data,
      ProductMeanRegression.data, PolynomialBudgetHistory.data]
  have hθ : HP.θ ≤ (1 / 2 : ℝ) := by
    have h := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at h
    linarith
  have hkh (i : ℕ) (_hi : i ∈ (B HP).bins) (v : ℝ)
      (hv : (B HP).cutoff i v ≠ 0) : (B HP).auxiliary i v = 1 :=
    HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      i (fun _ => 1) hv
  have hl (i : ℕ) (_hi : i ∈ (B HP).bins) (d : ℝ) (hd : d ≤ HP.θ) :
      (B HP).cutoff i d = 0 :=
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
  exact (B HP).finiteInput_residual_clipped_active_le 2 hbins rfl rfl rfl
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
    (fun m q => (2 : ℝ) ^ (-(B HP).requestPrecision m q))
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN


-- This is the concrete non-unit base, with positive E/EC above, on the actual common seed.
example (σ : Environment 5 3) (z y : ZMod 5) :
    (B HP).residualCanonicalChild 0
      (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual (r HP).source
        (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate 0)).right σ z y = 0 := by
  exact (B HP).residualCanonicalRight_zero_of_lt rfl rfl 0 1 (r HP)
    (TerminalMeanRegression.small_stage HP) (by decide) σ z y

-- Boundary and fine-bin left coefficients are retained. Strict coarse removal is exact.
example : (if 1 ≤ 0 then (2 : ℝ) * 16 else 0) = 0 ∧
    (if 1 ≤ 1 then (2 : ℝ) * 16 else 0) = 32 ∧
    (if 1 ≤ 2 then (2 : ℝ) * 16 else 0) = 32 := by norm_num

-- A fixed charge precedes every source/terminal exponent and every positive-precision budget.
-- This is eventual precision only, without a fixed-charge accuracy claim.
example (A : ℝ) :
    ∀ (P : ℕ) (D : BudgetData HP P), D.rankCharge = A →
      ∀ (ks ka : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
        q.source.rate = rate ks → q.terminal.rate = rate ka →
        ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < D.requestPrecision M q := by
  intro P D _ ks ka q hs ht
  exact D.grid_precision_eventually_pos ks ka q hs ht

-- The fine direct nominal salary grows: the existing clipped direct coefficient is
-- bounded below independently of the fine offset and supplies no compensating decay.
example : (1 / 16 : ℝ) ≤
    (rate 2 * (gridMass 5 1 / gridMass 5 (max 1 2))) / rate 1 :=
  BudgetData.residualDirect_fine_coefficient_lower SourceRegression.horizon 1 2
    (by decide) (by decide) (by decide)

example (M : ℕ) (hM : (B HP).slack * 5 ≤ M) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 2 .residual (r HP).source
      (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP).binRate 2)).direct
    (2 : ℝ) ^ (-(B HP).requestPrecision ((B HP).binBudget M 2 (r HP)) q) =
      (2 : ℝ) ^ (-(B HP).requestPrecision M (r HP)) *
        (2 : ℝ) ^ (37 / 16 - (80 * (HP.k : ℝ) + 94) * (B HP).rankCharge) := by
  convert (B HP).requestPrecision_residual_fine_direct M 2 1 2 (r HP) rfl rfl rfl rfl
    (by decide) (by simpa using hM) using 1; norm_num

-- The repair does not assert approximate right support. Even when the true table
-- vanishes, the exact coupled expansion retains the whole right error.
example (a c e : ℝ) : a * e - c * 0 = a * (e - 0) + (a - c) * 0 := by ring

-- Zero and the threshold endpoint have zero actual cutoff; active boundary/fine
-- matrix scales retain their nonzero canonical cutoff.
example : (B HP).cutoff 0 (0 / (B HP).binRate 0) = 0 ∧
    (B HP).cutoff 0 ((rate 0 / 2) / (B HP).binRate 0) = 0 := by
  constructor
  · apply (B HP).residual_cutoff_zero_of_le_half rfl rfl
    exact div_nonneg (rate_pos 0).le (by norm_num)
  · exact (B HP).residual_cutoff_zero_of_le_half rfl rfl 0 _ le_rfl

-- Charge first; then arbitrary bin horizon, source and terminal exponents. The prime
-- horizon is actually constructed, and every sufficiently large budget is active.
-- This does not supply simultaneous successful recursive rows or a paid accuracy bound.
example (A : ℝ) (n ks ka : ℕ) :
    ∃ (P : ℕ) (hP : P.Prime),
      let : Fact P.Prime := ⟨hP⟩
      ∃ (H : Horizon P) (D : BudgetData HP P)
        (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
        D.rankCharge = A ∧ D.bins = range (n + 1) ∧
        max n (max ks ka) ≤ H.maxExponent ∧
        q.source.rate = rate ks ∧ q.terminal.rate = rate ka ∧
        (∀ x y, D.base x y ≤ rate ka) ∧
        ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < D.requestPrecision M q := by
  obtain ⟨P, hP, _, _, H, hH, _⟩ :=
    exists_bounded_depth_prime (max n (max ks ka) + 1) 0 (by positivity)
  let : Fact P.Prime := ⟨hP⟩
  let D : BudgetData HP P :=
    {ProductAllocationRegression.data HP P 0 n with
      rankCharge := A, base := rate ka • (1 : Matrix (ZMod P) (ZMod P) ℝ)}
  let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.residual 0, gridChannel 0 ks [1], gridChannel 2 ka [2, 3],
      gridChannel 2 ka [2, 3]⟩
  refine ⟨P, hP, H, D, q, rfl, rfl, ?_, rfl, rfl, ?_,
    D.grid_precision_eventually_pos ks ka q rfl rfl⟩
  · rw [hH]
    omega
  · intro x y
    by_cases h : x = y
    · simp [D, h]
    · simp [D, h, (rate_pos ka).le]

end ActiveBinsRegression
