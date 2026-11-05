/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyJointProduct
public import Complexity.Foundations.Probability.HierarchyRawSemanticDeficit
import all Complexity.Foundations.Probability.HierarchyInitialMeanUniform
import Complexity.Foundations.Probability.SignedResidualBins

/-!
# Clipped means of actual RAW with exhausted positive endpoints

The actual schedule uses literal zero at exhausted budgets. Positive endpoint
comparisons use successful own-request scalar child bounds, while missing positive
canonical rays are retained as the genuine deterministic omission. No recursive
success at budget zero is required. This original finite-sum consumer does not
construct recursive availability or establish the full changing-request invariant.
Finite positive-entry coverage, full terminal usage and admitted distinct grid
roles remain explicit. The final consumer has positive parent precision but no
all-positive-bin-budget guard and no depth-to-maximum-budget hypothesis.

## Main results

* `raw_residual_mean_active_omission`: actual active errors and genuine omitted mass.
* `residualOmittedPositive_clipped_uniform_le`: width-free semantic payment after slack.
* `raw_residual_clipped_scalar_omission_le`: actual own-mask scalar comparisons and minima.
* `exists_residualRawMean_charge`: primitive charge before fields and horizons.
* `raw_residual_clipped_parent_le`: final actual RAW clipped mean at parent precision.

General prefix active-error allocation and weighted prefix summation, centered
RAW noise, completion and the recursive invariant are not proved here.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- The actual final RAW mean separates active direct/product errors, the once-negative
error and the genuine omitted positive mean. Rows are required only at positive budgets. -/
theorem raw_residual_mean_active_omission
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hcover : ∀ z y, B.base z y = 0 ∨ rate n ≤ B.base z y)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hrows : ∀ i ∈ B.bins, 0 < B.binBudget M i r →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history (B.binBudget M i r) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history (B.childBudget M) q = some (child 0 q))
    (husage : r.usage = r.terminal) (hnlive : 0 < B.childBudget M)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C)) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i))
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
        (canonicalChannel id (rate ka)) (rate ka) B.base
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
    let de := fun i x y => if 0 < B.binBudget M i r then
      (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
        rowSliceMean X Y (fun σ x y =>
          child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y else 0
    let pe := fun i x y => if 0 < B.binBudget M i r then
      B.residualProductMean i r (child i (Q i).left)
      (child i (Q i).right) x y - B.residualProductMean i r
        (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y else 0
    let nege := fun x y => -rowSliceMean X Y (fun σ x y =>
      HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
        r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
      HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
        r.source (midpoint r) r.terminal (B.binRate 0)
        (fun q => B.residualCanonicalChild 0 q σ) x y) x y
    let omission := fun x y => -B.residualOmittedPositive M (Nat.log2 M) ka r x y
    ∃ executed, B.raw history M .residual r = some executed ∧ ∀ x y,
      rowSliceMean X Y executed x y - G x y =
        omission x y + nege x y + ∑ i ∈ B.bins, de i x y + ∑ i ∈ B.bins, pe i x y := by
  dsimp only
  let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let de := fun i x y => if 0 < B.binBudget M i r then
    (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
      rowSliceMean X Y (fun σ x y =>
        child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y else 0
  let pe := fun i x y => if 0 < B.binBudget M i r then
    B.residualProductMean i r (child i (Q i).left)
    (child i (Q i).right) x y - B.residualProductMean i r
      (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y else 0
  let nege := fun x y => -rowSliceMean X Y (fun σ x y =>
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0)
      (fun q => B.residualCanonicalChild 0 q σ) x y) x y
  let omission := fun x y => -B.residualOmittedPositive M (Nat.log2 M) ka r x y
  have hsgrid : r.source = gridChannel r.source.role ks r.source.suffix := by
    change r.source = {r.source with rate := rate ks}
    rw [← hs]
  have htgrid : r.terminal = gridChannel r.terminal.role ka r.terminal.suffix := by
    change r.terminal = {r.terminal with rate := rate ka}
    rw [← ht]
  obtain ⟨Fgroup, _, hraw, hmean⟩ := B.raw_prefix_mean history M .residual r
    r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
    hsgrid (husage.trans htgrid) hcalls (Nat.log2 M) (by omega)
  have href (x y : ZMod P) : rowSliceMean X Y (B.residualCanonicalInput r) x y = G x y :=
    B.residualCanonicalInput_mean n hbins hrate hcutoff haux hD H hnH
      r r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
      hsgrid htgrid hks hka hC hC1 hCf x y (fun z => hcover z y)
  have homit (x y : ZMod P) : rowSliceMean X Y
      (fun σ x y => ∑ i ∈ B.bins,
        if B.binBudget M i r = 0 then B.residualCanonicalRay r (some i) σ x y else 0)
      x y = B.residualOmittedPositive M (Nat.log2 M) ka r x y := by
    have hm := B.residualOmittedPositive_mean n hbins hrate hcutoff haux hD H hnH
      M r r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
      hsgrid htgrid hks hka hC hC1 hCf (Nat.log2 M) x y
    simpa only [dyadicSlack_last, B.raw_positive_budget] using hm
  have hratio (i : ℕ) (y : ZMod P) : HierarchyTask.usageRatio (channels B.padding)
      r.terminal (Q i).direct y = gridMass P ka / gridMass P (max ka i) := by
    apply usageRatio_grid B.padding r.terminal (Q i).direct ka (max ka i) ht
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hrate, rate_min]
  have hpositive (i : ℕ) (hi : i ∈ B.bins) (x y : ZMod P) :
      rowSliceMean X Y (fun σ x y =>
        (B.sample history (B.binBudget M i r) .residual r (some i)).getD 0 σ x y -
          B.residualCanonicalRay r (some i) σ x y) x y =
        de i x y + pe i x y - rowSliceMean X Y
          (fun σ x y => if B.binBudget M i r = 0 then
            B.residualCanonicalRay r (some i) σ x y else 0) x y := by
    by_cases hlive : 0 < B.binBudget M i r
    · have hr (q) (hq : q ∈ ({(Q i).direct, (Q i).left, (Q i).right} : Finset _)) :=
        hrows i hi hlive q hq
      have hd := hr (Q i).direct (by simp)
      have hl := hr (Q i).left (by simp)
      have hri := hr (Q i).right (by simp)
      dsimp only [Q] at hd hl hri
      simp only [sample, hlive, Nat.ne_of_gt hlive, ↓reduceIte, positiveSample, hd, hl, hri,
        bind, Option.bind_some, pure, Option.getD_some, de, pe, residualCanonicalRay,
        HierarchyTask.rawPositiveSample, rowSliceMean, expect_sub_distrib,
        expect_add_distrib, residualProductMean, conditionalTableMean, expect_const_zero,
        sub_zero]
      dsimp only [Q] at hratio ⊢
      simp_rw [hratio, ← mul_expect]
      ring
    · have hz : B.binBudget M i r = 0 := by omega
      simp only [hz, sample_zero, Option.getD_some, Pi.zero_apply, Matrix.zero_apply,
        zero_sub, de, pe, Nat.lt_irrefl, ↓reduceIte, zero_add, rowSliceMean,
        expect_neg_distrib]
  have hnegative (x y : ZMod P) : rowSliceMean X Y
      (fun σ x y => (B.sample history (B.childBudget M) .residual r none).getD 0 σ x y -
        B.residualCanonicalRay r none σ x y) x y = nege x y := by
    simp only [sample, Nat.ne_of_gt hnlive, ↓reduceIte, hnrow, bind, Option.bind_some,
      pure, Option.getD_some, residualCanonicalRay, HierarchyTask.rawNegativeSample,
      HierarchyTask.rawRequests, nege, Pi.neg_apply,
      rowSliceMean, expect_sub_distrib, expect_neg_distrib]
    simp only [← mul_expect]
    ring
  have herr (x y : ZMod P) : rowSliceMean X Y
      (fun σ x y => ∑ i ∈ range (Nat.log2 M + 1), Fgroup i σ x y) x y - G x y =
      omission x y + nege x y + ∑ i ∈ B.bins, de i x y + ∑ i ∈ B.bins, pe i x y := by
    have hm := hmean x y
    have hm' : rowSliceMean X Y
        (fun σ x y => ∑ i ∈ range (Nat.log2 M + 1), Fgroup i σ x y) x y =
        rowSliceMean X Y (fun σ x y => ((B.rays .residual).map fun bin =>
          (B.sample history (LogSpaceEstimation.lastBudget M
            (dyadicSlack (Nat.log2 M + 1) (Nat.log2 M)) B.slack (B.sampleScale r bin))
            .residual r bin).getD 0 σ x y).sum) x y := by
      simpa only [rowSliceMean, X, Y, CorrectionRowTask.Channel.retains,
        channels, semanticSide_grid, hs, ht, H4RankEnvironment.X, H4RankEnvironment.Y] using hm
    rw [hm', dyadicSlack_last, ← href x y]
    change (𝔼 σ ∈ _, _) - (𝔼 σ ∈ _, _) = _
    rw [← expect_sub_distrib]
    have hp : (fun σ => ((B.rays .residual).map fun bin =>
        (B.sample history (LogSpaceEstimation.lastBudget M 1 B.slack
          (B.sampleScale r bin)) .residual r bin).getD 0 σ x y).sum -
        B.residualCanonicalInput r σ x y) =
        (fun σ => ∑ i ∈ B.bins,
          ((B.sample history (B.binBudget M i r) .residual r (some i)).getD 0 σ x y -
            B.residualCanonicalRay r (some i) σ x y) +
          ((B.sample history (B.childBudget M) .residual r none).getD 0 σ x y -
            B.residualCanonicalRay r none σ x y)) := by
      funext σ
      rw [← B.residualCanonicalRay_sum r σ x y]
      simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def,
        B.raw_positive_budget, B.raw_negative_budget, sum_map_toList, sum_sub_distrib]
      ring
    change (𝔼 σ ∈ _, _) = _
    rw [hp, expect_add_distrib, expect_sum_comm]
    simp only [rowSliceMean] at hpositive hnegative
    rw [sum_congr rfl (fun i hi => hpositive i hi x y), hnegative]
    simp only [sum_sub_distrib, sum_add_distrib]
    have ho := homit x y
    change (𝔼 σ ∈ _, ∑ i ∈ B.bins, _) = _ at ho
    rw [expect_sum_comm] at ho
    rw [ho]
    dsimp only [omission]
    ring
  exact ⟨_, hraw, herr⟩

/-- The genuine omitted direct-plus-product mass has a width-free clipped fourth
moment. True residual row mass supplies the integration measure; the entry bound
comes from the literal schedule. The cubic entry cost has no factor of `P`. -/
theorem residualOmittedPositive_clipped_entry_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (M j ks ka : ℕ) (H : Horizon P)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka) {b : ℝ} (hb : 0 ≤ b)
    (hentry : ∀ x y, B.residualOmittedPositive M j ka r x y ≤ b) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|B.residualOmittedPositive M j ka r x y| /
        (rate ka + G x y))) ≤ 256 * K * (b / rate ka) ^ 3 := by
  dsimp only
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
    (canonicalChannel id (rate ka)) (rate ka) B.base
  let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
  have hG (x y) : 0 ≤ G x y := HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y
  have hG1 : G *ᵥ 1 ≤ 1 := by
    intro x
    simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using
      HP.toHierarchyParams.residual_sum_le_one (canonicalChannel id (rate ka))
        (canonicalChannel id (rate ka)) (rate_pos ka) hC1 x
  have hL (x y) : 0 ≤ B.residualOmittedPositive M j ka r x y := by
    have hseq := HP.toHierarchyParams.isCorrectionSeq_correctionIter
      (X := canonicalChannel id (rate ka)) (Y := canonicalChannel id (rate ka))
      (rate_pos ka) hC
    have hfine (x y) : 0 ≤ B.initialFineLoss M (Nat.log2 M + 1) j r x y := by
      unfold initialFineLoss
      apply sum_nonneg
      intro i _
      split_ifs
      · exact mul_nonneg (by rw [hrate]; exact (rate_pos i).le) (B.cutoff_bounds i _).1
      · exact le_rfl
    exact add_nonneg (hfine x y) (sum_nonneg fun z _ =>
      mul_nonneg (hseq.nonneg HP.k x z) (hfine z y))
  let B' : BudgetData HP P := {B with base := G}
  let roles : RoleProfile 3 :=
    ⟨r.source.role, midpointRole r.source.role r.terminal.role, r.terminal.role,
      (midpointRole_distinct _ _).1, hst, (midpointRole_distinct _ _).2⟩
  have h := B'.grid_trueMass_le roles ks ka r.source.suffix r.terminal.suffix H
    hks hka hG1
    (fun x y => min 1 (|B.residualOmittedPositive M j ka r x y| / (rate ka + G x y)))
    (c := K * b ^ 3 / rate ka ^ 4) (by dsimp only [K]; positivity) ?_
  · have he : 256 * rate ka * (K * b ^ 3 / rate ka ^ 4) =
        256 * K * (b / rate ka) ^ 3 := by field_simp
    rw [he] at h
    dsimp only [B', roles] at h
    unfold Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments.retainedMask at h
    simp only [CorrectionRowTask.Channel.retains, channels, semanticSide_grid, hs, ht, G, K]
      at h ⊢
    convert h using 1
    simp [rowNormPow]
  intro x y
  have hLK := B.residualOmittedPositive_le_residual n hbins hrate hcutoff M r ka
    hC hC1 hCf j x y
  have hf := rate_pos ka
  have hz : 0 ≤ min 1 (|B.residualOmittedPositive M j ka r x y| /
      (rate ka + G x y)) :=
    le_min (by norm_num) (div_nonneg (abs_nonneg _) (add_nonneg hf.le (hG x y)))
  have hzL : min 1 (|B.residualOmittedPositive M j ka r x y| /
      (rate ka + G x y)) ≤ B.residualOmittedPositive M j ka r x y / rate ka := by
    apply (min_le_right _ _).trans
    rw [abs_of_nonneg (hL x y)]
    exact div_le_div_of_nonneg_left (hL x y) (rate_pos ka)
      (le_add_of_nonneg_right (hG x y))
  rw [abs_of_nonneg hz]
  calc
    _ ≤ (B.residualOmittedPositive M j ka r x y / rate ka) ^ 4 :=
      pow_le_pow_left₀ hz hzL 4
    _ = (B.residualOmittedPositive M j ka r x y) ^ 3 *
        B.residualOmittedPositive M j ka r x y / rate ka ^ 4 := by rw [div_pow]; ring
    _ ≤ b ^ 3 * (K * G x y) / rate ka ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ (hL x y) (hentry x y) 3)
        hLK (hL x y) (by positivity)
    _ = _ := by dsimp only [B']; ring

/-- Actual exhausted positive rays fit a uniform rooted semantic allowance after
surviving temporal slack. Finite positive-entry coverage already removes the
unretained tail; no retained-depth versus maximum-budget hypothesis is added here. -/
theorem residualOmittedPositive_clipped_uniform_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (M j ks ka : ℕ) (H : Horizon P)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hcharge : 1 ≤ B.rankCharge) (hrank : 1 ≤ r.task.rank)
    (hp : 0 < B.requestPrecision M r)
    (hd : dyadicSlack (Nat.log2 M + 1) j < M) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
    let C := 4 * (1 + K) * (1 + 2 * ((HP.k : ℝ) + 1) * B.binCap)
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|B.residualOmittedPositive M j ka r x y| /
        (rate ka + G x y))) ≤
      (C * (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)) ^ 4 := by
  dsimp only
  let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
  let D := 1 + 2 * ((HP.k : ℝ) + 1) * B.binCap
  let w := (2 : ℝ) ^ (-(4 / 3 : ℝ) * (B.requestPrecision M r + B.rankCharge))
  let t := (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  have hcap := B.binCap_nonneg
  have hf := rate_pos ka
  have hK : 1 ≤ K := le_max_left _ _
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((HP.k : ℝ) + 1)) hcap]
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hhi : M ≤ 32 * B.slack * M := by
    have hslack := B.slack_pos
    nlinarith
  -- The auxiliary index M is used only to reuse the scalar exponential inequality.
  -- It does not restrict the retained bin set or assert any recursive call.
  have hfine := (B.initial_mean_rate_salary hcharge M M ks ka hhi r hrank hs ht hp).2
  have hentry (x y) := B.residualOmittedPositive_fine_tail_le n hbins hrate M r hC hC1
    ks ka j hcharge hrank hs ht hp hd x y
  have h := B.residualOmittedPositive_clipped_entry_le n hbins hrate hcutoff M j ks ka H
    hks hka r hst hs ht hC hC1 hCf (by positivity) hentry
  have hb : (((HP.k : ℝ) + 1) *
      (2 * B.binCap * rate ka * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack))) / rate ka ≤ D * w := by
    have he : (((HP.k : ℝ) + 1) *
        (2 * B.binCap * rate ka * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack))) / rate ka =
        2 * ((HP.k : ℝ) + 1) * B.binCap * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack) := by
      field_simp [hf.ne']
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hfine
      (by positivity : 0 ≤ 2 * ((HP.k : ℝ) + 1) * B.binCap)
    dsimp only [D]
    nlinarith
  have hw3 : w ^ 3 = t ^ 4 := by
    dsimp only [w, t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcoef : K * D ^ 3 ≤ (1 + K) ^ 4 * D ^ 4 := by
    have hkpow : K ≤ (1 + K) ^ 4 := by nlinarith [sq_nonneg K, sq_nonneg (K ^ 2)]
    have hdpow : D ^ 3 ≤ D ^ 4 := by nlinarith [sq_nonneg D, sq_nonneg (D ^ 2)]
    exact mul_le_mul hkpow hdpow (by positivity) (by positivity)
  apply h.trans
  calc
    _ ≤ 256 * K * (D * w) ^ 3 := by dsimp only [K]; gcongr
    _ = 256 * (K * D ^ 3) * t ^ 4 := by rw [mul_pow, hw3]; ring
    _ ≤ 256 * ((1 + K) ^ 4 * D ^ 4) * t ^ 4 := by gcongr
    _ = _ := by dsimp only [K, D, t]; ring

/-- Actual RAW clipped mean with conditional positive-budget scalar IH.
The omitted positive canonical term is paid separately; the negative ray occurs
once and requires a positive final budget. The right side explicitly retains the
rooted omitted payment, so this is not yet parent-precision allocation. -/
theorem raw_residual_clipped_scalar_omission_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hcover : ∀ z y, B.base z y = 0 ∨ rate n ≤ B.base z y)
    (hkh : ∀ i ∈ B.bins, ∀ v, B.cutoff i v ≠ 0 → B.auxiliary i v = 1)
    (hlight : ∀ i ∈ B.bins, ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (ε : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (hrows : ∀ i ∈ B.bins, 0 < B.binBudget M i r →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history (B.binBudget M i r) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history (B.childBudget M) q = some (child 0 q))
    (hdirect : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row (child i q)))
    (hright : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate (B.childBudget M) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIL : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIR : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤ ε (B.childBudget M) q ^ 4)
    (husage : r.usage = r.terminal) (hnlive : 0 < B.childBudget M)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C)) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
    let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let d := fun i => min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (B.binBudget M i r) (Q i).direct ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
        ε (B.binBudget M i r) (Q i).direct ^ 4)
    let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let p := fun i => min (pc i) (po i)
    let ne := F * ε (B.childBudget M) neg ^ 4
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let omitted := rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|B.residualOmittedPositive M (Nat.log2 M) ka r x y| /
        (rate ka + G x y)))
    ∃ executed, B.raw history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          executed x y - G x y| /
            (rate ka + G x y))) ≤
        (omitted ^ (4⁻¹ : ℝ) + ne ^ (4⁻¹ : ℝ) +
          ∑ i ∈ B.bins, d i ^ (4⁻¹ : ℝ) +
          ∑ i ∈ B.bins, p i ^ (4⁻¹ : ℝ)) ^ 4 ∧
      0 ≤ omitted ^ (4⁻¹ : ℝ) + ne ^ (4⁻¹ : ℝ) +
        ∑ i ∈ B.bins, d i ^ (4⁻¹ : ℝ) + ∑ i ∈ B.bins, p i ^ (4⁻¹ : ℝ) := by
  dsimp only
  let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
  let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let d := fun i => min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (B.binBudget M i r) (Q i).direct ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
        ε (B.binBudget M i r) (Q i).direct ^ 4)
  let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
  let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
  let p := fun i => min (pc i) (po i)
  let ne := F * ε (B.childBudget M) neg ^ 4
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let de := fun i x y => if 0 < B.binBudget M i r then
    (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
      rowSliceMean X Y (fun σ x y =>
        child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y else 0
  let pe := fun i x y => if 0 < B.binBudget M i r then
    B.residualProductMean i r (child i (Q i).left)
    (child i (Q i).right) x y - B.residualProductMean i r
      (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y else 0
  let nege := fun x y => -rowSliceMean X Y (fun σ x y =>
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0)
      (fun q => B.residualCanonicalChild 0 q σ) x y) x y
  have hNu : 0 ≤ (P : ℝ) * r.source.rate :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [hs]; exact (rate_pos ks).le)
  have hiH (i : ℕ) (hi : i ∈ B.bins) : i ≤ H.maxExponent := by
    rw [hbins, mem_range] at hi
    omega
  have hde (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|de i x y| / (rate ka + G x y))) ≤ d i := by
    by_cases hlive : 0 < B.binBudget M i r
    · simp only [de, hlive, ↓reduceIte]
      apply le_min
      · exact B.residualDirect_parent_clipped_le n hbins hrate hcutoff hD H M i
          (depth i (Q i).direct) ks ka (ζ i (Q i).direct) (floor i (Q i).direct) r hst hs ht
          hks hi (hiH i hi) hC hC1 hCf (hkh i hi) hK
          (child i (Q i).direct) (hdirect i hi hlive) (ε (B.binBudget M i r) (Q i).direct) (hID i
            hi hlive)
      · exact B.residualDirect_parent_fine_clipped_le hrate M i (depth i (Q i).direct) ks ka
          (ζ i (Q i).direct) (floor i (Q i).direct) r hst hs ht hC
          (child i (Q i).direct) (hdirect i hi hlive) (ε (B.binBudget M i r) (Q i).direct) (hID i
            hi hlive)
    · simp only [de, hlive, ↓reduceIte, abs_zero, zero_div, min_eq_right (by norm_num : (0 : ℝ) ≤
      1)]
      simp only [rowNormPow, zero_pow (by decide : 4 ≠ 0), sum_const_zero,
        expect_const_zero, mul_zero, abs_zero]
      dsimp only [d, F]
      have hc := B.binCap_nonneg
      have hb : 0 ≤ B.binRate i := by rw [hrate]; exact (rate_pos i).le
      have hm := gridMass_pos (P := P) ka
      have hmi := gridMass_pos (P := P) (max ka i)
      have hf := rate_pos ka
      apply le_min <;> positivity
  have hpe (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|pe i x y| / (rate ka + G x y))) ≤ p i := by
    by_cases hlive : 0 < B.binBudget M i r
    · simp only [pe, hlive, ↓reduceIte]
      apply le_min
      · exact B.residualProduct_active_parent_clipped_le n hbins hrate hcutoff haux hD H M i
          (depth i (Q i).right) ks ka (ζ i (Q i).right) (floor i (Q i).right)
          r hst hs ht (congrFun hrate i)
          hks hka hi (hiH i hi) hC hC1 hCf (hlight i hi)
          (child i (Q i).left) (child i (Q i).right) (hleft i hi hlive) (hright i hi hlive)
          (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
          (hIL i hi hlive) (hIR i hi hlive)
      · apply (rowNormPow_clipped_le_of_ordinary hNu (rate_pos ka) X Y (fun x y =>
        B.residualProductMean i r (child i (Q i).left)
          (child i (Q i).right) x y - B.residualProductMean i r
          (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y) G
          (fun x y => HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)).trans
        dsimp only [po]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact B.residualProduct_active_parent_ordinary_le M i (depth i (Q i).right) ks ka
          (ζ i (Q i).right) (floor i (Q i).right) r hrate hcutoff hCf hst hs ht (congrFun hrate
            i) (hlight i hi)
          (child i (Q i).left) (child i (Q i).right) (hleft i hi hlive) (hright i hi hlive)
          (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
          (hIL i hi hlive) (hIR i hi hlive)
    · simp only [pe, hlive, ↓reduceIte, abs_zero, zero_div, min_eq_right (by norm_num : (0 : ℝ) ≤
      1)]
      simp only [rowNormPow, zero_pow (by decide : 4 ≠ 0), sum_const_zero,
        expect_const_zero, mul_zero, abs_zero]
      dsimp only [p, pc, po, F]
      have hb : 0 ≤ B.binRate i := by rw [hrate]; exact (rate_pos i).le
      have hu : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
      have ht0 : 0 < r.terminal.rate := by rw [ht]; exact rate_pos ka
      have hc := B.binCap_nonneg
      have hq := HP.Q_nonneg HP.toHierarchyParams.atomCap
      have hm := gridMass_pos (P := P) ka
      have hmi := gridMass_pos (P := P) (max ka i)
      have hf := rate_pos ka
      split_ifs <;> apply le_min <;> positivity
  have hne : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|nege x y| / (rate ka + G x y))) ≤ ne := by
    simp only [nege, abs_neg]
    exact B.residualNegative_parent_clipped_le hD H M ks ka r hst hs ht hks hka
      hC hC1 hCf (child 0 neg) hnegative (ε (B.childBudget M) neg) hIN
  let omission := fun x y => -B.residualOmittedPositive M (Nat.log2 M) ka r x y
  let opay := rowNormPow 4 P r.source.rate X Y
    (fun _ x y => min 1 (|omission x y| / (rate ka + G x y)))
  let S₀ : Finset (Option (ℕ ⊕ ℕ)) := insert none
    ((B.bins.image (fun i => some (Sum.inl i))) ∪
      (B.bins.image (fun i => some (Sum.inr i))))
  let S := insert none (S₀.image some)
  let e : Option (Option (ℕ ⊕ ℕ)) → ZMod P → ZMod P → ℝ := fun o =>
    match o with
    | none => omission
    | some none => nege
    | some (some (.inl i)) => de i
    | some (some (.inr i)) => pe i
  let pay : Option (Option (ℕ ⊕ ℕ)) → ℝ := fun o =>
    match o with
    | none => opay
    | some none => ne
    | some (some (.inl i)) => d i
    | some (some (.inr i)) => p i
  have hsum₀ (v : Option (ℕ ⊕ ℕ) → ℝ) : ∑ o ∈ S₀, v o =
      v none + ∑ i ∈ B.bins, v (some (.inl i)) + ∑ i ∈ B.bins, v (some (.inr i)) := by
    have hd : Disjoint (B.bins.image (fun i => some (Sum.inl i)))
        (B.bins.image (fun i => some (Sum.inr i))) := by
      simp only [disjoint_left, mem_image]
      rintro o ⟨i, hi, rfl⟩ ⟨j, hj, he⟩
      cases he
    rw [show S₀ = _ from rfl, sum_insert (by simp), sum_union hd,
      sum_image (fun _ _ _ _ h => by simpa using h),
      sum_image (fun _ _ _ _ h => by simpa using h)]
    ring
  have hsum (v : Option (Option (ℕ ⊕ ℕ)) → ℝ) : ∑ o ∈ S, v o =
      v none + v (some none) + ∑ i ∈ B.bins, v (some (some (.inl i))) +
        ∑ i ∈ B.bins, v (some (some (.inr i))) := by
    rw [show S = _ from rfl, sum_insert (by simp),
      sum_image (fun _ _ _ _ h => Option.some.inj h), hsum₀]
    ring
  have h := rowNormPow_clipped_sum_le_pow_sum S hNu X Y e
    (fun x y => rate ka + G x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka)
      (HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)) pay (by
        intro o ho
        cases o with
        | none => exact le_rfl
        | some a =>
          have ha : a ∈ S₀ := by simpa [S] using ho
          cases a with
          | none => exact hne
          | some a =>
            cases a with
            | inl i => exact hde i (by simpa [S₀] using ha)
            | inr i => exact hpe i (by simpa [S₀] using ha))
  rw [hsum (fun o => pay o ^ (4⁻¹ : ℝ))] at h
  simp only [pay, opay, omission, abs_neg] at h
  simp_rw [hsum (fun o => e o _ _)] at h
  obtain ⟨executed, hex, herr⟩ := B.raw_residual_mean_active_omission
    n hbins hrate hcutoff haux hD H hnH M ks ka r hst hs ht hks hka
    hC hC1 hCf hcover history child hrows hnrow husage hnlive hcalls
  refine ⟨executed, hex, ?_, ?_⟩
  · change rowNormPow 4 P r.source.rate X Y (fun _ x y => min 1
      (|rowSliceMean X Y executed x y - G x y| / (rate ka + G x y))) ≤ _
    change ∀ x y, rowSliceMean X Y executed x y - G x y =
      omission x y + nege x y + ∑ i ∈ B.bins, de i x y + ∑ i ∈ B.bins, pe i x y at herr
    simp_rw [herr]
    exact h
  suffices 0 ≤ opay ^ (4⁻¹ : ℝ) + ne ^ (4⁻¹ : ℝ) +
      ∑ i ∈ B.bins, d i ^ (4⁻¹ : ℝ) + ∑ i ∈ B.bins, p i ^ (4⁻¹ : ℝ) by
    simpa only [opay, omission, abs_neg] using this
  apply add_nonneg
  · apply add_nonneg
    · exact add_nonneg (Real.rpow_nonneg (rowNormPow_nonneg hNu _) _)
        (Real.rpow_nonneg ((rowNormPow_nonneg hNu _).trans hne) _)
    · exact sum_nonneg fun i hi =>
        Real.rpow_nonneg ((rowNormPow_nonneg hNu _).trans (hde i hi)) _
  · exact sum_nonneg fun i hi =>
      Real.rpow_nonneg ((rowNormPow_nonneg hNu _).trans (hpe i hi)) _


/-- Primitive root cost for actual RAW mean assembly, including genuine omission.
It is fixed before the field, horizon, exponents, suffixes and statistical budget. -/
@[expose] def residualRawMeanRootCost (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (cap : ℝ) : ℝ :=
  residualDirectRootCost HP cap + residualProductNegativeRootCost HP cap +
    4 * (1 + max 1 (((HP.k : ℝ) + 1) / HP.θ)) * (1 + 2 * ((HP.k : ℝ) + 1) * cap)

omit [Fact P.Prime] in
/-- A single charge pays actual RAW clipped means uniformly in every later field
and admitted horizon. This is a numerical primitive guard, with no availability claim. -/
theorem exists_residualRawMean_charge (cap : ℝ) :
    ∃ A : ℕ, 1 ≤ A ∧ residualRawMeanRootCost HP cap * (2 : ℝ) ^ (-(A : ℝ)) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (residualRawMeanRootCost HP cap)
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hc : residualRawMeanRootCost HP cap ≤ (2 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
    exact hn.le.trans hpow
  refine ⟨n + 1, by omega, ?_⟩
  apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The actual final clipped RAW mean meets parent precision across active and
exhausted positive bins. Only positive endpoint rows and own-request scalar IH
are required; parent precision derives the once-negative budget guard. -/
theorem raw_residual_clipped_parent_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hcover : ∀ z y, B.base z y = 0 ∨ rate n ≤ B.base z y)
    (hkh : ∀ i ∈ B.bins, ∀ v, B.cutoff i v ≠ 0 → B.auxiliary i v = 1)
    (hlight : ∀ i ∈ B.bins, ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (hrows : ∀ i ∈ B.bins, 0 < B.binBudget M i r →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history (B.binBudget M i r) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history (B.childBudget M) q = some (child 0 q))
    (hdirect : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row (child i q)))
    (hright : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate (B.childBudget M) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget
          M i r) q)) ^ 4)
    (hIL : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget
          M i r) q)) ^ 4)
    (hIR : ∀ i ∈ B.bins, 0 < B.binBudget M i r → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget
          M i r) q)) ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          (B.childBudget M) q)) ^ 4)
    (husage : r.usage = r.terminal) (htask : r.task = .residual 0)
    (hcharge : 1 ≤ B.rankCharge) (hp : 0 < B.requestPrecision M r)
    (hfixed : residualRawMeanRootCost HP B.binCap * (2 : ℝ) ^ (-B.rankCharge) ≤ 1)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C)) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    ∃ executed, B.raw history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          executed x y - G x y| /
            (rate ka + G x y))) ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  dsimp only
  let ε := fun m q => (2 : ℝ) ^ (-B.requestPrecision m q)
  have hrank : 1 ≤ r.task.rank := by rw [htask]; simp only [HierarchyTask.rank]; omega
  have hnlive : 0 < B.childBudget M := by
    rw [← B.raw_negative_budget M r]
    exact B.raw_negative_budget_pos_of_precision hcharge M ks ka r hrank hs ht hp
  have hd : dyadicSlack (Nat.log2 M + 1) (Nat.log2 M) < M := by
    rw [dyadicSlack_last]
    have hm := hnlive
    unfold childBudget LogSpaceEstimation.lastBudget at hm
    omega
  obtain ⟨executed, hex, hmean, hmean0⟩ := B.raw_residual_clipped_scalar_omission_le
    n hbins hrate hcutoff haux hD H hnH M ks ka r hst hs ht hks hka
    hC hC1 hCf hcover hkh hlight hK history child depth ζ floor ε
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN husage hnlive hcalls
  refine ⟨executed, hex, hmean.trans ?_⟩
  have ha : ka ≤ H.maxExponent := hka.trans hks
  have hi (i : ℕ) (hib : i ∈ B.bins) : i ≤ H.maxExponent := by
    rw [hbins, mem_range] at hib
    omega
  have hdirectpay := B.residualDirect_min_sum_salary H M ks ka ha hi r hrate hs ht htask
  have hnegativepay := B.residualNegative_root_salary M ks ka r hs ht htask
  have hproductpay := B.residualProduct_min_sum_salary H M ks ka ha hi r hrate hs ht htask
    hka (by linarith)
  have homission := B.residualOmittedPositive_clipped_uniform_le n hbins hrate hcutoff
    M (Nat.log2 M) ks ka H hks ha r hst hs ht hC hC1 hCf hcharge hrank hp hd
  let D := residualDirectRootCost HP B.binCap
  let PN := residualProductNegativeRootCost HP B.binCap
  let O := 4 * (1 + max 1 (((HP.k : ℝ) + 1) / HP.θ)) *
    (1 + 2 * ((HP.k : ℝ) + 1) * B.binCap)
  have hgeo : 0 < 1 - (2 : ℝ) ^ (-3 / 4 : ℝ) := by
    have hh := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (-3 / 4 : ℝ) < 0)
    linarith
  have hcap := B.binCap_nonneg
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hD0 : 0 ≤ D := by dsimp only [D, residualDirectRootCost]; positivity
  have hPN0 : 0 ≤ PN := by
    dsimp only [PN, residualProductNegativeRootCost, residualProductRootCost]
    positivity
  have hO0 : 0 ≤ O := by dsimp only [O]; positivity
  have hε0 : 0 ≤ ε M r := by dsimp only [ε]; positivity
  have hOroot := Real.rpow_le_rpow
    (rowNormPow_nonneg (mul_nonneg (Nat.cast_nonneg P) (by rw [hs]; exact (rate_pos ks).le)) _)
    homission (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have hroot : ((O * ε M r * (2 : ℝ) ^ (-B.rankCharge)) ^ 4) ^ (4⁻¹ : ℝ) =
      O * ε M r * (2 : ℝ) ^ (-B.rankCharge) := by
    convert Real.pow_rpow_inv_natCast (by positivity :
      0 ≤ O * ε M r * (2 : ℝ) ^ (-B.rankCharge)) (by decide : (4 : ℕ) ≠ 0) using 1
  change _ ≤ ((O * ε M r * (2 : ℝ) ^ (-B.rankCharge)) ^ 4) ^ (4⁻¹ : ℝ) at hOroot
  rw [hroot] at hOroot
  have heD : (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) ≤
      (2 : ℝ) ^ (-B.rankCharge) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) HP.k]
  have hePN : (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) ≤
      (2 : ℝ) ^ (-B.rankCharge) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hdpaid := hdirectpay.trans
    (mul_le_mul_of_nonneg_left heD (mul_nonneg hD0 hε0))
  have hpnpay := add_le_add hnegativepay hproductpay
  have hpnpaid : _ ≤ PN * ε M r * (2 : ℝ) ^ (-B.rankCharge) :=
    hpnpay.trans (by
      have hh := mul_le_mul_of_nonneg_left hePN (mul_nonneg hPN0 hε0)
      dsimp only [PN, residualProductNegativeRootCost, ε] at hh ⊢
      convert hh using 1; ring)
  have hpaid := add_le_add (add_le_add hOroot hdpaid) hpnpaid
  have hfixedpaid := mul_le_mul_of_nonneg_right hfixed hε0
  have htotal : _ ≤ ε M r := hpaid.trans (by
    dsimp only [residualRawMeanRootCost, residualDirectRootCost,
      residualProductNegativeRootCost, D, PN, O, ε] at hfixedpaid ⊢
    convert hfixedpaid using 1 <;> ring)
  have hpower := pow_le_pow_left₀ (b := ε M r) (n := 4) (show (0 : ℝ) ≤ _ from ?_) htotal
  · convert hpower using 1; dsimp only [ε]; ring
  convert hmean0 using 1; dsimp only [ε]; ring

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
