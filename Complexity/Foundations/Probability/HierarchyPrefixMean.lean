/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRawClippedAssembly
import all Complexity.Foundations.Probability.HierarchyInitialMeanUniform

/-!
# Clipped means of actual RAW prefixes at literal slack

Each positive endpoint uses `lastBudget M d B.slack (B.sampleScale r (some i))`;
the once-negative endpoint uses `lastBudget M d B.slack 0`. Rebasing by the
literal scale cutoff recovers the existing final-bin comparisons, with at most
`d / (16 * B.slack)` loss of parent precision. This preserves their direct and
product minima, geometric bin decay, own source/usage masks and rank gaps.

`raw_residual_prefix_clipped_le` bounds the actual clipped conditional mean by
`(C * 2^(-parentPrecision) * 2^(-rankCharge) * 2^(d/(16*slack)))^4`, where
`C = residualRawMeanRootCost HP B.binCap`. Use the existing
`exists_residualRawMean_charge` after fixing HP and the cap, before fields,
horizons, endpoint exponents, suffixes and budgets. Finite positive-entry
coverage, full terminal usage, distinct admitted grid roles and positive parent
precision remain explicit. Availability and scalar IH are conditional only at
positive actual endpoints; intermediate calls concern positive unequal endpoints.

For `d < M`, true omitted mass is the whole `L + E L`, with its existing
width-free payment. For `d ≥ M`, every endpoint is zero and the actual prefix
mean is zero, leaving the entire deficit `-G`. Its clipped integrand is at most
one; substochastic true residual mass gives a width-free moment bound of 256,
paid by the same root allowance. The canonical negative ray is never dropped.

## Main results

* `prefixBudget_precision_loss`: exact maximum-cutoff loss, including exhaustion.
* `residualDirect_prefix_min_sum_salary`: geometric direct prefix allocation.
* `residualProduct_prefix_min_sum_salary`: geometric product prefix allocation.
* `raw_residual_prefix_clipped_le`: actual all-slack RAW prefix consumer.

These original finite bounds have root slope `1/(16*slack) ≤ 1`, suitable for
the existing stationary, final, raw and deterministic-tail schedule weights.
Their joint weighted assembly is not established here. In particular centered
correlated RAW noise receives no rarity discount and remains unproved, as do
completion/progress, later inputs, joint recursive availability, the full
changing-request invariant and native RL=L.
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

omit [Fact P.Prime] in
/-- Actual prefix budget loss, including exhausted endpoints, uses the maximum
of prefix slack and scale cutoff. No positive-budget premise is needed. -/
theorem prefixBudget_precision_loss (M d : ℕ) (h : ℤ) :
    ((M : ℝ) - LogSpaceEstimation.lastBudget M d B.slack h) / (16 * B.slack) ≤
      (max d (LogSpaceEstimation.scaleCutoff B.slack h) : ℝ) / (16 * B.slack) := by
  have hn : M ≤ LogSpaceEstimation.lastBudget M d B.slack h +
      max d (LogSpaceEstimation.scaleCutoff B.slack h) := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hr : (M : ℝ) ≤ LogSpaceEstimation.lastBudget M d B.slack h +
      (max d (LogSpaceEstimation.scaleCutoff B.slack h) : ℝ) := by exact_mod_cast hn
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

omit [Fact P.Prime] in
/-- Rebasing the parent budget by the literal cutoff recovers exactly the
prefix endpoint under the final-bin interface. This includes zero endpoints. -/
theorem binBudget_prefix_rebase (M d i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.binBudget (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some i)) +
      LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some i))) i r =
      LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some i)) := by
  have hc : 1 ≤ LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some i)) := by
    unfold LogSpaceEstimation.scaleCutoff
    have hh := B.slack_pos
    nlinarith [Nat.zero_le (B.sampleScale r (some i)).natAbs]
  change _ - max 1 (LogSpaceEstimation.scaleCutoff B.slack
    (B.sampleScale r (some i))) = _
  rw [max_eq_right hc, Nat.add_sub_cancel]

omit [Fact P.Prime] in
/-- At a fixed actual request, rebasing loses at most `d/(16*slack)` of
precision. Source, terminal and rank terms are retained exactly on both sides. -/
theorem prefix_rebase_accuracy_le (M d : ℕ) (h : ℤ)
    (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    (2 : ℝ) ^ (-B.requestPrecision
      (LogSpaceEstimation.lastBudget M d B.slack h +
        LogSpaceEstimation.scaleCutoff B.slack h) q) ≤
      (2 : ℝ) ^ (-B.requestPrecision M q) *
        (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)) := by
  have hn : M ≤ LogSpaceEstimation.lastBudget M d B.slack h +
      LogSpaceEstimation.scaleCutoff B.slack h + d := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hr : (M : ℝ) ≤
      ((LogSpaceEstimation.lastBudget M d B.slack h +
        LogSpaceEstimation.scaleCutoff B.slack h : ℕ) : ℝ) + d := by exact_mod_cast hn
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  unfold requestPrecision LogSpaceEstimation.precision
  have hh := div_le_div_of_nonneg_right hr (by positivity : (0 : ℝ) ≤ 16 * B.slack)
  rw [add_div] at hh
  linarith

omit [Fact P.Prime] in
/-- The once-negative prefix uses scale zero at every slack. -/
theorem sampleScale_none_eq_zero
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.sampleScale r none = 0 := by
  by_cases ht : r.terminal.rate = 0
  · simp [sampleScale, midpoint, ht]
  · simp only [sampleScale, Option.map_none, Option.getD_none, midpoint, div_self ht,
      Real.logb_one, Int.floor_zero]

/-- The actual RAW prefix mean separates active direct/product errors, the once-negative
error and the genuine omitted positive mean. Rows are required only at positive budgets. -/
theorem raw_residual_prefix_mean_active_omission
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M j ks ka : ℕ) (hj : j < Nat.log2 M + 1) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hcover : ∀ z y, B.base z y = 0 ∨ rate n ≤ B.base z y)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hrows : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0))
        q = some (child 0 q))
    (husage : r.usage = r.terminal) (hnlive : 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j) B.slack 0))
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
    let de := fun i x y => if 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1)
      j) B.slack (B.sampleScale r (some i))) then
      (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
        rowSliceMean X Y (fun σ x y =>
          child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y else 0
    let pe := fun i x y => if 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1)
      j) B.slack (B.sampleScale r (some i))) then
      B.residualProductMean i r (child i (Q i).left)
      (child i (Q i).right) x y - B.residualProductMean i r
        (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y else 0
    let nege := fun x y => -rowSliceMean X Y (fun σ x y =>
      HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
        r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
      HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
        r.source (midpoint r) r.terminal (B.binRate 0)
        (fun q => B.residualCanonicalChild 0 q σ) x y) x y
    let omission := fun x y => -B.residualOmittedPositive M j ka r x y
    ∃ Fgroup : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) .residual r =
          some (Fgroup i)) ∧
      B.raw history M .residual r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), Fgroup i σ x y) ∧ ∀ x y,
      rowSliceMean X Y (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y =
        omission x y + nege x y + ∑ i ∈ B.bins, de i x y + ∑ i ∈ B.bins, pe i x y := by
  dsimp only
  let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let de := fun i x y => if 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
    B.slack (B.sampleScale r (some i))) then
    (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
      rowSliceMean X Y (fun σ x y =>
        child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y else 0
  let pe := fun i x y => if 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
    B.slack (B.sampleScale r (some i))) then
    B.residualProductMean i r (child i (Q i).left)
    (child i (Q i).right) x y - B.residualProductMean i r
      (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y else 0
  let nege := fun x y => -rowSliceMean X Y (fun σ x y =>
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0)
      (fun q => B.residualCanonicalChild 0 q σ) x y) x y
  let omission := fun x y => -B.residualOmittedPositive M j ka r x y
  have hsgrid : r.source = gridChannel r.source.role ks r.source.suffix := by
    change r.source = {r.source with rate := rate ks}
    rw [← hs]
  have htgrid : r.terminal = gridChannel r.terminal.role ka r.terminal.suffix := by
    change r.terminal = {r.terminal with rate := rate ka}
    rw [← ht]
  obtain ⟨Fgroup, hgroups, hraw, hmean⟩ := B.raw_prefix_mean history M .residual r
    r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
    hsgrid (husage.trans htgrid) hcalls j hj
  have href (x y : ZMod P) : rowSliceMean X Y (B.residualCanonicalInput r) x y = G x y :=
    B.residualCanonicalInput_mean n hbins hrate hcutoff haux hD H hnH
      r r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
      hsgrid htgrid hks hka hC hC1 hCf x y (fun z => hcover z y)
  have homit (x y : ZMod P) : rowSliceMean X Y
      (fun σ x y => ∑ i ∈ B.bins,
        if (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i))) = 0 then B.residualCanonicalRay r (some i) σ x y else 0)
      x y = B.residualOmittedPositive M j ka r x y := by
    have hm := B.residualOmittedPositive_mean n hbins hrate hcutoff haux hD H hnH
      M r r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
      hsgrid htgrid hks hka hC hC1 hCf j x y
    exact hm
  have hratio (i : ℕ) (y : ZMod P) : HierarchyTask.usageRatio (channels B.padding)
      r.terminal (Q i).direct y = gridMass P ka / gridMass P (max ka i) := by
    apply usageRatio_grid B.padding r.terminal (Q i).direct ka (max ka i) ht
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hrate, rate_min]
  have hpositive (i : ℕ) (hi : i ∈ B.bins) (x y : ZMod P) :
      rowSliceMean X Y (fun σ x y =>
        (B.sample history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r (some i)))) .residual r (some i)).getD 0 σ x y -
          B.residualCanonicalRay r (some i) σ x y) x y =
        de i x y + pe i x y - rowSliceMean X Y
          (fun σ x y => if (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
            B.slack (B.sampleScale r (some i))) = 0 then
            B.residualCanonicalRay r (some i) σ x y else 0) x y := by
    by_cases hlive : 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i)))
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
    · have hz : (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
      (B.sampleScale r (some i))) = 0 := by omega
      simp only [hz, sample_zero, Option.getD_some, Pi.zero_apply, Matrix.zero_apply,
        zero_sub, de, pe, Nat.lt_irrefl, ↓reduceIte, zero_add, rowSliceMean,
        expect_neg_distrib]
  have hnegative (x y : ZMod P) : rowSliceMean X Y
      (fun σ x y => (B.sample history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M
        + 1) j) B.slack 0)) .residual r none).getD 0 σ x y -
        B.residualCanonicalRay r none σ x y) x y = nege x y := by
    simp only [sample, Nat.ne_of_gt hnlive, ↓reduceIte, hnrow, bind, Option.bind_some,
      pure, Option.getD_some, residualCanonicalRay, HierarchyTask.rawNegativeSample,
      HierarchyTask.rawRequests, nege, Pi.neg_apply,
      rowSliceMean, expect_sub_distrib, expect_neg_distrib]
    simp only [← mul_expect]
    ring
  have herr (x y : ZMod P) : rowSliceMean X Y
      (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y =
      omission x y + nege x y + ∑ i ∈ B.bins, de i x y + ∑ i ∈ B.bins, pe i x y := by
    have hm := hmean x y
    have hm' : rowSliceMean X Y
        (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y =
        rowSliceMean X Y (fun σ x y => ((B.rays .residual).map fun bin =>
          (B.sample history (LogSpaceEstimation.lastBudget M
            (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r bin))
            .residual r bin).getD 0 σ x y).sum) x y := by
      simpa only [rowSliceMean, X, Y, CorrectionRowTask.Channel.retains,
        channels, semanticSide_grid, hs, ht, H4RankEnvironment.X, H4RankEnvironment.Y] using hm
    rw [hm', ← href x y]
    change (𝔼 σ ∈ _, _) - (𝔼 σ ∈ _, _) = _
    rw [← expect_sub_distrib]
    have hp : (fun σ => ((B.rays .residual).map fun bin =>
        (B.sample history (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r bin)) .residual r bin).getD 0 σ x y).sum -
        B.residualCanonicalInput r σ x y) =
        (fun σ => ∑ i ∈ B.bins,
          ((B.sample history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
            B.slack (B.sampleScale r (some i)))) .residual r (some i)).getD 0 σ x y -
            B.residualCanonicalRay r (some i) σ x y) +
          ((B.sample history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
            B.slack 0)) .residual r none).getD 0 σ x y -
            B.residualCanonicalRay r none σ x y)) := by
      funext σ
      rw [← B.residualCanonicalRay_sum r σ x y]
      simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def,
        sum_map_toList, sum_sub_distrib, B.sampleScale_none_eq_zero]
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
  exact ⟨Fgroup, hgroups, hraw, herr⟩



/-- The literal prefix endpoint inherits geometric bin decay, with explicit
root growth for the slack lost before this endpoint. -/
theorem residualDirect_prefix_min_root_salary (H : Horizon P) (M d ks ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let D := max 1 F * max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)
    let ε := (2 : ℝ) ^ (-B.requestPrecision ((LogSpaceEstimation.lastBudget M d B.slack
      (B.sampleScale r (some i)))) q)
    (min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) * ε ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) * ε ^ 4)) ^
      (4⁻¹ : ℝ) ≤
    D ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) *
      (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4) * (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)) := by
  dsimp only
  let m := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some i)) +
    LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some i))
  have hh := B.residualDirect_min_root_salary H m ks ka i ha hi r hrate hs ht hr
  have hb := B.binBudget_prefix_rebase M d i r
  change B.binBudget m i r = _ at hb
  simp only [hb] at hh
  apply hh.trans
  have he := B.prefix_rebase_accuracy_le M d (B.sampleScale r (some i)) r
  have hc := B.binCap_nonneg
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hm : (2 : ℝ) ^ (-B.requestPrecision m r) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)) := he
  have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ (max 1 (512 * (3 * max 1 (((HP.k : ℝ) + 1)
    / HP.θ) + 3) ^ 3) *
      max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) from by positivity)
  have hmul' := mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤
    (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) *
      (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4))
  convert hmul' using 1 <;> ring

/-- The literal prefix endpoint inherits geometric bin decay, with explicit
root growth for the slack lost before this endpoint. -/
theorem residualProduct_prefix_min_root_salary (H : Horizon P) (M d ks ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0)
    (hka : ka ≤ ks) (hcharge : 0 ≤ B.rankCharge) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let ε := fun m q => (2 : ℝ) ^ (-B.requestPrecision m q)
    let pc := (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε ((LogSpaceEstimation.lastBudget M d
          B.slack (B.sampleScale r (some i)))) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε ((LogSpaceEstimation.lastBudget M d B.slack
              (B.sampleScale r (some i)))) (Q i).right ^ 4))
    let po := (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε ((LogSpaceEstimation.lastBudget M d
          B.slack (B.sampleScale r (some i)))) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε ((LogSpaceEstimation.lastBudget M d B.slack
              (B.sampleScale r (some i)))) (Q i).right ^ 4))
    (min pc po) ^ (4⁻¹ : ℝ) ≤
      residualProductRootCost HP B.binCap * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) *
        (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4) * (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)) := by
  dsimp only
  let m := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some i)) +
    LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some i))
  have hh := B.residualProduct_min_root_salary H m ks ka i ha hi r hrate hs ht hr hka hcharge
  have hb := B.binBudget_prefix_rebase M d i r
  change B.binBudget m i r = _ at hb
  simp only [hb] at hh
  apply hh.trans
  have he := B.prefix_rebase_accuracy_le M d (B.sampleScale r (some i)) r
  have hc := B.binCap_nonneg
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hm : (2 : ℝ) ^ (-B.requestPrecision m r) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)) := he
  have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ residualProductRootCost HP B.binCap from by
    dsimp only [residualProductRootCost]; positivity)
  have hmul' := mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤
    (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) *
      (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4))
  convert hmul' using 1 <;> ring

/-- Actual RAW clipped mean with conditional positive-budget scalar IH.
The omitted positive canonical term is paid separately; the negative ray occurs
once and requires a positive prefix budget. The right side explicitly retains the
rooted omitted payment, so this is not yet parent-precision allocation. -/
theorem raw_residual_prefix_clipped_scalar_omission_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M j ks ka : ℕ) (hj : j < Nat.log2 M + 1) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
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
    (hrows : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0))
        q = some (child 0 q))
    (hdirect : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1)
      j) B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) q = some (.row (child i q)))
    (hright : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) q
        = some (.row (child 0 q)))
    (hID : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) q ^ 4)
    (hIL : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) q ^ 4)
    (hIR : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) q ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤ ε ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) q ^ 4)
    (husage : r.usage = r.terminal) (hnlive : 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j) B.slack 0))
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
        ε ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) (Q i).direct ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
        ε ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) (Q i).direct ^ 4)
    let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε ((LogSpaceEstimation.lastBudget M (dyadicSlack
              (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).right ^ 4))
    let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε ((LogSpaceEstimation.lastBudget M (dyadicSlack
              (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).right ^ 4))
    let p := fun i => min (pc i) (po i)
    let ne := F * ε ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
      0)) neg ^ 4
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let omitted := rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|B.residualOmittedPositive M j ka r x y| /
        (rate ka + G x y)))
    ∃ Fgroup : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) .residual r =
          some (Fgroup i)) ∧
      B.raw history M .residual r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), Fgroup i σ x y) ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y| /
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
        ε ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) (Q i).direct ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
        ε ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) (Q i).direct ^ 4)
  let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε ((LogSpaceEstimation.lastBudget M (dyadicSlack
              (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).right ^ 4))
  let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε ((LogSpaceEstimation.lastBudget M
          (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε ((LogSpaceEstimation.lastBudget M (dyadicSlack
              (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).right ^ 4))
  let p := fun i => min (pc i) (po i)
  let ne := F * ε ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0))
    neg ^ 4
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let de := fun i x y => if 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
    B.slack (B.sampleScale r (some i))) then
    (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
      rowSliceMean X Y (fun σ x y =>
        child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y else 0
  let pe := fun i x y => if 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
    B.slack (B.sampleScale r (some i))) then
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
  let bm := fun i => LogSpaceEstimation.lastBudget M
    (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)) +
      LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some i))
  have hbm (i : ℕ) : B.binBudget (bm i) i r =
      LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
        B.slack (B.sampleScale r (some i)) := B.binBudget_prefix_rebase M _ i r
  let nm := LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 +
    B.slack
  have hnm : B.childBudget nm =
      LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 := by
    have hc : 1 ≤ B.slack := B.slack_pos
    simp only [nm, childBudget, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff, Int.natAbs_zero, add_zero, mul_one,
      max_eq_right hc]
    omega
  have hde (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|de i x y| / (rate ka + G x y))) ≤ d i := by
    by_cases hlive : 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i)))
    · simp only [de, hlive, ↓reduceIte]
      apply le_min
      · exact B.residualDirect_parent_clipped_le n hbins hrate hcutoff hD H (bm i) i
          (depth i (Q i).direct) ks ka (ζ i (Q i).direct) (floor i (Q i).direct) r hst hs ht
          hks hi (hiH i hi) hC hC1 hCf (hkh i hi) hK
          (child i (Q i).direct) (by simpa only [hbm] using hdirect i hi hlive) (ε
            ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
              (B.sampleScale r (some i)))) (Q i).direct) (hID i
            hi hlive)
      · exact B.residualDirect_parent_fine_clipped_le hrate (bm i) i (depth i (Q i).direct) ks ka
          (ζ i (Q i).direct) (floor i (Q i).direct) r hst hs ht hC
          (child i (Q i).direct) (by simpa only [hbm] using hdirect i hi hlive) (ε
            ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
              (B.sampleScale r (some i)))) (Q i).direct) (hID i
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
    by_cases hlive : 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i)))
    · simp only [pe, hlive, ↓reduceIte]
      apply le_min
      · exact B.residualProduct_active_parent_clipped_le n hbins hrate hcutoff haux hD H (bm i) i
          (depth i (Q i).right) ks ka (ζ i (Q i).right) (floor i (Q i).right)
          r hst hs ht (congrFun hrate i)
          hks hka hi (hiH i hi) hC hC1 hCf (hlight i hi)
          (child i (Q i).left) (child i (Q i).right) (by simpa only [hbm] using hleft i hi hlive)
            (by simpa only [hbm] using hright i hi hlive)
          (ε ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) (Q i).left) (ε ((LogSpaceEstimation.lastBudget M
              (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).right)
          (hIL i hi hlive) (hIR i hi hlive)
      · apply (rowNormPow_clipped_le_of_ordinary hNu (rate_pos ka) X Y (fun x y =>
        B.residualProductMean i r (child i (Q i).left)
          (child i (Q i).right) x y - B.residualProductMean i r
          (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y) G
          (fun x y => HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)).trans
        dsimp only [po]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact B.residualProduct_active_parent_ordinary_le (bm i) i (depth i (Q i).right) ks ka
          (ζ i (Q i).right) (floor i (Q i).right) r hrate hcutoff hCf hst hs ht (congrFun hrate
            i) (hlight i hi)
          (child i (Q i).left) (child i (Q i).right) (by simpa only [hbm] using hleft i hi hlive)
            (by simpa only [hbm] using hright i hi hlive)
          (ε ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) (Q i).left) (ε ((LogSpaceEstimation.lastBudget M
              (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r (some i)))) (Q i).right)
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
    exact B.residualNegative_parent_clipped_le hD H nm ks ka r hst hs ht hks hka
      hC hC1 hCf (child 0 neg) (by simpa only [hnm] using hnegative) (ε
        ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) neg) hIN
  let omission := fun x y => -B.residualOmittedPositive M j ka r x y
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
  obtain ⟨Fgroup, hgroups, hex, herr⟩ := B.raw_residual_prefix_mean_active_omission
    n hbins hrate hcutoff haux hD H hnH M j ks ka hj r hst hs ht hks hka
    hC hC1 hCf hcover history child hrows hnrow husage hnlive hcalls
  refine ⟨Fgroup, hgroups, hex, ?_, ?_⟩
  · change rowNormPow 4 P r.source.rate X Y (fun _ x y => min 1
      (|rowSliceMean X Y (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y| / (rate
        ka + G x y))) ≤ _
    change ∀ x y, rowSliceMean X Y (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y =
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




/-- Literal prefix minima sum geometrically without a bin-count factor. -/
theorem residualDirect_prefix_min_sum_salary (H : Horizon P) (M d ks ka : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let D := max 1 F * max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)
    let ε := fun i => (2 : ℝ) ^ (-B.requestPrecision ((LogSpaceEstimation.lastBudget M d B.slack
      (B.sampleScale r (some i)))) (Q i))
    (∑ i ∈ B.bins, (min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) * ε i ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) * ε i ^ 4)) ^
      (4⁻¹ : ℝ)) ≤
    (2 / (1 - (2 : ℝ) ^ (-3 / 4 : ℝ))) * D ^ (4⁻¹ : ℝ) *
      (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) * (2 : ℝ) ^ ((d : ℝ) / (16 *
        B.slack)) := by
  dsimp only
  have hh := sum_le_sum fun i hib =>
    B.residualDirect_prefix_min_root_salary H M d ks ka i ha (hi i hib) r hrate hs ht hr
  apply hh.trans
  simp_rw [mul_right_comm _ _ ((2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)))]
  rw [← mul_sum]
  have hc := B.binCap_nonneg
  have hg := mul_le_mul_of_nonneg_left (sum_two_rpow_offset_le B.bins ka)
    (by positivity : 0 ≤
      (max 1 (512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3) *
        max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
          (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) * (2 : ℝ) ^ ((d : ℝ) / (16 *
            B.slack)))
  convert hg using 1 <;> ring



/-- Literal prefix minima sum geometrically without a bin-count factor. -/
theorem residualProduct_prefix_min_sum_salary (H : Horizon P) (M d ks ka : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0)
    (hka : ka ≤ ks) (hcharge : 0 ≤ B.rankCharge) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let ε := fun m q => (2 : ℝ) ^ (-B.requestPrecision m q)
    let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε ((LogSpaceEstimation.lastBudget M d
          B.slack (B.sampleScale r (some i)))) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε ((LogSpaceEstimation.lastBudget M d B.slack
              (B.sampleScale r (some i)))) (Q i).right ^ 4))
    let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε ((LogSpaceEstimation.lastBudget M d
          B.slack (B.sampleScale r (some i)))) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε ((LogSpaceEstimation.lastBudget M d B.slack
              (B.sampleScale r (some i)))) (Q i).right ^ 4))
    (∑ i ∈ B.bins, (min (pc i) (po i)) ^ (4⁻¹ : ℝ)) ≤
      (2 / (1 - (2 : ℝ) ^ (-3 / 4 : ℝ))) * residualProductRootCost HP B.binCap *
        (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) * (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)) := by
  dsimp only
  apply (sum_le_sum fun i hib =>
    B.residualProduct_prefix_min_root_salary H M d ks ka i ha (hi i hib) r hrate hs ht hr
      hka hcharge).trans
  simp_rw [mul_right_comm _ _ ((2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)))]
  rw [← mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_two_rpow_offset_le B.bins ka)
    (by have := B.binCap_nonneg
        have hcost : 0 ≤ residualProductRootCost HP B.binCap := by
          dsimp only [residualProductRootCost]
          have := HP.Q_nonneg HP.toHierarchyParams.atomCap
          positivity
        positivity : 0 ≤ residualProductRootCost HP B.binCap *
          (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) * (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)))
  convert hh using 1 <;> ring


omit [Fact P.Prime] in
/-- The once-negative prefix payment uses its literal zero-scale budget. -/
theorem residualNegative_prefix_root_salary (M d ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hr : r.task = .residual 0) :
    let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    (F * ((2 : ℝ) ^ (-B.requestPrecision ((LogSpaceEstimation.lastBudget M d B.slack 0)) neg)) ^
      4) ^ (4⁻¹ : ℝ) ≤
      F ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) * (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack)) := by
  dsimp only
  let m := LogSpaceEstimation.lastBudget M d B.slack 0 + B.slack
  have hc : 1 ≤ B.slack := B.slack_pos
  have hb : B.childBudget m = LogSpaceEstimation.lastBudget M d B.slack 0 := by
    simp only [m, childBudget, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff, Int.natAbs_zero, add_zero, mul_one, max_eq_right hc]
    omega
  have hh := B.residualNegative_root_salary m ks ka r hs ht hr
  simp only [hb] at hh
  apply hh.trans
  have he := B.prefix_rebase_accuracy_le M d 0 r
  simp only [LogSpaceEstimation.scaleCutoff, Int.natAbs_zero, add_zero, mul_one] at he
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤
    (512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3) ^ (4⁻¹ : ℝ) from by
      positivity)
  have hmul' := mul_le_mul_of_nonneg_right hmul (by positivity :
    0 ≤ (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge))
  convert hmul' using 1; ring

/-- The small-slack clipped RAW prefix mean retains paid structural root growth.
Only positive endpoint rows and own-request scalar IH are required. Positive
parent precision and `d < M` derive the once-negative prefix budget guard. -/
theorem raw_residual_prefix_clipped_salary_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M j ks ka : ℕ) (hj : j < Nat.log2 M + 1)
    (hd : dyadicSlack (Nat.log2 M + 1) j < M) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
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
    (hrows : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0))
        q = some (child 0 q))
    (hdirect : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1)
      j) B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) q = some (.row (child i q)))
    (hright : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) q
        = some (.row (child 0 q)))
    (hID : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIL : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIR : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) q)) ^ 4)
    (husage : r.usage = r.terminal) (htask : r.task = .residual 0)
    (hcharge : 1 ≤ B.rankCharge) (hp : 0 < B.requestPrecision M r)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C)) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    ∃ Fgroup : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) .residual r =
          some (Fgroup i)) ∧
      B.raw history M .residual r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), Fgroup i σ x y) ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y| /
            (rate ka + G x y))) ≤
        (residualRawMeanRootCost HP B.binCap *
          (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
          (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack))) ^ 4 := by
  dsimp only
  let ε := fun m q => (2 : ℝ) ^ (-B.requestPrecision m q)
  have hrank : 1 ≤ r.task.rank := by rw [htask]; simp only [HierarchyTask.rank]; omega
  have hnlive : 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 := by
    have hn := B.raw_negative_budget_pos_of_precision hcharge M ks ka r hrank hs ht hp
    rw [B.raw_negative_budget] at hn
    unfold childBudget at hn
    unfold LogSpaceEstimation.lastBudget LogSpaceEstimation.scaleCutoff at hn ⊢
    norm_num only [Int.natAbs_zero, Nat.add_zero, Nat.mul_one] at hn ⊢
    omega
  obtain ⟨Fgroup, hgroups, hex, hmean, hmean0⟩ := B.raw_residual_prefix_clipped_scalar_omission_le
    n hbins hrate hcutoff haux hD H hnH M j ks ka hj r hst hs ht hks hka
    hC hC1 hCf hcover hkh hlight hK history child depth ζ floor ε
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN husage hnlive hcalls
  refine ⟨Fgroup, hgroups, hex, hmean.trans ?_⟩
  have ha : ka ≤ H.maxExponent := hka.trans hks
  have hi (i : ℕ) (hib : i ∈ B.bins) : i ≤ H.maxExponent := by
    rw [hbins, mem_range] at hib
    omega
  have hdirectpay := B.residualDirect_prefix_min_sum_salary H M (dyadicSlack (Nat.log2 M + 1) j)
    ks ka ha hi r hrate hs ht htask
  have hnegativepay := B.residualNegative_prefix_root_salary M (dyadicSlack (Nat.log2 M + 1) j)
    ks ka r hs ht htask
  have hproductpay := B.residualProduct_prefix_min_sum_salary H M (dyadicSlack (Nat.log2 M + 1)
    j) ks ka ha hi r hrate hs ht htask
    hka (by linarith)
  have homission := B.residualOmittedPositive_clipped_uniform_le n hbins hrate hcutoff
    M j ks ka H hks ha r hst hs ht hC hC1 hCf hcharge hrank hp hd
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
  let growth := (2 : ℝ) ^
    ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack))
  have hgrowth : 1 ≤ growth := Real.one_le_rpow (by norm_num)
    (div_nonneg (Nat.cast_nonneg _) (by positivity))
  have hdpaid := hdirectpay.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left heD (mul_nonneg hD0 hε0))
      (by positivity : 0 ≤ growth))
  have hpnpay := add_le_add hnegativepay hproductpay
  have hpnpaid : _ ≤ PN * ε M r * (2 : ℝ) ^ (-B.rankCharge) * growth :=
    hpnpay.trans (by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hePN (mul_nonneg hPN0 hε0))
        (by positivity : 0 ≤ growth)
      dsimp only [PN, residualProductNegativeRootCost, ε] at hh ⊢
      convert hh using 1; ring)
  have hopaid := hOroot.trans (le_mul_of_one_le_right (by positivity) hgrowth)
  have hpaid := add_le_add (add_le_add hopaid hdpaid) hpnpaid
  have htotal : _ ≤ residualRawMeanRootCost HP B.binCap * ε M r *
      (2 : ℝ) ^ (-B.rankCharge) * growth := hpaid.trans_eq (by
    dsimp only [residualRawMeanRootCost, residualDirectRootCost, D, PN, O, ε, growth]
    ring)
  have hpower := pow_le_pow_left₀ (n := 4) (show (0 : ℝ) ≤ _ from ?_) htotal
  · convert hpower using 1; dsimp only [ε, growth]; ring
  convert hmean0 using 1; dsimp only [ε]; ring


/-- At or beyond the parent budget every literal prefix endpoint is zero.
The actual prefix mean is zero; its deficit is the entire negative target,
including the canonical negative ray. No child row or zero-budget IH is used. -/
theorem raw_prefix_mean_zero_of_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays t,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f t r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c t r bin = some C))
    (j : ℕ) (hj : j < Nat.log2 M + 1)
    (hd : M ≤ dyadicSlack (Nat.log2 M + 1) j) :
    ∃ F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) t r = some (F i)) ∧
      B.raw history M t r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), F i σ x y) ∧
      ∀ x y, rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y u (side P ku) (CopyPadding.identifier B.padding su))
        (fun σ x y => ∑ i ∈ range (j + 1), F i σ x y) x y = 0 := by
  obtain ⟨F, hg, hr, hm⟩ := B.raw_prefix_mean history M t r s u hsu ks ku ss su
    hs hu hcalls j hj
  refine ⟨F, hg, hr, ?_⟩
  intro x y
  rw [hm]
  have hz (bin : Option ℕ) : LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  simp [hz, B.sample_zero, rowSliceMean]

/-- Width-free large-prefix payment for the whole genuine residual.
The clipped integrand is at most one and its fourth power is bounded by `G/f`.
True substochastic residual row mass, rather than field cardinality, integrates it. -/
theorem residual_zero_clipped_le
    (H : Horizon P) (ks ka : ℕ) (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|-G x y| / (rate ka + G x y))) ≤ 256 := by
  dsimp only
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
    (canonicalChannel id (rate ka)) (rate ka) B.base
  have hG (x y) : 0 ≤ G x y := HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y
  have hG1 : G *ᵥ 1 ≤ 1 := by
    intro x
    simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using
      HP.toHierarchyParams.residual_sum_le_one (canonicalChannel id (rate ka))
        (canonicalChannel id (rate ka)) (rate_pos ka) hC1 x
  let B' : BudgetData HP P := { B with base := G }
  let roles : RoleProfile 3 :=
    ⟨r.source.role, midpointRole r.source.role r.terminal.role, r.terminal.role,
      (midpointRole_distinct _ _).1, hst, (midpointRole_distinct _ _).2⟩
  have hh := B'.grid_trueMass_le roles ks ka r.source.suffix r.terminal.suffix H
    hks hka hG1 (fun x y => min 1 (|-G x y| / (rate ka + G x y)))
    (c := 1 / rate ka) (by exact div_nonneg (by norm_num) (rate_pos ka).le) ?_
  · have he : 256 * rate ka * (1 / rate ka) = 256 := by field_simp [(rate_pos ka).ne']
    rw [he] at hh
    dsimp only [B', roles] at hh
    unfold Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments.retainedMask at hh
    simp only [CorrectionRowTask.Channel.retains, channels, semanticSide_grid, hs, ht, G]
      at hh ⊢
    convert hh using 1
    simp [rowNormPow]
  intro x y
  have hf := rate_pos ka
  have hz : 0 ≤ min 1 (|-G x y| / (rate ka + G x y)) := le_min (by norm_num) (div_nonneg
    (abs_nonneg _)
    (add_nonneg hf.le (hG x y)))
  have hz1 : min 1 (|-G x y| / (rate ka + G x y)) ≤ 1 := min_le_left _ _
  have hzG : min 1 (|-G x y| / (rate ka + G x y)) ≤ G x y / rate ka := by
    apply (min_le_right _ _).trans
    rw [abs_neg, abs_of_nonneg (hG x y)]
    exact div_le_div_of_nonneg_left (hG x y) hf (le_add_of_nonneg_right (hG x y))
  rw [abs_of_nonneg hz]
  calc
    _ ≤ min 1 (|-G x y| / (rate ka + G x y)) := pow_le_of_le_one hz hz1 (by decide)
    _ ≤ _ := by dsimp only [B']; simpa only [div_eq_mul_inv, mul_comm, one_mul] using hzG

/-- Actual clipped RAW prefix means at every slack, including fully exhausted
prefixes. Negative rows and own-request accuracy are conditional on their literal
positive budget. One primitive cost is uniform before fields and horizons. -/
theorem raw_residual_prefix_clipped_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M j ks ka : ℕ) (hj : j < Nat.log2 M + 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
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
    (hrows : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) q = some (child i q))
    (hnrow : 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0))
        q = some (child 0 q))
    (hdirect : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1)
      j) B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) q = some (.row (child i q)))
    (hright : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) q
        = some (.row (child 0 q)))
    (hID : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIL : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIR : ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIN : 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) q)) ^ 4)
    (husage : r.usage = r.terminal) (htask : r.task = .residual 0)
    (hcharge : 1 ≤ B.rankCharge) (hp : 0 < B.requestPrecision M r)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C)) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    ∃ Fgroup : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) .residual r =
          some (Fgroup i)) ∧
      B.raw history M .residual r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), Fgroup i σ x y) ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun σ x y => ∑ i ∈ range (j + 1), Fgroup i σ x y) x y - G x y| /
            (rate ka + G x y))) ≤
        (residualRawMeanRootCost HP B.binCap *
          (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
          (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack))) ^ 4 := by
  by_cases hd : dyadicSlack (Nat.log2 M + 1) j < M
  · have hrank : 1 ≤ r.task.rank := by rw [htask]; simp only [HierarchyTask.rank]; omega
    have hn := B.raw_negative_budget_pos_of_precision hcharge M ks ka r hrank hs ht hp
    rw [B.raw_negative_budget] at hn
    have hnlive : 0 < LogSpaceEstimation.lastBudget M
        (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 := by
      unfold childBudget at hn
      unfold LogSpaceEstimation.lastBudget LogSpaceEstimation.scaleCutoff at hn ⊢
      norm_num only [Int.natAbs_zero, Nat.add_zero, Nat.mul_one] at hn ⊢
      omega
    exact B.raw_residual_prefix_clipped_salary_le n hbins hrate hcutoff haux hD H hnH
      M j ks ka hj hd r hst hs ht hks hka hC hC1 hCf hcover hkh hlight hK
      history child depth ζ floor hrows (hnrow hnlive) hdirect hleft hright
      (hnegative hnlive) hID hIL hIR (hIN hnlive) husage htask hcharge hp hcalls
  have hd' : M ≤ dyadicSlack (Nat.log2 M + 1) j := by omega
  dsimp only
  have hsgrid : r.source = gridChannel r.source.role ks r.source.suffix := by
    change r.source = {r.source with rate := rate ks}
    rw [← hs]
  have htgrid : r.terminal = gridChannel r.terminal.role ka r.terminal.suffix := by
    change r.terminal = {r.terminal with rate := rate ka}
    rw [← ht]
  obtain ⟨F, hg, hr, hm⟩ := B.raw_prefix_mean_zero_of_le history M .residual r
    r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
    hsgrid (husage.trans htgrid) hcalls j hj hd'
  have hm' (x y : ZMod P) : rowSliceMean
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun σ x y => ∑ i ∈ range (j + 1), F i σ x y) x y = 0 := by
    simpa only [rowSliceMean, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
      hs, ht, H4RankEnvironment.X, H4RankEnvironment.Y] using hm x y
  refine ⟨F, hg, hr, ?_⟩
  simp_rw [hm', zero_sub]
  apply (B.residual_zero_clipped_le H ks ka hks (hka.trans hks) r hst hs ht hC hC1).trans
  have hgeo : 0 < 1 - (2 : ℝ) ^ (-3 / 4 : ℝ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hcap := B.binCap_nonneg
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hD : 0 ≤ residualDirectRootCost HP B.binCap := by
    dsimp only [residualDirectRootCost]; positivity
  have hPN : 0 ≤ residualProductNegativeRootCost HP B.binCap := by
    dsimp only [residualProductNegativeRootCost, residualProductRootCost]; positivity
  have hO : 4 ≤ 4 * (1 + max 1 (((HP.k : ℝ) + 1) / HP.θ)) *
      (1 + 2 * ((HP.k : ℝ) + 1) * B.binCap) := by
    have hK := le_max_left (1 : ℝ) (((HP.k : ℝ) + 1) / HP.θ)
    have hmul : 0 ≤ 2 * ((HP.k : ℝ) + 1) * B.binCap := by positivity
    nlinarith
  have hcost : 4 ≤ residualRawMeanRootCost HP B.binCap := by
    dsimp only [residualRawMeanRootCost]
    linarith
  have hgrowth : 1 ≤ (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge) *
      (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.one_le_rpow (by norm_num)
    rw [B.requestPrecision_grid M ks ka r hs ht]
    have hrank : (1 : ℝ) ≤ r.task.rank := by
      have hn : 1 ≤ r.task.rank := by rw [htask]; simp only [HierarchyTask.rank]; omega
      exact_mod_cast hn
    have hmd : (M : ℝ) ≤ dyadicSlack (Nat.log2 M + 1) j := by exact_mod_cast hd'
    have hdiv := div_le_div_of_nonneg_right hmd
      (by positivity : (0 : ℝ) ≤ 16 * B.slack)
    nlinarith [Nat.cast_nonneg (α := ℝ) ks, Nat.cast_nonneg (α := ℝ) ka]
  have hroot : 4 ≤ residualRawMeanRootCost HP B.binCap *
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
      (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack)) := by
    have hh := mul_le_mul hcost hgrowth (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    convert hh using 1 <;> ring
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hroot 4
  norm_num only [show (4 : ℝ) ^ 4 = 256 by norm_num] at hh
  exact hh

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
