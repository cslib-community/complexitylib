/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyProductTransport
public import Complexity.Foundations.Probability.HierarchyInitialMean

/-!
# Canonical means of executed finite hierarchy products

The bounded polynomial dense recipes and genuine final correction requests identify the
finite reference used by the product root payment with the actual hierarchy residual.
All children use one common environment. The product-right request resets its whole source;
the negative endpoint correction is subtracted once, outside the positive bin sum.

The finite horizon, narrower source, substochastic base, stage bound and finite positive-entry
coverage are explicit. These original composition results do not construct simultaneous
successful recursive calls or allocate the scalar root allowances from the precision schedule.

## Main definitions

* `residualCanonicalChild`: actual bin dense and final correction reference family.
* `residualCanonicalInput`: finite signed assembly with one negative endpoint.

## Main results

* `residualCanonicalInput_mean`: bounded polynomial finite-reference mean.
* `residualCanonicalInput_stage_mean`: identification with the actual request stage residual.
* `finiteInput_residual_mean_payment`: compressed execution and own-request child IH consumer.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- The actual bounded dense and genuine final normalized correction family. -/
@[expose] def residualCanonicalChild (i : ℕ) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  canonicalRequestChild HP B.padding id B.base (B.cutoff i) (B.auxiliary i) HP.ρ HP.K

/-- The finite canonical reference has exactly the same bin/negative assembly as finiteInput.
No recursive execution is asserted by this definition. -/
@[expose] def residualCanonicalInput
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (σ : Environment P 3) (x y : ZMod P) : ℝ :=
  (∑ i ∈ B.bins, HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)
    (fun q => B.residualCanonicalChild i q σ) x y) -
  HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
    r.source (midpoint r) r.terminal (B.binRate 0)
    (fun q => B.residualCanonicalChild 0 q σ) x y

variable (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1))
  (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
  (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
  (s t : Fin 3) (hst : s ≠ t) (ks kt : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t kt st)
  (hks : ks ≤ H.maxExponent) (hts : kt ≤ ks)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
  (hCf : ∀ x y, B.base x y ≤ rate kt)
include hbins hrate hcutoff haux hD hnH hst hs ht hks hts hC hC1 hCf

/-- Actual bounded polynomial finite bins average to the genuine hierarchy residual.
Coverage concerns the base matrix only, never approximate children. The rank rate is the
parent terminal rate; the source can be narrower. All suffixes are preserved until the
existing common-environment mean laws transport them. -/
theorem residualCanonicalInput_mean (x y : ZMod P)
    (hcover : ∀ z, B.base z y = 0 ∨ rate n ≤ B.base z y) :
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (B.residualCanonicalInput r) x y =
    HP.toHierarchyParams.residual (canonicalChannel id (rate kt))
      (canonicalChannel id (rate kt)) (rate kt) B.base x y := by
  let roles : RoleProfile 3 :=
    ⟨s, midpointRole s t, t, (midpointRole_distinct s t).1, hst,
      (midpointRole_distinct s t).2⟩
  have hm : midpoint r = gridChannel roles.midpoint kt [] := by
    simp only [midpoint, hs, ht, gridChannel, roles]
  have hp (i : ℕ) (hi : i ∈ B.bins) (v : ℝ) (hv : B.cutoff i v ≠ 0) :
      B.auxiliary i v = 1 := by
    rw [hcutoff] at hv
    rw [haux]
    exact HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      i (fun _ => 1) hv
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  let E := HP.toHierarchyParams.correctionIter (canonicalChannel id (rate kt))
    (canonicalChannel id (rate kt)) (rate kt) B.base HP.k
  have hpositive (i : ℕ) (hi : i ∈ B.bins) :
      rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ x y => HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
          r.source (midpoint r) r.terminal (B.binRate i)
          (fun q => B.residualCanonicalChild i q σ) x y) x y =
      B.binRate i * B.cutoff i (B.base x y / B.binRate i) +
        ∑ z, E x z * (B.binRate i * B.cutoff i (B.base z y / B.binRate i)) := by
    have hiH : i ≤ H.maxExponent := by rw [hbins, mem_range] at hi; omega
    have hmean := canonical_rawPositiveSample_mean HP B.padding id hD
      Function.injective_id H roles 0 i ks kt kt i hks hts hiH ss [] st B.base
      hC hC1 hCf (B.cutoff i) (B.auxiliary i) HP.ρ HP.K (hp i hi)
      HP.ρ_nonneg HP.ρ_le_one HP.η_pos HP.ρ_one hK x y
    simpa only [rowSliceMean, residualCanonicalChild, hs, ht, hm, hrate, roles, id_eq]
      using hmean
  have hnegative := canonical_rawNegativeSample_mean HP B.padding id hD
    Function.injective_id H roles 0 0 ks kt kt 0 hks hts ss [] st B.base
    hC hC1 hCf (B.cutoff 0) (B.auxiliary 0) HP.ρ HP.K x y
  have hsum (z : ZMod P) :
      ∑ i ∈ B.bins, B.binRate i * B.cutoff i (B.base z y / B.binRate i) = B.base z y := by
    rw [B.initialBins_polynomial_sum n hbins hrate hcutoff hC hC1]
    rcases hcover z with hz | hz
    · rw [hz, zero_mul]
    · rw [polynomialSwitch4_of_ge (by norm_num)
        ((one_le_div (rate_pos n)).mpr hz), mul_one]
  change (𝔼 σ ∈ _, _) = _
  simp only [residualCanonicalInput, expect_sub_distrib, expect_sum_comm]
  change (∑ i ∈ B.bins, rowSliceMean _ _ _ x y) - _ = _
  rw [sum_congr rfl hpositive]
  have hneg : (𝔼 σ ∈ ({σ : Environment P 3 |
      r.source.retains (channels B.padding) σ x ∧
      r.terminal.retains (channels B.padding) σ y} : Finset _),
      HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual r.source
        (midpoint r) r.terminal (B.binRate 0)
        (fun q => B.residualCanonicalChild 0 q σ) x y) = E x y := by
    simpa only [residualCanonicalChild, hs, ht, hm, hrate, roles, id_eq] using hnegative
  rw [hneg, sum_add_distrib, hsum, sum_comm]
  simp_rw [← mul_sum, hsum]
  rw [HierarchyParams.residual_eq, ← HierarchyParams.correctionIter_last]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, E]
  ring

/-- The reference is also the actual request's residual on its transported true stage
channels. This uses the stage law, not equality of samples under changed suffixes. -/
theorem residualCanonicalInput_stage_mean (ha : Admissible r) (x y : ZMod P)
    (hcover : ∀ z, B.base z y = 0 ∨ rate n ≤ B.base z y) :
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (B.residualCanonicalInput r) x y =
    HP.toHierarchyParams.residual (stageSource B.padding id r ha)
      (splitTerminal B.padding id r) r.terminal.rate B.base x y := by
  rw [stage_residual_eq_canonical HP B.padding id r ha hD B.base]
  have hm := B.residualCanonicalInput_mean n hbins hrate hcutoff haux hD H hnH
    r s t hst ks kt ss st hs ht hks hts hC hC1 hCf x y hcover
  simpa only [ht, gridChannel] using hm

/-- Conditional general residual mean payment for literal compressed-history calls.
The true child reference is fixed by the actual recipes, rather than an assumed desired
mean. Each child allowance uses its own source/usage masks. Positive bin budgets and the
separate negative child budget remain unchanged. No independence is required. -/
theorem finiteInput_residual_mean_payment
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ha : Admissible r) (ζ floor : ℝ) (M : ℕ)
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hc : ∀ i ∈ B.bins, ∀ q ∈
      ({(HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).direct,
        (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).left,
        (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).right} : Finset _),
      row (fun m q => if m < M then B.compressedHistory exponent ζ floor m q else none)
        (B.binBudget M i r) q = some (child i q))
    (hnegative : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      row (fun m q => if m < M then B.compressedHistory exponent ζ floor m q else none)
        (B.childBudget M) q = some (child 0 q))
    (hcover : ∀ y z, B.base z y = 0 ∨ rate n ≤ B.base z y)
    {CA CB cap δ : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hδ : 0 ≤ δ)
    (hcap : max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * B.binCap) ≤ cap)
    (hrange : ∀ i q, (i, q) ∈ HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
      r.source (midpoint r) r.terminal B.binRate → ∀ σ x y,
      child i q σ x y ∈ Set.Icc 0 cap)
    (hoff : ∀ i q, (i, q) ∈ HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
      r.source (midpoint r) r.terminal B.binRate → ∀ σ x y,
      ¬ q.usage.retains (channels B.padding) σ y →
      child i q σ x y = 0)
    (hl : ∀ i ∈ B.bins, ∀ σ x z,
      |child i (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i)).left σ x z| ≤ CA)
    (hCBtop : 2 * B.binCap ≤ CB) :
    let scale := (P : ℝ) ^ 2 / (P * r.source.rate) *
      HierarchyTask.residualCostCoefficient (k := HP.k) (V := ZMod P) (channels B.padding)
        B.bins 0 r.source (midpoint r) r.terminal B.binRate CA CB
    (∀ i q, (i, q) ∈ HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
      r.source (midpoint r) r.terminal B.binRate →
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤
      (δ / (1 + scale)) /
        (1 + (4 * cap ^ ((3 : ℝ) / 4)) ^ 4 * (P * q.source.rate)) /
        (1 + #(HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
          r.source (midpoint r) r.terminal B.binRate))) →
    ∃ executed, B.finiteInput
      (fun m q => if m < M then B.compressedHistory exponent ζ floor m q else none)
      M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y) executed x y -
            HP.toHierarchyParams.residual (stageSource B.padding id r ha)
              (splitTerminal B.padding id r) r.terminal.rate B.base x y) ≤ δ := by
  intro scale hroot
  have hspos : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  have hsource : ∀ i q, (i, q) ∈ HierarchyTask.residualErrorCalls (k := HP.k) B.bins 0
      r.source (midpoint r) r.terminal B.binRate → 0 < q.source.rate := by
    intro i q hq
    simp only [HierarchyTask.residualErrorCalls, mem_union, mem_biUnion,
      mem_insert, mem_singleton, Prod.mk.injEq] at hq
    rcases hq with ⟨j, _, hq⟩ | ⟨_, rfl⟩
    · rcases hq with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · simpa only [HierarchyTask.rawRequests] using hspos
      · simpa only [HierarchyTask.rawRequests] using hspos
      · simpa only [HierarchyTask.rawRequests, midpoint, ht, gridChannel] using rate_pos kt
    · exact hspos
  have hcanonical (i : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      (σ : Environment P 3) (x y : ZMod P) :
      B.residualCanonicalChild i q σ x y ∈ Set.Icc 0 cap := by
    have hb := canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
      (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) q σ x y
    exact ⟨hb.1, hb.2.trans hcap⟩
  have hoffCanonical (i : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      (σ : Environment P 3) (x y : ZMod P)
      (hy : ¬ q.usage.retains (channels B.padding) σ y) :
      B.residualCanonicalChild i q σ x y = 0 :=
    canonicalRequestChild_zero_off_usage HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K q σ x y hy
  have hr (i : ℕ) (_hi : i ∈ B.bins) (σ : Environment P 3) (z y : ZMod P) :
      |B.residualCanonicalChild i (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right σ z y| ≤ CB := by
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
    have hb := normalizedRequest_mem_Icc HP B.padding q (B.cutoff i)
      B.binCap_nonneg (B.cutoff_bounds i) (fun _ => B.base)
      (densePreparation B.padding id q (B.auxiliary i) HP.ρ HP.K B.base) σ z y
    change |normalizedRequest B.padding id q (B.cutoff i) HP.ρ HP.K
      (fun _ => B.base) (densePreparation B.padding id q (B.auxiliary i) HP.ρ HP.K B.base)
      σ z y| ≤ CB
    exact ((abs_of_nonneg hb.1).trans_le hb.2).trans hCBtop
  obtain ⟨executed, he, hpay⟩ := B.finiteInput_residual_root_payment
    (fun m q => if m < M then B.compressedHistory exponent ζ floor m q else none)
    M r child B.residualCanonicalChild hc hnegative hCA hCB hspos hδ hsource
    (fun i q hq σ x y => ⟨hrange i q hq σ x y, hcanonical i q σ x y⟩)
    (fun i q hq σ x y hy => ⟨hoff i q hq σ x y hy, hoffCanonical i q σ x y hy⟩)
    hl hr hroot
  refine ⟨executed, he, ?_⟩
  have hmean (x y : ZMod P) := B.residualCanonicalInput_stage_mean n hbins hrate hcutoff haux
    hD H hnH r s t hst ks kt ss st hs ht hks hts hC hC1 hCf ha x y (hcover y)
  have hid : (fun _ x y => rowSliceMean
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun σ x y => executed σ x y - B.residualCanonicalInput r σ x y) x y) =
      (fun (_ : Environment P 3) x y => rowSliceMean
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y) executed x y -
          HP.toHierarchyParams.residual (stageSource B.padding id r ha)
            (splitTerminal B.padding id r) r.terminal.rate B.base x y) := by
    funext σ x y
    simp only [rowSliceMean, expect_sub_distrib] at hmean ⊢
    rw [hmean]
  change rowNormPow 4 P r.source.rate _ _
    (fun _ x y => rowSliceMean _ _
      (fun σ x y => executed σ x y - B.residualCanonicalInput r σ x y) x y) ≤ δ at hpay
  rw [hid] at hpay
  exact hpay

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
