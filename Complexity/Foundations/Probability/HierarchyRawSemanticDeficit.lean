/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyDyadicRawMean
public import Complexity.Foundations.Probability.HierarchyProductMean
public import Complexity.Foundations.Probability.HierarchyInitialMeanPayment
public import Complexity.Foundations.Probability.HierarchyResidualDomination
public import Complexity.Foundations.Probability.HierarchyInitialFeasibility
public import Complexity.Foundations.Probability.HierarchyInitialMeanUniform
public import Complexity.Foundations.Probability.HierarchyActiveBins

/-!
# Genuine reference rays and omitted positive mass of RAW prefixes

The reference rays below are the actual dense/correction recipes. Finite positive-entry
coverage removes their target gap against the genuine signed residual. Exhausted rays
still contribute their entire negative reference; no zero-budget child accuracy is used.
The deterministic omitted positive mass includes both the direct input and its product
with the true final correction. Its cap and residual domination do not require recursive
availability or an assumption about approximate-child support.

These are original semantic identities and deterministic bounds. They do not allocate
the prefix mean salary, supply joint recursive calls, or bound centered RAW noise.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Actual positive recipes and the once-negative final correction recipe. -/
@[expose] def residualCanonicalRay
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ
  | some i => fun σ => HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)
      (fun q => B.residualCanonicalChild i q σ)
  | none => fun σ => -HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0)
      (fun q => B.residualCanonicalChild 0 q σ)

/-- The negative recipe occurs once outside the finite positive-bin sum. -/
theorem residualCanonicalRay_sum
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (σ : Environment P 3) (x y : ZMod P) :
    ((B.rays .residual).map fun bin => B.residualCanonicalRay r bin σ x y).sum =
      B.residualCanonicalInput r σ x y := by
  simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def,
    residualCanonicalRay, Pi.neg_apply, residualCanonicalInput,
    ← sub_eq_add_neg]
  rw [sum_map_toList]

omit [Fact P.Prime] in
/-- Positive precision and a unit structural charge force the final negative budget
positive. This uses the actual grid precision; it says nothing about fine positive bins. -/
theorem raw_negative_budget_pos_of_precision
    (hcharge : 1 ≤ B.rankCharge) (M ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrank : 1 ≤ r.task.rank) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hp : 0 < B.requestPrecision M r) :
    0 < LogSpaceEstimation.lastBudget M 1 B.slack (B.sampleScale r none) := by
  rw [B.raw_negative_budget]
  have hslack : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
  have hrankR : (1 : ℝ) ≤ r.task.rank := by exact_mod_cast hrank
  have hchargeR : 1 ≤ B.rankCharge * r.task.rank := by nlinarith
  rw [B.requestPrecision_grid M ks ka r hs ht] at hp
  have hm : (16 * B.slack : ℝ) < M := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).mp
      (show (1 : ℝ) < (M : ℝ) / (16 * B.slack) by
        nlinarith [Nat.cast_nonneg (α := ℝ) ks, Nat.cast_nonneg (α := ℝ) ka])
    simpa only [one_mul] using h
  have hmN : 16 * B.slack < M := by exact_mod_cast hm
  unfold childBudget LogSpaceEstimation.lastBudget LogSpaceEstimation.scaleCutoff
  norm_num only [Int.natAbs_zero, Nat.add_zero, Nat.mul_one]
  have hc := B.slack_pos
  omega

/-- Strictly coarse canonical direct tables vanish, just as the reset-right tables do.
The approximate direct table retains its own error and is not constrained here. -/
theorem residualCanonicalDirect_zero_of_lt
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (i ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hCf : ∀ x y, B.base x y ≤ rate ka) (hia : i < ka)
    (σ : Environment P 3) (x y : ZMod P) :
    B.residualCanonicalChild i
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i)).direct σ x y = 0 := by
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)).direct
  have hz : B.cutoff i (B.base x y / q.terminal.rate) = 0 := by
    apply B.residual_cutoff_zero_of_le_half hcutoff hrate
    have hh : rate ka ≤ rate (i + 1) := rate_antitone hia
    have hp := rate_pos (i + 1)
    have he := rate_succ_sixteen i
    linarith [hCf x y]
  change normalizedRequest B.padding id q (B.cutoff i) HP.ρ HP.K
    (fun _ => B.base) (densePreparation B.padding id q (B.auxiliary i) HP.ρ HP.K B.base)
    σ x y = 0
  by_cases ha : Admissible q
  · rw [normalizedRequest_formula B.padding id q ha]
    split_ifs <;> simp [hz]
  · simp [normalizedRequest, ha]

variable (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1))
  (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
  (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
  (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
  (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
  (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
  (hCf : ∀ x y, B.base x y ≤ rate ka)

include hbins hrate hcutoff haux hD hnH hst hs ht hks hka hC hC1 hCf

omit hbins hnH in
/-- One genuine positive ray has its actual direct-plus-product mean, independently
of whether the RAW schedule retains that ray. -/
theorem residualCanonicalRay_positive_mean (i : ℕ) (hi : i ≤ H.maxExponent)
    (x y : ZMod P) :
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (B.residualCanonicalRay r (some i)) x y =
      B.binRate i * B.cutoff i (B.base x y / B.binRate i) +
        ∑ z, HP.toHierarchyParams.correctionIter (canonicalChannel id (rate ka))
          (canonicalChannel id (rate ka)) (rate ka) B.base HP.k x z *
            (B.binRate i * B.cutoff i (B.base z y / B.binRate i)) := by
  let roles : RoleProfile 3 :=
    ⟨s, midpointRole s t, t, (midpointRole_distinct s t).1, hst,
      (midpointRole_distinct s t).2⟩
  have hm : midpoint r = gridChannel roles.midpoint ka [] := by
    simp only [midpoint, hs, ht, gridChannel, roles]
  have hp (v : ℝ) (hv : B.cutoff i v ≠ 0) : B.auxiliary i v = 1 := by
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
  have hmean := canonical_rawPositiveSample_mean HP B.padding id hD
    Function.injective_id H roles 0 i ks ka ka i hks hka hi ss [] st B.base
    hC hC1 hCf (B.cutoff i) (B.auxiliary i) HP.ρ HP.K hp
    HP.ρ_nonneg HP.ρ_le_one HP.η_pos HP.ρ_one hK x y
  simpa only [rowSliceMean, residualCanonicalRay, residualCanonicalChild,
    hs, ht, hm, hrate, roles, id_eq] using hmean

/-- Literal RAW prefix deficit against the genuine residual. Coverage is a finite
base-matrix condition and is discharged through the actual canonical mean theorem.
Only positive unequal endpoint samples require availability. This is an exact identity,
not a payment of either the active errors or the exhausted canonical rays. -/
theorem raw_prefix_residual_signed_deficit
    (husage : r.usage = r.terminal)
    (hcover : ∀ z y, B.base z y = 0 ∨ rate n ≤ B.base z y)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C))
    (j : ℕ) (hj : j < Nat.log2 M + 1) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    ∃ F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
      (∀ i < Nat.log2 M + 1,
        B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) .residual r =
          some (F i)) ∧
      B.raw history M .residual r = some (fun σ x y =>
        ∑ i ∈ range (Nat.log2 M + 1), F i σ x y) ∧
      ∀ x y, rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y t (side P ka) (CopyPadding.identifier B.padding st))
        (fun σ x y => ∑ i ∈ range (j + 1), F i σ x y) x y - G x y =
      rowSliceMean
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y t (side P ka) (CopyPadding.identifier B.padding st))
        (fun σ x y => ((B.rays .residual).map fun bin =>
          if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
              B.slack (B.sampleScale r bin) = 0 then -B.residualCanonicalRay r bin σ x y
          else (B.sample history (LogSpaceEstimation.lastBudget M
            (dyadicSlack (Nat.log2 M + 1) j) B.slack (B.sampleScale r bin))
              .residual r bin).getD 0 σ x y - B.residualCanonicalRay r bin σ x y).sum)
        x y := by
  dsimp only
  obtain ⟨F, hF, hraw, hm⟩ := B.raw_prefix_signed_deficit history M .residual r
    s t hst ks ka ss st hs (husage.trans ht) hcalls j hj (B.residualCanonicalRay r)
    (HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base)
  refine ⟨F, hF, hraw, fun x y => ?_⟩
  have hmean := B.residualCanonicalInput_mean n hbins hrate hcutoff haux hD H hnH
    r s t hst ks ka ss st hs ht hks hka hC hC1 hCf x y (fun z => hcover z y)
  have hcanonical : rowSliceMean
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ka) (CopyPadding.identifier B.padding st))
      (fun σ x y => ((B.rays .residual).map fun bin =>
        B.residualCanonicalRay r bin σ x y).sum) x y =
      HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
        (canonicalChannel id (rate ka)) (rate ka) B.base x y := by
    simp_rw [B.residualCanonicalRay_sum]
    simpa only [rowSliceMean, hs, ht, gridChannel, CorrectionRowTask.Channel.retains,
      channels, semanticSide_grid, H4RankEnvironment.X, H4RankEnvironment.Y] using hmean
  simpa only [hcanonical, sub_self, add_zero] using hm x y

/-- The omitted positive semantic input includes the product with the true correction,
not merely the omitted direct bins. This also covers a wholly exhausted prefix. -/
@[expose] def residualOmittedPositive (M j ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (x y : ZMod P) : ℝ :=
  B.initialFineLoss M (Nat.log2 M + 1) j r x y +
    ∑ z, HP.toHierarchyParams.correctionIter (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base HP.k x z *
        B.initialFineLoss M (Nat.log2 M + 1) j r z y

/-- The deterministic omission is exactly the conditional mean of the actual omitted
positive canonical rays. No agreement hypothesis for an approximate child is present. -/
theorem residualOmittedPositive_mean (j : ℕ) (x y : ZMod P) :
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun σ x y => ∑ i ∈ B.bins,
        if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
            B.slack (B.sampleScale r (some i)) = 0 then
          B.residualCanonicalRay r (some i) σ x y else 0) x y =
      B.residualOmittedPositive M j ka r x y := by
  change (𝔼 σ ∈ _, ∑ i ∈ B.bins, _) = _
  rw [expect_sum_comm]
  have hmean (i : ℕ) (hi : i ∈ B.bins) :=
    B.residualCanonicalRay_positive_mean hrate hcutoff haux hD H r s t hst
      ks ka ss st hs ht hks hka hC hC1 hCf i
      (by rw [hbins, mem_range] at hi; omega) x y
  have he (i : ℕ) (hi : i ∈ B.bins) :
      (𝔼 σ ∈ ({σ : Environment P 3 | r.source.retains (channels B.padding) σ x ∧
          r.terminal.retains (channels B.padding) σ y} : Finset _),
        if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
            B.slack (B.sampleScale r (some i)) = 0 then
          B.residualCanonicalRay r (some i) σ x y else 0) =
      if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r (some i)) = 0 then
        B.binRate i * B.cutoff i (B.base x y / B.binRate i) +
          ∑ z, HP.toHierarchyParams.correctionIter (canonicalChannel id (rate ka))
            (canonicalChannel id (rate ka)) (rate ka) B.base HP.k x z *
              (B.binRate i * B.cutoff i (B.base z y / B.binRate i)) else 0 := by
    split_ifs
    · exact hmean i hi
    · simp only [expect_const_zero]
  rw [sum_congr rfl he]
  unfold residualOmittedPositive initialFineLoss
  have hsplit (i : ℕ) :
      (if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r (some i)) = 0 then
        B.binRate i * B.cutoff i (B.base x y / B.binRate i) +
          ∑ z, HP.toHierarchyParams.correctionIter (canonicalChannel id (rate ka))
            (canonicalChannel id (rate ka)) (rate ka) B.base HP.k x z *
              (B.binRate i * B.cutoff i (B.base z y / B.binRate i)) else 0) =
      (if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r (some i)) = 0 then
        B.binRate i * B.cutoff i (B.base x y / B.binRate i) else 0) +
        ∑ z, HP.toHierarchyParams.correctionIter (canonicalChannel id (rate ka))
          (canonicalChannel id (rate ka)) (rate ka) B.base HP.k x z *
            (if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
                B.slack (B.sampleScale r (some i)) = 0 then
              B.binRate i * B.cutoff i (B.base z y / B.binRate i) else 0) := by
    split_ifs <;> simp
  simp_rw [hsplit]
  rw [sum_add_distrib, sum_comm]
  simp_rw [← mul_sum]
  rfl

omit hbins hrate hcutoff haux hD hnH hst hs ht hks hka hCf in
/-- Actual schedule/cutoff cap and true correction row mass bound the whole omitted
positive input. No child tables, support assumptions or recursive calls occur here. -/
theorem residualOmittedPositive_le_charge (ka j : ℕ) (x y : ZMod P)
    (hrate0 : ∀ i, 0 ≤ B.binRate i) :
    B.residualOmittedPositive M j ka r x y ≤
      ((HP.k : ℝ) + 1) * B.initialInactiveCharge M j r := by
  have hseq := HP.toHierarchyParams.isCorrectionSeq_correctionIter
    (X := canonicalChannel id (rate ka)) (Y := canonicalChannel id (rate ka))
    (rate_pos ka) hC
  have hbound (z : ZMod P) := B.initialFineLoss_le_charge M j r hrate0 z y
  have hcharge : 0 ≤ B.initialInactiveCharge M j r := by
    unfold initialInactiveCharge
    apply mul_nonneg B.binCap_nonneg
    apply sum_nonneg
    intro i _
    split_ifs
    · exact hrate0 i
    · exact le_rfl
  change B.initialFineLoss M (Nat.log2 M + 1) j r x y +
    (∑ z, _ * B.initialFineLoss M (Nat.log2 M + 1) j r z y) ≤ _
  calc
    _ ≤ B.initialInactiveCharge M j r +
        ∑ z, HP.toHierarchyParams.correctionIter (canonicalChannel id (rate ka))
          (canonicalChannel id (rate ka)) (rate ka) B.base HP.k x z *
            B.initialInactiveCharge M j r :=
      add_le_add (hbound x) (sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_left (hbound z) (hseq.nonneg HP.k x z))
    _ = B.initialInactiveCharge M j r +
        (∑ z, HP.toHierarchyParams.correctionIter (canonicalChannel id (rate ka))
          (canonicalChannel id (rate ka)) (rate ka) B.base HP.k x z) *
            B.initialInactiveCharge M j r := by rw [sum_mul]
    _ ≤ B.initialInactiveCharge M j r + (HP.k : ℝ) *
        B.initialInactiveCharge M j r :=
      add_le_add_right (mul_le_mul_of_nonneg_right (hseq.sum_le hC1 HP.k x) hcharge) _
    _ = _ := by ring

omit haux hD hnH hst hs ht hks hka in
/-- Omitted direct bins and their true products are dominated together by the signed
residual. This remains valid before the temporal slack is exhausted and at zero RAW. -/
theorem residualOmittedPositive_le_residual (j : ℕ) (x y : ZMod P) :
    B.residualOmittedPositive M j ka r x y ≤
      max 1 (((HP.k : ℝ) + 1) / HP.θ) *
        HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
          (canonicalChannel id (rate ka)) (rate ka) B.base x y := by
  have hseq := HP.toHierarchyParams.isCorrectionSeq_correctionIter
    (X := canonicalChannel id (rate ka)) (Y := canonicalChannel id (rate ka))
    (rate_pos ka) hC
  have hfine (z : ZMod P) : B.initialFineLoss M (Nat.log2 M + 1) j r z y ≤
      B.base z y := by
    calc
      _ ≤ ∑ i ∈ B.bins, B.binRate i * B.cutoff i (B.base z y / B.binRate i) := by
        unfold initialFineLoss
        apply sum_le_sum
        intro i _
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (by rw [hrate]; exact (rate_pos i).le) (B.cutoff_bounds i _).1
      _ = _ := B.initialBins_polynomial_sum n hbins hrate hcutoff hC hC1 z y
      _ ≤ B.base z y := mul_le_of_le_one_right (hC z y) (polynomialSwitch4_le_one _ _ _)
  apply le_trans _ (HP.toHierarchyParams.correctionInput_last_le_residual
    (canonicalChannel id (rate ka)) (canonicalChannel id (rate ka))
    (rate_pos ka) hC hC1 hCf x y)
  exact add_le_add (hfine x) (sum_le_sum fun z _ =>
    mul_le_mul_of_nonneg_left (hfine z) (hseq.nonneg HP.k x z))

omit hcutoff haux hD hnH hst hs ht hks hka hCf in
/-- After the temporal boundary, all actual exhausted positive bins have a fine-rate
tail. The bound includes the true correction product and requires no all-budgets-live
guard or bin-count factor. This is a deterministic charge, not a child-error salary. -/
theorem residualOmittedPositive_fine_tail_le
    (ks ka j : ℕ) (hcharge : 1 ≤ B.rankCharge) (hrank : 1 ≤ r.task.rank)
    (hsrate : r.source.rate = rate ks) (htrate : r.terminal.rate = rate ka)
    (hp : 0 < B.requestPrecision M r)
    (hd : dyadicSlack (Nat.log2 M + 1) j < M) (x y : ZMod P) :
    B.residualOmittedPositive M j ka r x y ≤
      ((HP.k : ℝ) + 1) *
        (2 * B.binCap * rate ka * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack)) := by
  exact (B.residualOmittedPositive_le_charge M r hC hC1 ka j x y
    (fun i => by rw [hrate]; exact (rate_pos i).le)).trans
      (mul_le_mul_of_nonneg_left
        (B.initialInactiveCharge_fine_tail_le hcharge M n j ks ka hbins hrate
          r hrank hsrate htrate hp hd) (by positivity))

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
