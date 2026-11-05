/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialMean
import Complexity.Foundations.Probability.HierarchyInitialFeasibility

/-!
# Finite scheduled payments for initial conditional means

The chosen horizon kills the actual initial coarse boundary. Omitted polynomial coverage
costs at most the last retained rate. Inactive mass is charged using the literal scale cutoff,
not an assumed parent error. These original finite bounds retain the scale allocation;
they do not close the lower-budget induction, preparation or second noise.

## Main results

* `initialRelativeNoiseBudget_polynomial_le`: structural-cap payment using existing steps.
* `initialCoarseLoss_eq_zero`: no initial coarse boundary at the chosen horizon.
* `initialPolynomialLoss_le`: matrix-unit omitted and inactive charge bound.
* `initialPolynomialLoss_div_le`: omitted/inactive mass in actual decoder units.
* `initialPolynomialLoss_div_bounded_family`: positive-prefix joint semantic payment.
* `initialMeanCharge_preloss`: finite scheduled payment under explicit scale allocation.
* `initialFirstSignal_clippedMean_final`: actual final first-mean payment.
* `initialFirstSignal_clippedMean_preloss`: stationary consumer with row maxima.
* `initial_requestSignals_paid_envelope`: actual compression request with separate noise.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- The initial coarse sample is genuinely at budget zero for the evaluator's horizon,
regardless of the bin's scale cutoff. -/
theorem initialCoarseLoss_eq_zero (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (x y : ZMod P) :
    B.initialCoarseLoss M (Nat.log2 M + 1) r x y = 0 := by
  have hp : M < 2 ^ (Nat.log2 M + 1) := by
    simpa only [Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self (b := 2) (by decide) M
  have hd : M ≤ 2 * dyadicSlack (Nat.log2 M + 1) 0 := by
    simp only [dyadicSlack, Nat.add_sub_cancel, Nat.pow_succ] at hp ⊢
    omega
  unfold initialCoarseLoss
  apply sum_eq_zero
  intro bin _
  have hz : LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) 0)
      B.slack (B.sampleScale { r with usage := r.terminal } (some bin)) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  rw [hz, ite_eq_left rfl]

/-- Omitted coverage is small in matrix units, even for arbitrarily tiny positive entries.
No positive lower bound on entries is needed. -/
theorem initialOmitted_le (n : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    w * (1 - polynomialSwitch4 (1 / 2) 1 (w / rate n)) ≤ rate n := by
  by_cases h : rate n ≤ w
  · rw [polynomialSwitch4_of_ge (by norm_num) ((le_div_iff₀ (rate_pos n)).mpr
      (by simpa only [one_mul] using h))]
    simpa using (rate_pos n).le
  · have hχ := polynomialSwitch4_nonneg (1 / 2) 1 (w / rate n)
    nlinarith [not_le.mp h, mul_nonneg hw hχ]

/-- A finite, source-independent charge for the actual inactive bins at prefix j+1.
The indicator is exactly the literal lastBudget-zero condition, expanded into its two
causes. The primitive bin cap is fixed before evaluating the history. -/
@[expose] def initialInactiveCharge (B : BudgetData HP P) (M j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℝ :=
  B.binCap * ∑ bin ∈ B.bins,
    if M ≤ max (dyadicSlack (Nat.log2 M + 1) j)
      (LogSpaceEstimation.scaleCutoff B.slack
        (B.sampleScale { r with usage := r.terminal } (some bin))) then B.binRate bin else 0

/-- Every inactive-bin payment follows from the actual schedule and primitive cutoff cap. -/
theorem initialFineLoss_le_charge (B : BudgetData HP P) (M j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : ∀ bin, 0 ≤ B.binRate bin) (x y : ZMod P) :
    B.initialFineLoss M (Nat.log2 M + 1) j r x y ≤ B.initialInactiveCharge M j r := by
  unfold initialFineLoss initialInactiveCharge
  rw [mul_sum]
  apply sum_le_sum
  intro bin _
  have hz : LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
      B.slack (B.sampleScale { r with usage := r.terminal } (some bin)) = 0 ↔
      M ≤ max (dyadicSlack (Nat.log2 M + 1) j)
        (LogSpaceEstimation.scaleCutoff B.slack
          (B.sampleScale { r with usage := r.terminal } (some bin))) := by
    unfold LogSpaceEstimation.lastBudget
    omega
  simp only [hz]
  split_ifs
  · simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (B.cutoff_bounds bin _).2 (hrate bin)
  · simp

/-- Once both actual schedule constraints are strictly below M, there is no inactive
charge. This includes the final prefix when all retained scale cutoffs are below M. -/
theorem initialInactiveCharge_eq_zero (B : BudgetData HP P) (M j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hd : dyadicSlack (Nat.log2 M + 1) j < M)
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M) :
    B.initialInactiveCharge M j r = 0 := by
  unfold initialInactiveCharge
  have hz : (∑ bin ∈ B.bins,
      if M ≤ max (dyadicSlack (Nat.log2 M + 1) j)
        (LogSpaceEstimation.scaleCutoff B.slack
          (B.sampleScale { r with usage := r.terminal } (some bin))) then B.binRate bin
      else 0) = 0 := by
    apply sum_eq_zero
    intro bin hi
    rw [ite_eq_right (not_le.mpr (max_lt hd (hc bin hi)))]
  rw [hz, mul_zero]

/-- Finite initial first-mean budget in decoder units. The rank rate is retained explicitly;
this is a computable allocation charge, not a requested final error or a substituted target. -/
@[expose] def initialMeanCharge (B : BudgetData HP P) (M n j ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℝ :=
  (rate n + B.initialInactiveCharge M j r) / rate ka

/-- The matrix-unit deficit uses actual omitted and inactive mass; no output budget or
positive lower bound on base entries is assumed. -/
theorem initialPolynomialLoss_le (B : BudgetData HP P) (M n j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hC : ∀ x y, 0 ≤ B.base x y) (x y : ZMod P) :
    B.initialPolynomialLoss M n j r x y ≤ rate n + B.initialInactiveCharge M j r := by
  unfold initialPolynomialLoss
  rw [B.initialCoarseLoss_eq_zero, add_zero]
  exact add_le_add (initialOmitted_le n (hC x y))
    (B.initialFineLoss_le_charge M j r
      (by intro bin; rw [hrate]; exact (rate_pos bin).le) x y)

/-- Pointwise transport through the actual denominator rankRate+baseEntry. -/
theorem initialPolynomialLoss_div_le (B : BudgetData HP P) (M n j ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hC : ∀ x y, 0 ≤ B.base x y) (x y : ZMod P) :
    B.initialPolynomialLoss M n j r x y / (rate ka + B.base x y) ≤
      B.initialMeanCharge M n j ka r := by
  have hnon := B.initialPolynomialLoss_nonneg M n j r hrate hC x y
  have hbound := B.initialPolynomialLoss_le M n j r hrate hC x y
  exact (div_le_div_of_nonneg_left hnon (rate_pos ka)
    (le_add_of_nonneg_right (hC x y))).trans
      (div_le_div_of_nonneg_right hbound (rate_pos ka).le)

/-- A positive prefix index has slack strictly smaller than the parent budget. Thus,
once every retained scale cutoff is below M, only group zero can have inactive bins. -/
theorem initialInactiveCharge_eq_zero_of_pos (B : BudgetData HP P) (M j : ℕ)
    (hM : 1 < M) (hj : 0 < j)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M) :
    B.initialInactiveCharge M j r = 0 := by
  apply B.initialInactiveCharge_eq_zero M j r _ hc
  have hp : 2 ^ Nat.log2 M ≤ M := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (by omega : M ≠ 0)
  by_cases hl : Nat.log2 M = 0
  · simpa only [dyadicSlack, hl, zero_add, Nat.sub_eq_zero_of_le (by omega : 1 ≤ j + 1),
      pow_zero] using hM
  · have he : Nat.log2 M + 1 - (j + 1) < Nat.log2 M := by omega
    exact (Nat.pow_lt_pow_right (by decide : 1 < 2) he).trans_le hp

/-- Budget-only upper bound on inactive mass, used for the sole possible initial group. -/
theorem initialInactiveCharge_le (B : BudgetData HP P) (M j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hrate : ∀ bin, 0 ≤ B.binRate bin) :
    B.initialInactiveCharge M j r ≤ B.binCap * ∑ bin ∈ B.bins, B.binRate bin := by
  apply mul_le_mul_of_nonneg_left _ B.binCap_nonneg
  apply sum_le_sum
  intro bin _
  split_ifs
  · exact le_rfl
  · exact hrate bin

/-- In a fixed-depth bounded-budget family, every positive prefix pays its actual
omitted/inactive deficit at parent precision. Group zero is deliberately excluded. -/
theorem initialPolynomialLoss_div_bounded_family (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (M n j ks ka : ℕ) (hM : 1 < M) (hj : 0 < j)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M)
    (hhi : M ≤ 32 * B.slack * n) (ha : 2 * ka ≤ n)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y) (x y : ZMod P) :
    B.initialPolynomialLoss M n j r x y / (rate ka + B.base x y) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) := by
  have hg := B.bounded_family_depth_guards hcharge n M ks ka hlo hhi ha r hrate hs ht
  have hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale {r with usage := r.terminal} (some bin)) < M := by
    intro bin hb
    rw [hbins, mem_range] at hb
    exact B.retained_scaleCutoff_lt {r with usage := r.terminal} M n ka hrate ht hlo
      bin (by omega)
  have hz := B.initialInactiveCharge_eq_zero_of_pos M j hM hj r hc
  have hp := B.initialPolynomialLoss_div_le M n j ka r hrate hC x y
  rw [initialMeanCharge, hz, add_zero] at hp
  exact hp.trans hg.2.2

/-- Global finite stationary first-mean payment. Scale allocation makes every positive
index active; the possible initial deficit is multiplied by its actual exponentially small
floor. The inverse-floor stationary coefficient is retained rather than discarded. -/
theorem initialMeanCharge_preloss (B : BudgetData HP P) (M n ka : ℕ) (hM : 1 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hrate : ∀ bin, 0 ≤ B.binRate bin)
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M)
    {δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) :
    let m := Nat.log2 M + 1
    (36 * L + 72 * L / δ) *
      (∑ i ∈ range m, dyadicFloor δ m i * B.initialMeanCharge M n i ka r) ≤
      (36 * L * δ + 72 * L) *
        (rate n / rate ka / 1023 + (1 / 1024 : ℝ) ^ (2 ^ Nat.log2 M) *
          (B.binCap * ∑ bin ∈ B.bins, B.binRate bin) / rate ka) := by
  dsimp only
  let m := Nat.log2 M + 1
  let A := B.binCap * ∑ bin ∈ B.bins, B.binRate bin
  have hA : 0 ≤ A := mul_nonneg B.binCap_nonneg (sum_nonneg fun bin _ => hrate bin)
  have hs : (∑ i ∈ range m, dyadicFloor δ m i * B.initialMeanCharge M n i ka r) ≤
      δ / 1023 * (rate n / rate ka) + dyadicFloor δ m 0 * (A / rate ka) := by
    have hi (i : ℕ) : B.initialMeanCharge M n i ka r ≤
        rate n / rate ka + if i = 0 then A / rate ka else 0 := by
      by_cases hz : i = 0
      · subst i
        simp only [initialMeanCharge, ↓reduceIte, ← add_div]
        exact div_le_div_of_nonneg_right
          (add_le_add le_rfl (B.initialInactiveCharge_le M 0 r hrate)) (rate_pos ka).le
      · rw [initialMeanCharge, B.initialInactiveCharge_eq_zero_of_pos M i hM
          (by omega) r hc, add_zero, ite_eq_right hz, add_zero]
    calc
      _ ≤ ∑ i ∈ range m, dyadicFloor δ m i *
          (rate n / rate ka + if i = 0 then A / rate ka else 0) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i)
          (dyadicFloor_nonneg hδ.le m i)
      _ = (∑ i ∈ range m, dyadicFloor δ m i) * (rate n / rate ka) +
          dyadicFloor δ m 0 * (A / rate ka) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, mul_ite, mul_zero]
        rw [sum_ite_eq']
        simp only [m, mem_range, Nat.zero_lt_succ, ↓reduceIte]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
        (sum_range_dyadicFloor_le_scale hδ.le m)
        (div_nonneg (rate_pos n).le (rate_pos ka).le)) le_rfl
  have hp := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 36 * L + 72 * L / δ by positivity)
  refine hp.trans_eq ?_
  dsimp only [dyadicFloor, dyadicSlack, m]
  simp only [Nat.add_sub_cancel]
  dsimp only [A]
  field_simp

variable [Fact P.Prime]

section Polynomial
variable (B : BudgetData HP P) (M : ℕ) (hM : 0 < M) (n : ℕ)
  (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1))
  (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
  (hD : B.padding ≠ 0) (H : Horizon P) (hn : n ≤ H.maxExponent)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
  (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
  (hks : ks ≤ H.maxExponent)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
  (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
  (hF : B.initialPrefixes M r = some F) (j : ℕ) (hj : j < Nat.log2 M + 1)
include hM hbins hrate hcutoff haux hD hn hst hs ht hks hC hC1 hF


include hj in
/-- Real predecoder consumer of the finite payment: no desired first-channel error is
assumed. The original-environment actual mean is bounded at every executed prefix. -/
theorem initialFirstSignal_clippedMean_le (Lt : ℕ) (ζ : ℝ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) (x y : ZMod P) :
    actualClippedMean HP s t (side P ks) (side P ka) Lt B.padding ss st ka B.base ζ
      (firstSignalIncrement F ka second) 0 0 j x y ≤ B.initialMeanCharge M n j ka r := by
  rw [B.initialFirstSignal_clippedMean M hM n hbins hrate hcutoff haux hD H hn r
    s t hst ks ka ss st hs ht hks hC hC1 F hF j hj Lt ζ second x y]
  exact (min_le_right _ _).trans (B.initialPolynomialLoss_div_le M n j ka r hrate hC x y)

/-- Final first-mean payment after the actual retained scale cutoffs fit the parent
budget. Omitted coverage remains charged; no minimum positive base entry is assumed. -/
theorem initialFirstSignal_clippedMean_final (hM1 : 1 < M)
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M)
    (Lt : ℕ) (ζ : ℝ) (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (x y : ZMod P) :
    actualClippedMean HP s t (side P ks) (side P ka) Lt B.padding ss st ka B.base ζ
      (firstSignalIncrement F ka second) 0 0 (Nat.log2 M) x y ≤ rate n / rate ka := by
  have hd : dyadicSlack (Nat.log2 M + 1) (Nat.log2 M) < M := by
    simpa only [dyadicSlack_last] using hM1
  have hc0 := B.initialInactiveCharge_eq_zero M (Nat.log2 M) r hd hc
  have hb := B.initialFirstSignal_clippedMean_le M hM n hbins hrate hcutoff haux hD H hn r
    s t hst ks ka ss st hs ht hks hC hC1 F hF (Nat.log2 M) (by omega) Lt ζ second x y
  simpa only [initialMeanCharge, hc0, add_zero] using hb

/-- Stationary preloss of the actual first mean, uniformly over rows and environments.
The rank maximum may choose a different endpoint at every prefix. Second mean/noise and
centered first noise are separate payments. -/
theorem initialFirstSignal_clippedMean_preloss (hM1 : 1 < M)
    (hc : ∀ bin ∈ B.bins, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale { r with usage := r.terminal } (some bin)) < M)
    (Lt : ℕ) (ζ : ℝ) (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    {δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (σ : Environment P 3) (x : ZMod P) :
    let m := Nat.log2 M + 1
    (36 * L + 72 * L / δ) * (∑ i ∈ range m, dyadicFloor δ m i *
      kthLargest 1 {y | retainedMask t Lt B.padding st σ y}
        (fun y => actualClippedMean HP s t (side P ks) (side P ka) Lt B.padding ss st
          ka B.base ζ (firstSignalIncrement F ka second) 0 0 i x y)) ≤
      (36 * L * δ + 72 * L) *
        (rate n / rate ka / 1023 + (1 / 1024 : ℝ) ^ (2 ^ Nat.log2 M) *
          (B.binCap * ∑ bin ∈ B.bins, B.binRate bin) / rate ka) := by
  dsimp only
  apply le_trans _ (B.initialMeanCharge_preloss M n ka hM1 r
    (by intro bin; rw [hrate]; exact (rate_pos bin).le) hc hδ hL)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (dyadicFloor_nonneg hδ.le _ _)
  have he : 0 ≤ B.initialMeanCharge M n i ka r := by
    apply div_nonneg _ (rate_pos ka).le
    apply add_nonneg (rate_pos n).le
    apply mul_nonneg B.binCap_nonneg
    apply sum_nonneg
    intro bin _
    split_ifs
    · rw [hrate]; exact (rate_pos bin).le
    · exact le_rfl
  apply kthLargest_le he
  intro y _
  exact B.initialFirstSignal_clippedMean_le M hM n hbins hrate hcutoff haux hD H hn r
    s t hst ks ka ss st hs ht hks hC hC1 F hF i (mem_range.mp hi) Lt ζ second x y

include hj in
/-- The executed compression request consumes the finite first-mean charge. The actual
preparation target, centered first noise and unpaid second discrepancy remain literal. -/
theorem initial_requestSignals_paid_envelope (bin : ℕ) (ζ : ℝ)
    (W : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P 3) (x y : ZMod P) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    let truth := requestSignals ζ B.padding id r (fun _ => B.base)
      (B.binPreparation bin r (fun _ => B.base)) σ x y
    let a := uncompressedRow
      (firstSignalIncrement F ka (secondSignalIncrement W ζ) σ x) 0 (j + 1) y
    clippedError (truth 0) (truth 1) a ≤
      B.initialMeanCharge M n j ka r +
      |F (j + 1) σ x y - rowSliceMean Xs Ya (F (j + 1)) x y| / rate ka +
      |a 1 - truth 1| := by
  have hp := B.initial_requestSignals_envelope M hM n hbins hrate hcutoff haux hD H hn r
    s t hst ks ka ss st hs ht hks hC hC1 F hF j hj bin ζ W σ x y
  exact hp.trans (add_le_add (add_le_add
    (B.initialPolynomialLoss_div_le M n j ka r hrate hC x y) le_rfl) le_rfl)


end Polynomial

section PolynomialNoise

/-- The existing walk schedule pays the canonical polynomial input's normalized fourth
moment with a structural cap factor. Joint slice densities and the correlated prefix cube
are those of `initialRelativeNoiseBudget`; no transported child error is included. -/
theorem initialRelativeNoiseBudget_polynomial_le (B : BudgetData HP P)
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hb : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (ha : ka ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1) (j : ℕ) :
    let m := Nat.log2 M + 1
    let q := {r with usage := r.terminal}
    B.initialRelativeNoiseBudget M r s t hst ks ka ss st B.base j ≤
      (256 * B.binCap) ^ 4 * ((min j m : ℕ) ^ (3 : ℕ) *
        ∑ i ∈ range (min j m),
          ((2 : ℝ) ^ (-B.requestPrecision M q) * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 4) := by
  dsimp only
  let C := (256 * B.binCap) ^ 4
  let ρ : ℝ := 1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)
  let q := {r with usage := r.terminal}
  let m := Nat.log2 M + 1
  have hsource : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  have hNu : 0 < (P : ℝ) * r.source.rate :=
    mul_pos (by exact_mod_cast (Fact.out : P.Prime).pos) hsource
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hr : 0 < ρ := by norm_num [ρ]
  have hr1 : ρ < 1 := by norm_num [ρ]
  have hgraph (x y : ZMod P) :
      RotationMap.spectralExpansion (graph s t hst (side P ks) (side P ka)
        (side_le P ks) (side_le P ka) (CopyPadding.identifier B.padding ss)
        (CopyPadding.identifier B.padding st) x y) ≤ ρ := by
    unfold graph
    rw [RotationMap.spectralExpansion_reindex, RotationMap.spectralExpansion_reindex]
    exact spectralExpansion_lazy_ofPerms_componentMove_le (by decide)
  unfold initialRelativeNoiseBudget
  dsimp only
  rw [mul_comm C, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [sum_mul]
  apply sum_le_sum
  intro i _
  rw [mul_comm _ C]
  let d := dyadicSlack m i
  let T := B.steps M q d
  have hp := spectralWalkLength_payment hr hr1
    (show 0 ≤ 32 * ((P : ℝ)^2 / (P * r.source.rate) * B.magnitude q ^ 4) by positivity)
    (Real.rpow_pos_of_pos (by norm_num) _) d T (Nat.le_max_right _ _)
  have hm : 1 ≤ B.magnitude q ^ 4 := one_le_pow₀ (B.one_le_magnitude q)
  have he : 0 ≤ (P : ℝ)^2 / (P * r.source.rate) := div_nonneg (sq_nonneg _) hNu.le
  have hpay : 2 * ((P : ℝ)^2 / (P * r.source.rate)) * ρ ^ (2 * T) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M q) * (64 : ℝ)⁻¹ ^ d) ^ 4 := by
    apply le_trans _ hp
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le _)
    nlinarith [mul_le_mul_of_nonneg_left hm he]
  calc
    _ ≤ ((P : ℝ) * r.source.rate)⁻¹ * ∑ _x : ZMod P, ∑ _y : ZMod P,
        2 * ρ ^ (2 * T) * C := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu.le)
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      have hmom := B.initialGroupInput_polynomial_relative_fourth_le hrate hcutoff H hb
        M d q s t ks ka ss st ht ha hC hC1 x y
      have hd : (({σ | retainedMask s (side P ks) B.padding ss σ x ∧
          retainedMask t (side P ka) B.padding st σ y} :
            Finset (Environment P 3)).dens : ℝ) ≤ 1 := by
        exact_mod_cast Finset.dens_le_one
      have hg := pow_le_pow_left₀ (RotationMap.spectralExpansion_nonneg _) (hgraph x y) (2 * T)
      apply (mul_le_mul hd (mul_le_mul (mul_le_mul_of_nonneg_left hg (by norm_num))
        hmom (expect_nonneg fun _ _ => by positivity) (by positivity))
        (mul_nonneg (mul_nonneg (by norm_num)
          (pow_nonneg (RotationMap.spectralExpansion_nonneg _) _))
          (expect_nonneg fun _ _ => by positivity)) zero_le_one).trans
      rw [one_mul]
    _ = C * (2 * ((P : ℝ)^2 / (P * r.source.rate)) * ρ ^ (2 * T)) := by
      simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      ring
    _ ≤ C * ((2 : ℝ) ^ (-B.requestPrecision M q) * (64 : ℝ)⁻¹ ^ d) ^ 4 :=
      mul_le_mul_of_nonneg_left hpay hC0

end PolynomialNoise

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
