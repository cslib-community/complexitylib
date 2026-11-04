/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialHistory

/-!
# Canonical means of initial statistical-budget histories

The direct dense normalization is averaged on the original source/terminal environment,
including unequal bin rates. Literal budget boundaries survive the group telescope.
The polynomial ratio-16 specialization retains omitted coverage, inactive fine samples
and the initial coarse boundary separately. These are first-signal deterministic errors;
preparation transport, second noise and the full parent induction remain separate.
The assembly proofs are original.

## Main results

* `initialSample_mean`: canonical bins on the parent's original source/terminal event.
* `initialPrefix_canonical_mean`: all bins with both literal budget boundaries.
* `initialPrefix_polynomial_mean`: exact omitted, inactive and coarse deficit.
* `initialFirstSignal_clippedMean`: actual first predecoder deterministic statistic.
* `initial_requestSignals_envelope`: actual bin-preparation raw-prefix envelope.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

set_option backward.isDefEq.respectTransparency false in
/-- Each literal initial sample has its canonical matrix-unit bin mean. The conditioning
is the parent's source/terminal event, not the narrower bin usage event. -/
theorem initialSample_mean (B : BudgetData HP P) (hD : B.padding ≠ 0)
    (H : Horizon P) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka kb bin : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hks : ks ≤ H.maxExponent) (hkb : kb ≤ H.maxExponent)
    (hb : B.binRate bin = rate kb)
    (hprep : ∀ v, B.cutoff bin v ≠ 0 → B.auxiliary bin v = 1)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K) (x y : ZMod P) :
    rowSliceMean (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ka) (CopyPadding.identifier B.padding st))
      (B.initialSample r bin) x y = B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin) := by
  let req := (HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)).direct
  have hr : Admissible req := by
    dsimp only [req, HierarchyTask.rawRequests]
    rw [hs, ht]
    exact ⟨hst, rfl, rfl⟩
  let q := fun A => coordinate B.padding (gridChannel t ka st) A y
  have hsub (A : FrameChannel P 4 1) : splitUsage B.padding id req A y → q A := by
    dsimp only [splitUsage, req, HierarchyTask.rawRequests, q]
    rw [ht, hb]
    exact coordinate_min_grid B.padding t st ka kb A y
  have hm := denseChild_mean_on_terminal_event B.padding id req hr hD Function.injective_id H
    hks (by dsimp only [req, HierarchyTask.rawRequests]; rw [hs]; rfl) hkb
    (by dsimp only [req, HierarchyTask.rawRequests]; rw [hb])
    (u := max ka kb) (by
      dsimp only [req, HierarchyTask.rawRequests]
      rw [ht, hb]
      exact rate_min ka kb)
    (B.cutoff bin) (B.auxiliary bin) HP.ρ HP.K B.base q x y hsub hprep
    HP.ρ_nonneg HP.ρ_le_one HP.η_pos HP.ρ_one (hC x)
    (by simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using hC1 x) hK
  convert hm using 1 <;>
    simp only [rowSliceMean, initialSample, HierarchyTask.usageRatio, req,
      HierarchyTask.rawRequests, hs, ht, hb, q, coordinate, gridChannel,
      CorrectionRowTask.Channel.retains, channels, semanticSide_grid, X, Y, id_eq]

/-- Stationarity and the literal input telescope yield canonical bin means with both
budget guards. No single-walk representation of the prefix or desired mean is assumed. -/
theorem initialPrefix_canonical_mean (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (hD : B.padding ≠ 0) (H : Horizon P)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (hks : ks ≤ H.maxExponent)
    (hb : ∀ bin ∈ B.bins, ∃ kb ≤ H.maxExponent, B.binRate bin = rate kb)
    (hprep : ∀ bin ∈ B.bins, ∀ v, B.cutoff bin v ≠ 0 → B.auxiliary bin v = 1)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F) (j : ℕ) (hj : j < Nat.log2 M + 1)
    (x y : ZMod P) :
    rowSliceMean (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ka) (CopyPadding.identifier B.padding st)) (F (j + 1)) x y =
      ∑ bin ∈ B.bins,
        ((if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale {r with usage := r.terminal} (some bin)) = 0 then 0
          else B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin)) -
        (if LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) 0) B.slack
          (B.sampleScale {r with usage := r.terminal} (some bin)) = 0 then 0
          else B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin))) := by
  have hm := B.initialPrefix_mean M hM hbins r s t hst ks ka ss st hs ht F hF (j + 1) x y
  dsimp only at hm
  rw [min_eq_left (by omega)] at hm
  rw [hm]
  simp only [rowSliceMean, ← expect_sum_comm]
  simp_rw [B.initialGroupInput_sum M (Nat.log2 M + 1) j hj]
  rw [expect_sum_comm]
  apply sum_congr rfl
  intro bin hi
  obtain ⟨kb, hkb, hrate⟩ := hb bin hi
  have hbmean := B.initialSample_mean hD H {r with usage := r.terminal}
    s t hst ks ka kb bin ss st hs ht hks hkb hrate (hprep bin hi) hC hC1 hK x y
  change (𝔼 σ ∈ _, _) = _ at hbmean ⊢
  rw [expect_sub_distrib]
  split_ifs <;> simp only [expect_const_zero, hbmean]

/-- Canonical bin mass excluded because the current fine budget is inactive. -/
@[expose] def initialFineLoss (B : BudgetData HP P) (M m j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (x y : ZMod P) : ℝ :=
  ∑ bin ∈ B.bins,
    if LogSpaceEstimation.lastBudget M (dyadicSlack m j) B.slack
      (B.sampleScale {r with usage := r.terminal} (some bin)) = 0 then
      B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin) else 0

/-- Canonical bin mass subtracted at the initial coarse boundary. It is a separate
loss even when later fine budgets are active. -/
@[expose] def initialCoarseLoss (B : BudgetData HP P) (M m : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (x y : ZMod P) : ℝ :=
  ∑ bin ∈ B.bins,
    if LogSpaceEstimation.lastBudget M (2 * dyadicSlack m 0) B.slack
      (B.sampleScale {r with usage := r.terminal} (some bin)) = 0 then 0
      else B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin)

/-- Actual polynomial ratio-16 bins cover the base up to the explicit omitted fine-bin
mass. No minimum positive base entry or sufficient-budget hypothesis is required. -/
theorem initialBins_polynomial_sum (B : BudgetData HP P) (n : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1) (x y : ZMod P) :
    ∑ bin ∈ B.bins, B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin) =
      B.base x y * polynomialSwitch4 (1 / 2) 1 (B.base x y / rate n) := by
  have hw : B.base x y ≤ 1 := by
    have hs := hC1 x
    simp only [mulVec, dotProduct, Pi.one_apply, mul_one] at hs
    exact (single_le_sum (fun z _ => hC x z) (mem_univ y)).trans hs
  rw [hbins, hrate, hcutoff]
  have he (i : ℕ) : boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1) (B.base x y / rate i) =
      routedBinCutoff (polynomialSwitch4 (1 / 2) 1) rate i (fun _ => 1)
        (B.base x y / rate i) := by
    cases i with
    | zero => apply boundedRoutedBinCutoff_eq (div_nonneg (hC x y) (rate_pos 0).le)
              simpa only [rate, pow_zero, inv_one, one_pow, div_one] using hw
    | succ i => simp only [boundedRoutedBinCutoff, Nat.succ_ne_zero, ↓reduceIte,
        not_lt.mpr (div_nonneg (hC x y) (rate_pos _).le)]
  simp_rw [he, mul_routedBinCutoff (rate_pos _).ne', mul_one]
  rw [← mul_sum, sum_range_binWeight]

/-- Total first-mean deficit for actual polynomial initial histories. The three charges
remain separate in the definition so coverage is never confused with an active budget. -/
@[expose] def initialPolynomialLoss (B : BudgetData HP P) (M n j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (x y : ZMod P) : ℝ :=
  B.base x y * (1 - polynomialSwitch4 (1 / 2) 1 (B.base x y / rate n)) +
    B.initialFineLoss M (Nat.log2 M + 1) j r x y +
    B.initialCoarseLoss M (Nat.log2 M + 1) r x y

omit [Fact P.Prime] in
/-- Every explicit first-mean charge is nonnegative for nonnegative base entries and
positive bin rates. No assumption about a desired output error occurs. -/
theorem initialPolynomialLoss_nonneg (B : BudgetData HP P) (M n j : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hC : ∀ x y, 0 ≤ B.base x y) (x y : ZMod P) :
    0 ≤ B.initialPolynomialLoss M n j r x y := by
  have hc (bin : ℕ) : 0 ≤ B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin) := by
    rw [hrate]
    exact mul_nonneg (rate_pos bin).le (B.cutoff_bounds bin _).1
  unfold initialPolynomialLoss initialFineLoss initialCoarseLoss
  apply add_nonneg (add_nonneg
    (mul_nonneg (hC x y) (sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _))) ?_) ?_
  · exact sum_nonneg fun bin _ => by
      split_ifs <;> first | exact hc bin | exact le_rfl
  · exact sum_nonneg fun bin _ => by
      split_ifs <;> first | exact hc bin | exact le_rfl

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
include hM hbins hrate hcutoff haux hD hn hst hs ht hks hC hC1 hF hj

/-- The canonical mean deficit of an executed initial prefix is exactly omitted fine
coverage plus inactive fine samples plus the initial coarse boundary. All conditioning
uses the original environment; the target is the initial base, not a residual-specific mean. -/
theorem initialPrefix_polynomial_mean (x y : ZMod P) :
    let m := Nat.log2 M + 1
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    B.base x y - rowSliceMean Xs Ya (F (j + 1)) x y =
      B.base x y * (1 - polynomialSwitch4 (1 / 2) 1 (B.base x y / rate n)) +
        B.initialFineLoss M m j r x y + B.initialCoarseLoss M m r x y := by
  dsimp only
  have hne : B.bins.Nonempty := by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩
  have hb (bin : ℕ) (hi : bin ∈ B.bins) :
      ∃ kb ≤ H.maxExponent, B.binRate bin = rate kb := by
    rw [hbins, mem_range] at hi
    exact ⟨bin, by omega, congrFun hrate bin⟩
  have hp (bin : ℕ) (_hi : bin ∈ B.bins) (v : ℝ) (hv : B.cutoff bin v ≠ 0) :
      B.auxiliary bin v = 1 := by
    rw [hcutoff] at hv
    rw [haux]
    exact HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      bin (fun _ => 1) hv
  have hk : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  rw [B.initialPrefix_canonical_mean M hM hne hD H r s t hst ks ka ss st hs ht
    hks hb hp hC hC1 hk F hF j hj]
  have hcover := B.initialBins_polynomial_sum n hbins hrate hcutoff hC hC1 x y
  have hsplit : (∑ bin ∈ B.bins,
      ((if LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale {r with usage := r.terminal} (some bin)) = 0 then 0
        else B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin)) -
      (if LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) 0) B.slack
        (B.sampleScale {r with usage := r.terminal} (some bin)) = 0 then 0
        else B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin)))) =
      (∑ bin ∈ B.bins, B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin)) -
        B.initialFineLoss M (Nat.log2 M + 1) j r x y -
        B.initialCoarseLoss M (Nat.log2 M + 1) r x y := by
    unfold initialFineLoss initialCoarseLoss
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro bin _
    split_ifs <;> ring
  rw [hsplit, hcover]
  ring
/-- Exact first-channel deterministic error in decoder units. The denominator retains
the parent rank rate and the initial canonical base entry. -/
theorem initialFirstSignal_mean_error (x y : ZMod P) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    |rowSliceMean Xs Ya (F (j + 1)) x y / rate ka - B.base x y / rate ka| /
      (1 + B.base x y / rate ka) =
      B.initialPolynomialLoss M n j r x y / (rate ka + B.base x y) := by
  dsimp only
  have hm := B.initialPrefix_polynomial_mean M hM n hbins hrate hcutoff haux hD H hn
    r s t hst ks ka ss st hs ht hks hC hC1 F hF j hj x y
  change B.base x y - _ = B.initialPolynomialLoss M n j r x y at hm
  have hnloss := B.initialPolynomialLoss_nonneg M n j r hrate hC x y
  rw [← sub_div, abs_div, abs_of_pos (rate_pos ka), abs_sub_comm, hm,
    abs_of_nonneg hnloss]
  rw [div_div, mul_add, mul_one, mul_div_cancel₀ _ (rate_pos ka).ne']

set_option backward.isDefEq.respectTransparency false in
/-- The actual first clipped-mean statistic used by the shared predecoder has an exact
deterministic envelope. Second preparation and noise are arbitrary and remain unpaid. -/
theorem initialFirstSignal_clippedMean (Lt : ℕ) (ζ : ℝ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) (x y : ZMod P) :
    actualClippedMean HP s t (side P ks) (side P ka) Lt B.padding ss st ka B.base ζ
      (firstSignalIncrement F ka second) 0 0 j x y =
      min 1 (B.initialPolynomialLoss M n j r x y / (rate ka + B.base x y)) := by
  have hm := B.initialFirstSignal_mean_error M hM n hbins hrate hcutoff haux hD H hn
    r s t hst ks ka ss st hs ht hks hC hC1 F hF j hj x y
  unfold actualClippedMean twoMaskMean
  simp only [Fin.isValue, ↓reduceIte,
    actualPrefix_firstSignalIncrement F ka second 0 (by intros; rfl)]
  unfold rowSliceMean at hm ⊢
  simp only [← expect_div]
  simpa only [retainedMask, X, Y] using congrArg (min 1) hm

/-- First deterministic envelope plus the literal centered first noise and the still
unpaid second-channel discrepancy bound the actual raw-prefix clipped error. This is in
the form consumed by `CompressionIntegrated`, at post-increment prefix j+1. -/
theorem initialFirstSignal_envelope
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (v : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P 3) (x y : ZMod P) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    let a := actualPrefix (firstSignalIncrement F ka second) 0 j σ x y
    clippedError (B.base x y / rate ka) (v σ x y) a ≤
      B.initialPolynomialLoss M n j r x y / (rate ka + B.base x y) +
      |F (j + 1) σ x y - rowSliceMean Xs Ya (F (j + 1)) x y| / rate ka +
      |a 1 - v σ x y| := by
  extract_lets Xs Ya a
  have hd := div_nonneg (hC x y) (rate_pos ka).le
  have hden : 0 < 1 + B.base x y / rate ka := by positivity
  have hμ := B.initialFirstSignal_mean_error M hM n hbins hrate hcutoff haux hD H hn
    r s t hst ks ka ss st hs ht hks hC hC1 F hF j hj x y
  have hnloss := div_nonneg (B.initialPolynomialLoss_nonneg M n j r hrate hC x y)
    (add_pos_of_pos_of_nonneg (rate_pos ka) (hC x y)).le
  have ha : a 0 = F (j + 1) σ x y / rate ka :=
    actualPrefix_firstSignalIncrement F ka second 0 (by intros; rfl) j σ x y
  have htri := abs_sub_le (F (j + 1) σ x y / rate ka)
    (rowSliceMean Xs Ya (F (j + 1)) x y / rate ka) (B.base x y / rate ka)
  have hrel := div_le_div_of_nonneg_right htri hden.le
  rw [add_div, hμ] at hrel
  have hnoise : |F (j + 1) σ x y / rate ka -
      rowSliceMean Xs Ya (F (j + 1)) x y / rate ka| /
      (1 + B.base x y / rate ka) ≤
      |F (j + 1) σ x y - rowSliceMean Xs Ya (F (j + 1)) x y| / rate ka := by
    rw [← sub_div, abs_div, abs_of_pos (rate_pos ka)]
    exact div_le_self (div_nonneg (abs_nonneg _) (rate_pos ka).le) (by linarith)
  unfold clippedError
  apply max_le
  · exact (min_le_right _ _).trans (by rw [ha]; linarith [abs_nonneg (a 1 - v σ x y)])
  · exact (min_le_right _ _).trans (le_add_of_nonneg_left
      (add_nonneg hnloss (div_nonneg (abs_nonneg _) (rate_pos ka).le)))

/-- Specialization to the actual bin-preparation target and the two actual signal
increments used by `compressedBin`. The last summand is precisely the remaining second
signal obligation; this theorem does not assume it is small. -/
theorem initial_requestSignals_envelope (bin : ℕ) (ζ : ℝ)
    (W : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P 3) (x y : ZMod P) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    let truth := requestSignals ζ B.padding id r (fun _ => B.base)
      (B.binPreparation bin r (fun _ => B.base)) σ x y
    let a := uncompressedRow
      (firstSignalIncrement F ka (secondSignalIncrement W ζ) σ x) 0 (j + 1) y
    clippedError (truth 0) (truth 1) a ≤
      B.initialPolynomialLoss M n j r x y / (rate ka + B.base x y) +
      |F (j + 1) σ x y - rowSliceMean Xs Ya (F (j + 1)) x y| / rate ka +
      |a 1 - truth 1| := by
  dsimp only
  have hfirst : requestSignals ζ B.padding id r (fun _ => B.base)
      (B.binPreparation bin r (fun _ => B.base)) σ x y 0 = B.base x y / rate ka := by
    simp only [requestSignals, Fin.isValue, ↓reduceIte, ht, gridChannel]
  rw [hfirst]
  exact B.initialFirstSignal_envelope M hM n hbins hrate hcutoff haux hD H hn r
    s t hst ks ka ss st hs ht hks hC hC1 F hF j hj (secondSignalIncrement W ζ)
    (fun σ x y => requestSignals ζ B.padding id r (fun _ => B.base)
      (B.binPreparation bin r (fun _ => B.base)) σ x y 1) σ x y

end Polynomial

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
