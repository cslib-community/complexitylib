/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPrefixMean
public import Complexity.Foundations.Probability.NormalizedAtomRows.ScheduledMeanTail
public import Complexity.Foundations.Probability.NormalizedAtomRows.FirstSignal
public import Complexity.Foundations.Probability.NormalizedAtomRows.ScheduleAllocation

/-!
# Literal RAW first-mean schedule payments

`rawFirstPrefixes` decodes the actual completed RAW groups, with no replacement
of their histories or budgets. `raw_residual_first_mean_schedule` consumes the
existential output of `raw_residual_prefix_clipped_le` at every prefix. Option
uniqueness identifies all its witnesses with this one executed history. The
first-signal identity then transports their clipped means without undoing clipping.
Its increments equal the production `requestSignals` first coordinate on each
literal completed group, including the first increment from zero.

The stationary floor, final prefix, raw false-charge and deterministic heavy-event
tail all receive horizon-independent payments. The last bound concerns the actual
`meanFirstEvent` and `meanRowTail`, using genuine residual substochastic mass and
the existing rarity/Minkowski theorem. Centered RAW noise receives no rarity.

The primitive HP/cap cost and charge are those of `exists_residualRawMean_charge`,
fixed before fields, horizons, bins, exponents, budgets and precision. The supplied
prefix certificates retain positive-only own-request IH and separate completion
availability; this module constructs neither jointly. Second mean, both centered
noises, complete reserve allocation, later inputs and native RL=L remain open.
These are original finite consumers; first-signal/compression proof patterns are
adapted from Samuel Schlesinger. No new cited mathematical endpoint is asserted.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Prefixes of the literal completed RAW groups. Decoding alone asserts no
availability: the schedule consumer separately proves every used group executed. -/
@[expose] def rawFirstPrefixes
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (j : ℕ) (σ : Environment P 3) (x y : ZMod P) : ℝ :=
  ∑ i ∈ range j,
    (B.completedGroup history M (dyadicSlack (Nat.log2 M + 1) i) t r).getD 0 σ x y

/-- Actual RAW prefix certificates pay the literal first deterministic statistic.
The premise is exactly the output of `raw_residual_prefix_clipped_le`, not a
scalar schedule surrogate. Each witness includes all executed groups and RAW.
Only the deterministic tail receives heavy-event rarity. -/
theorem raw_residual_first_mean_schedule_of_prefix
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hD : B.padding ≠ 0) (H : Horizon P) (hka : ka ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (floor radius ζ : ℝ) (hf : 0 < floor)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (hprefix : ∀ j < Nat.log2 M + 1,
      let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
        (canonicalChannel id (rate ka)) (rate ka) B.base
      ∃ F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ,
        (∀ i < Nat.log2 M + 1, B.completedGroup history M
          (dyadicSlack (Nat.log2 M + 1) i) .residual r = some (F i)) ∧
        B.raw history M .residual r = some (fun σ x y =>
          ∑ i ∈ range (Nat.log2 M + 1), F i σ x y) ∧
        rowNormPow 4 P r.source.rate
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun _ x y => min 1 (|rowSliceMean
            (fun σ x => r.source.retains (channels B.padding) σ x)
            (fun σ y => r.terminal.retains (channels B.padding) σ y)
            (fun σ x y => ∑ i ∈ range (j + 1), F i σ x y) x y - G x y| /
              (rate ka + G x y))) ≤
          (residualRawMeanRootCost HP B.binCap * (2 : ℝ) ^ (-B.requestPrecision M r) *
            (2 : ℝ) ^ (-B.rankCharge) *
            (2 : ℝ) ^ ((dyadicSlack (Nat.log2 M + 1) j : ℝ) / (16 * B.slack))) ^ 4) :
    let m := Nat.log2 M + 1
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let X := retainedMask r.source.role (side P ks) B.padding r.source.suffix
    let Y := retainedMask r.terminal.role (side P ka) B.padding r.terminal.suffix
    let Δ := firstSignalIncrement (B.rawFirstPrefixes history M .residual r) ka second
    let μ := fun j x y => actualClippedMean HP r.source.role r.terminal.role
      (side P ks) (side P ka) (side P ka) B.padding r.source.suffix r.terminal.suffix
      ka G ζ Δ 0 0 j x y
    let b := fun j => rowNormPow 4 P r.source.rate X Y (fun _ => μ j)
    let E := residualRawMeanRootCost HP B.binCap * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge)
    (∀ i σ x y, Δ σ x i y 0 = requestSignals ζ B.padding id r
      ((B.completedGroup history M (dyadicSlack m i) .residual r).getD 0) 0 σ x y 0) ∧
    (∀ i < m, ∃ F, B.completedGroup history M (dyadicSlack m i) .residual r = some F) ∧
    B.raw history M .residual r = some (B.rawFirstPrefixes history M .residual r m) ∧
    (∑ j ∈ range m, dyadicFloor floor m j * b j ^ (4⁻¹ : ℝ)) ≤ floor * E / 511 ∧
    b (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤ 2 * E ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * b j) ≤
      (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)) * E ^ 4 / 63 ∧
    (∑ j ∈ range m,
      (((2 + 256 / dyadicFloor floor m j) / (compatibleCapacity HP.K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * b i ^ (4⁻¹ : ℝ)) ≤
      (2 + 256 / floor) ^ (4⁻¹ : ℝ) * E / 63 ∧
    vertexNormPow 4 P r.source.rate X (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent r.terminal.role B.padding r.terminal.suffix
        ka m j floor G (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
          meanRowTail r.terminal.role (side P ka) B.padding r.terminal.suffix m j μ σ x
        else 0) ≤ ((2 + 256 / floor) ^ (4⁻¹ : ℝ) * E / 63) ^ 4 := by
  extract_lets m G X Y Δ μ b E
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hG : ∀ x y, 0 ≤ G x y := HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC
  have hmass : ∀ x, ∑ y, G x y ≤ 1 :=
    HP.toHierarchyParams.residual_sum_le_one (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate_pos ka) hC1
  have hgeo : 0 < 1 - (2 : ℝ) ^ (-3 / 4 : ℝ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hcap := B.binCap_nonneg
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hcost : 0 ≤ residualRawMeanRootCost HP B.binCap := by
    dsimp only [residualRawMeanRootCost, residualDirectRootCost,
      residualProductNegativeRootCost, residualProductRootCost]
    positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hdecoded (j : ℕ)
      (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (hg : ∀ i < m, B.completedGroup history M (dyadicSlack m i) .residual r = some (F i))
      (hj : j ≤ m) : B.rawFirstPrefixes history M .residual r j =
        (fun σ x y => ∑ i ∈ range j, F i σ x y) := by
    funext σ x y
    apply sum_congr rfl
    intro i hi
    rw [hg i ((mem_range.mp hi).trans_le hj), Option.getD_some]
  have hb0 (j : ℕ) : 0 ≤ b j := rowNormPow_nonneg hNu _
  have hroot (j : ℕ) (hj : j < m) : b j ^ (4⁻¹ : ℝ) ≤
      E * (2 : ℝ) ^ dyadicSlack m j := by
    obtain ⟨F, hg, _, hm⟩ := hprefix j hj
    have hμ : μ j = fun x y => min 1 (|rowSliceMean
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ x y => ∑ i ∈ range (j + 1), F i σ x y) x y - G x y| /
          (rate ka + G x y)) := by
      funext x y
      dsimp only [μ, Δ]
      rw [actualClippedMean_first_prefix_eq, hdecoded (j + 1) F hg (by omega)]
      simp only [CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
        hs, ht, retainedMask, rowSliceMean]
    have hpow : b j ≤ (E * (2 : ℝ) ^
        ((dyadicSlack m j : ℝ) / (16 * B.slack))) ^ 4 := by
      simpa only [b, hμ, X, Y, E, G, CorrectionRowTask.Channel.retains, channels,
        semanticSide_grid, hs, ht, retainedMask, rowNormPow] using hm
    have hr := Real.rpow_le_rpow (hb0 j) hpow (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    have he : ((E * (2 : ℝ) ^ ((dyadicSlack m j : ℝ) / (16 * B.slack))) ^ 4) ^
        (4⁻¹ : ℝ) = E * (2 : ℝ) ^ ((dyadicSlack m j : ℝ) / (16 * B.slack)) := by
      convert Real.pow_rpow_inv_natCast (by positivity :
        0 ≤ E * (2 : ℝ) ^ ((dyadicSlack m j : ℝ) / (16 * B.slack)))
        (by decide : (4 : ℕ) ≠ 0) using 1
    rw [he] at hr
    apply hr.trans
    apply mul_le_mul_of_nonneg_left _ hE
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hslack : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
    exact div_le_self (Nat.cast_nonneg _) (by linarith)
  obtain ⟨F, hg, hraw, _⟩ := hprefix 0 (by omega)
  have hpre := compatible_growing_mean_pre_le hf.le hE m _ hroot
  have htail := compatible_growing_mean_tail_le hf hE HP.K m _ hroot
  have hrawpay := compatible_growing_mean_raw_le hf HP.K m radius
    (fun j => b j ^ (4⁻¹ : ℝ))
    (fun j hj => ⟨Real.rpow_nonneg (hb0 j) _, hroot j hj⟩)
  have hpow (j : ℕ) : (b j ^ (4⁻¹ : ℝ)) ^ 4 = b j := by
    convert Real.rpow_inv_natCast_pow (hb0 j) (by decide : (4 : ℕ) ≠ 0) using 1
  simp_rw [hpow] at hrawpay
  have hfinal := hroot (Nat.log2 M) (by dsimp only [m]; omega)
  rw [show dyadicSlack m (Nat.log2 M) = 1 from dyadicSlack_last (Nat.log2 M), pow_one] at hfinal
  refine ⟨?_, fun i hi => ⟨F i, hg i hi⟩, ?_, hpre, by linarith, hrawpay, htail, ?_⟩
  · intro i σ x y
    dsimp only [Δ, firstSignalIncrement, rawFirstPrefixes, requestSignals, m]
    simp only [Fin.isValue, ↓reduceIte, ht]
    by_cases hi : i = 0
    · subst i
      simp
    · rw [ite_eq_right hi, sum_range_succ]
      ring
  · rw [hdecoded m F hg le_rfl]
    exact hraw
  have htpaid := integrated_mean_tail_schedule r.source.role r.terminal.role hst.symm
    (side P ks) (side P ka) B.padding hD r.source.suffix r.terminal.suffix H hka
    (side_le P ka) G hG hf hNu hmass m (compatibleCapacity HP.K m) (fun _ => HP.K)
    (fun j _ => lt_of_lt_of_le (by positivity) (compatibleCapacity_bounds HP.K m j).2)
    Δ 0 μ (fun j => b j ^ (4⁻¹ : ℝ))
    (fun j _ => Real.rpow_nonneg (hb0 j) _) (fun j _ => by rw [hpow])
  have htpaid' : _ ≤ ((2 + 256 / floor) ^ (4⁻¹ : ℝ) * E / 63) ^ 4 :=
    htpaid.trans (pow_le_pow_left₀ (sum_nonneg fun j _ =>
      mul_nonneg (Real.rpow_nonneg (by
        have hfl := dyadicFloor_pos hf m j
        positivity) _) (sum_nonneg fun i _ =>
          mul_nonneg (by positivity) (Real.rpow_nonneg (hb0 i) _)))
      (by simpa only [mul_one] using htail) 4)
  simpa only [mul_one] using htpaid'

/-- Direct production consumer: positive-only own-request child comparisons at each
literal prefix, allowing different children at different endpoint budgets,
pay the actual first mean's four schedule components and actual
heavy-event tail. Intermediate completion availability is still separate. -/
theorem raw_residual_first_mean_schedule
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M ks ka : ℕ)
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
    (child : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (hrows : ∀ j < Nat.log2 M + 1, ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) →
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
          (B.sampleScale r (some i)))) q = some (child j i q))
    (hnrow : ∀ j < Nat.log2 M + 1, 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0))
        q = some (child j 0 q))
    (hdirect : ∀ j < Nat.log2 M + 1, ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1)
      j) B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) i (depth j i q) (ζ j i q) (floor j i q) q =
        some (child j i q))
    (hleft : ∀ j < Nat.log2 M + 1, ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) q = some (.row (child j i q)))
    (hright : ∀ j < Nat.log2 M + 1, ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
        (B.sampleScale r (some i)))) i (depth j i q) (ζ j i q) (floor j i q) q =
        some (child j i q))
    (hnegative : ∀ j < Nat.log2 M + 1, 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) q
        = some (.row (child j 0 q)))
    (hID : ∀ j < Nat.log2 M + 1, ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child j i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIL : ∀ j < Nat.log2 M + 1, ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child j i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIR : ∀ j < Nat.log2 M + 1, ∀ i ∈ B.bins, 0 < (LogSpaceEstimation.lastBudget M (dyadicSlack
      (Nat.log2 M + 1) j)
      B.slack (B.sampleScale r (some i))) → let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child j i q) (B.residualCanonicalChild i q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack
            (B.sampleScale r (some i)))) q)) ^ 4)
    (hIN : ∀ j < Nat.log2 M + 1, 0 < LogSpaceEstimation.lastBudget M
      (dyadicSlack (Nat.log2 M + 1) j) B.slack 0 → let q := (⟨HierarchyTask.correctionAtomTask 0
        false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child j 0 q) (B.residualCanonicalChild 0 q) ≤ ((2 : ℝ) ^ (-B.requestPrecision
          ((LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j) B.slack 0)) q)) ^ 4)
    (husage : r.usage = r.terminal) (htask : r.task = .residual 0)
    (hcharge : 1 ≤ B.rankCharge) (hp : 0 < B.requestPrecision M r)
    (hcalls : ∀ i < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) i
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C))
    (δ radius z : ℝ) (hδ : 0 < δ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ) :
    let m := Nat.log2 M + 1
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let X := retainedMask r.source.role (side P ks) B.padding r.source.suffix
    let Y := retainedMask r.terminal.role (side P ka) B.padding r.terminal.suffix
    let Δ := firstSignalIncrement (B.rawFirstPrefixes history M .residual r) ka second
    let μ := fun j x y => actualClippedMean HP r.source.role r.terminal.role
      (side P ks) (side P ka) (side P ka) B.padding r.source.suffix r.terminal.suffix
      ka G z Δ 0 0 j x y
    let b := fun j => rowNormPow 4 P r.source.rate X Y (fun _ => μ j)
    let E := residualRawMeanRootCost HP B.binCap * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge)
    (∀ i σ x y, Δ σ x i y 0 = requestSignals z B.padding id r
      ((B.completedGroup history M (dyadicSlack m i) .residual r).getD 0) 0 σ x y 0) ∧
    (∀ i < m, ∃ F, B.completedGroup history M (dyadicSlack m i) .residual r = some F) ∧
    B.raw history M .residual r = some (B.rawFirstPrefixes history M .residual r m) ∧
    (∑ j ∈ range m, dyadicFloor δ m j * b j ^ (4⁻¹ : ℝ)) ≤ δ * E / 511 ∧
    b (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤ 2 * E ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor δ m j ^ 4)) * b j) ≤
      (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * δ ^ 4)) * E ^ 4 / 63 ∧
    (∑ j ∈ range m,
      (((2 + 256 / dyadicFloor δ m j) / (compatibleCapacity HP.K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * b i ^ (4⁻¹ : ℝ)) ≤
      (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63 ∧
    vertexNormPow 4 P r.source.rate X (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent r.terminal.role B.padding r.terminal.suffix
        ka m j δ G (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
          meanRowTail r.terminal.role (side P ka) B.padding r.terminal.suffix m j μ σ x
        else 0) ≤ ((2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63) ^ 4 := by
  apply B.raw_residual_first_mean_schedule_of_prefix history M ks ka r hst hs ht hD H
    (hka.trans hks) hC hC1 δ radius z hδ second
  intro j hj
  exact B.raw_residual_prefix_clipped_le n hbins hrate hcutoff haux hD H hnH M j ks ka hj
    r hst hs ht hks hka hC hC1 hCf hcover hkh hlight hK history (child j) (depth j) (ζ j) (floor j)
    (hrows j hj) (hnrow j hj) (hdirect j hj) (hleft j hj) (hright j hj)
    (hnegative j hj) (hID j hj) (hIL j hj) (hIR j hj) (hIN j hj)
    husage htask hcharge hp hcalls

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
