/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRawMeanSchedule
public import Complexity.Foundations.Probability.HierarchyInitialIntegrated

/-!
# Reserve allocation for the literal RAW first mean

The decoder constants, floor, cap and primitive HP/bin-cap cost precede one
structural charge. Every larger charge still pays the primitive guard and the
first-mean separated reserve, before choosing fields, horizons, bin families,
exponents, budgets or precision. The scalar allocation reuses the existing
first-transport allocator rather than introducing another absorption lemma.

The production consumer applies `raw_residual_first_mean_schedule` to the actual
RAW history and `requestSignals`. Positive-only endpoint success and own-request
IH, and separate completion availability, remain explicit. The literal
stationary, final, rarity-weighted deterministic tail and raw payments are
inserted into `initialSeparatedReserve`, including its outer raw factor 64.
This is a conditional first-mean seam, not a complete initial reserve: second
mean, unconditional centered noise, joint recursion and native RL=L remain open.
No centered noise is rarity-discounted. These finite consumers are original;
allocation/compression proof patterns are adapted from Samuel Schlesinger.

## Main definitions

* `residualFirstMeanPayment`: the exact four-component first-mean envelope.

## Main results

* `exists_residualFirstMean_reserve_charge`: common charge with an arbitrary lower bound.
* `raw_residual_first_mean_reserve`: the actual RAW first-mean reserve consumer.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

/-- Exact first-mean reserve envelope. The radius is the production cap radius;
raw false-event payment retains both its `K + 1` gain and outer factor 64. -/
@[expose] def residualFirstMeanPayment (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre E : ℝ) : ℝ :=
  initialSeparatedReserve HP C Cpre (floor * E / 511) (2 * E)
    ((2 + 256 / floor) ^ (4⁻¹ : ℝ) * E / 63)
    (64 * (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
      ((HP.K + 1) * floor ^ 4)) * E ^ 4 / 63)

private theorem residualFirstMeanPayment_le_transport
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre E : ℝ) (hf : 0 < floor) (hE : 0 ≤ E) :
    residualFirstMeanPayment HP floor cap C Cpre E ≤
      initialFirstTransportPayment HP floor cap C Cpre (2 * E) := by
  have h8 : (1 : ℝ) ≤ 8 ^ (4⁻¹ : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hq : 0 ≤ (2 + 256 / floor) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (by positivity) _
  have he : E ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * (2 * E) := by nlinarith
  unfold residualFirstMeanPayment initialFirstTransportPayment
  apply initialSeparatedReserve_mono HP C Cpre
  · positivity
  · positivity
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_right he hf.le]
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right he hq]
  · have hW : 0 ≤ 64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((HP.K + 1) * floor ^ 4) := by positivity
    nlinarith [mul_nonneg hW (pow_nonneg hE 4)]

/-- One charge, above any requested lower bound, pays the primitive guard and the
exact first-mean reserve at every larger charge and every real precision. All
structural constants precede the charge; no field or execution is chosen here. -/
theorem exists_residualFirstMean_reserve_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap floor cap C Cpre : ℝ) (hcap : 0 ≤ binCap) (hf : 0 < floor) (lower : ℕ) :
    ∃ A : ℕ, lower ≤ A ∧ 1 ≤ A ∧ ∀ a : ℝ, (A : ℝ) ≤ a →
      residualRawMeanRootCost HP binCap * (2 : ℝ) ^ (-a) ≤ 1 ∧
      ∀ p : ℝ, residualFirstMeanPayment HP floor cap C Cpre
        (residualRawMeanRootCost HP binCap * (2 : ℝ) ^ (-p) * (2 : ℝ) ^ (-a)) ≤
        ((2 : ℝ) ^ (-p)) ^ 4 := by
  let L := residualRawMeanRootCost HP binCap
  have hL : 0 ≤ L := by
    dsimp only [L, residualRawMeanRootCost, residualDirectRootCost,
      residualProductNegativeRootCost, residualProductRootCost]
    have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
    have hgeo : 0 < 1 - (2 : ℝ) ^ (-3 / 4 : ℝ) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    positivity
  obtain ⟨A₀, hA₀, hprim⟩ := exists_residualRawMean_charge (HP := HP) binCap
  obtain ⟨A₁, halloc⟩ := initialFirstTransportPayment_exists_charge HP floor cap C Cpre (2 * L)
  refine ⟨max lower (max A₀ A₁), le_max_left _ _, hA₀.trans
    ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro a ha
  have hsmall (n : ℕ) (hn : n ≤ max lower (max A₀ A₁)) :
      (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hn' : (n : ℝ) ≤ max lower (max A₀ A₁) := by exact_mod_cast hn
      linarith)
  refine ⟨(mul_le_mul_of_nonneg_left (hsmall A₀
    ((le_max_left _ _).trans (le_max_right _ _))) hL).trans hprim, ?_⟩
  intro p
  have he : 0 ≤ L * (2 : ℝ) ^ (-p) * (2 : ℝ) ^ (-a) := by positivity
  apply (residualFirstMeanPayment_le_transport HP floor cap C Cpre _ hf he).trans
  apply le_trans _ (halloc ((2 : ℝ) ^ (-p)))
  apply initialFirstTransportPayment_mono HP floor cap C Cpre hf.le (by positivity)
  have hs := mul_le_mul_of_nonneg_left (hsmall A₁
    ((le_max_right _ _).trans (le_max_right _ _))) (by positivity : 0 ≤ 2 * L * (2 : ℝ) ^ (-p))
  dsimp only [L] at *
  nlinarith only [hs]

variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Pay the actual first mean in the existing separated reserve. `halloc` is
supplied uniformly by `exists_residualFirstMean_reserve_charge`, after fixing
structural constants and before this field/history. The tail is the actual
rarity-gated deterministic event, not centered noise. No other statistic is paid. -/
theorem raw_residual_first_mean_reserve
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
    (δ cap C Cpre z : ℝ) (hδ : 0 < δ)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (halloc : residualFirstMeanPayment HP δ cap C Cpre
      (residualRawMeanRootCost HP B.binCap * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)) ≤ ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4) :
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
    let tail := vertexNormPow 4 P r.source.rate X (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent r.terminal.role B.padding r.terminal.suffix
        ka m j δ G (compatibleCapacity HP.K m) (fun _ => HP.K) Δ 0 σ x then
          meanRowTail r.terminal.role (side P ka) B.padding r.terminal.suffix m j μ σ x
        else 0)
    (∀ i σ x y, Δ σ x i y 0 = requestSignals z B.padding id r
      ((B.completedGroup history M (dyadicSlack m i) .residual r).getD 0) 0 σ x y 0) ∧
    (∀ i < m, ∃ F, B.completedGroup history M (dyadicSlack m i) .residual r = some F) ∧
    B.raw history M .residual r = some (B.rawFirstPrefixes history M .residual r m) ∧
    initialSeparatedReserve HP C Cpre
      (∑ j ∈ range m, dyadicFloor δ m j * b j ^ (4⁻¹ : ℝ))
      (b (Nat.log2 M) ^ (4⁻¹ : ℝ)) (tail ^ (4⁻¹ : ℝ))
      (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) *
        ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor δ m j ^ 4)) * b j) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  extract_lets m G X Y Δ μ b tail
  let E := residualRawMeanRootCost HP B.binCap * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge)
  obtain ⟨hsignals, hgroups, hraw, hpre, hfinal, hrawpay, _htail, hmoment⟩ :=
    B.raw_residual_first_mean_schedule n hbins hrate hcutoff haux hD H hnH M ks ka r hst
      hs ht hks hka hC hC1 hCf hcover hkh hlight hK history child depth ζ floor
      hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN
      husage htask hcharge hp hcalls δ ((2 * max cap 16) ^ (4⁻¹ : ℝ)) z hδ second
  refine ⟨hsignals, hgroups, hraw, ?_⟩
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hb (j : ℕ) : 0 ≤ b j := rowNormPow_nonneg hNu _
  have htail0 : 0 ≤ tail := vertexNormPow_nonneg hNu _
  have hgeo : 0 < 1 - (2 : ℝ) ^ (-3 / 4 : ℝ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hcap := B.binCap_nonneg
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hE : 0 ≤ E := by
    dsimp only [E, residualRawMeanRootCost, residualDirectRootCost,
      residualProductNegativeRootCost, residualProductRootCost]
    positivity
  have ht : tail ^ (4⁻¹ : ℝ) ≤ (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63 := by
    have hh := Real.rpow_le_rpow htail0 hmoment (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    have hid : (((2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63) ^ 4) ^ (4⁻¹ : ℝ) =
        (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63 := by
      convert Real.pow_rpow_inv_natCast (by positivity :
        0 ≤ (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63) (by decide : (4 : ℕ) ≠ 0) using 1
    exact hh.trans_eq hid
  apply le_trans _ halloc
  change _ ≤ residualFirstMeanPayment HP δ cap C Cpre E
  unfold residualFirstMeanPayment
  apply initialSeparatedReserve_mono HP C Cpre
  · exact sum_nonneg fun j _ => mul_nonneg (dyadicFloor_nonneg hδ.le m j)
      (Real.rpow_nonneg (hb j) _)
  · exact Real.rpow_nonneg (hb _) _
  · exact Real.rpow_nonneg htail0 _
  · exact hpre
  · exact hfinal
  · exact ht
  · convert mul_le_mul_of_nonneg_left hrawpay (by norm_num : (0 : ℝ) ≤ 64) using 1; ring

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
