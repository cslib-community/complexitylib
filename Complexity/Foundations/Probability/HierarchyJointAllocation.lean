/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRawMeanReserve
public import Complexity.Foundations.Probability.HierarchyDecoderAllocation

/-!
# Joint allocation of the first RAW mean and noise

Fix the primitive cap, decoder constants and positive floor before one charge.
Every larger charge pays the sum of the two first-coordinate separated numerical
contributions, with a sixteenth allowance for each. This is not the reserve of
an assembled overflow event: second-coordinate means, preparation, noise and
recursive availability remain separate obligations. Noise is unconditional.
The allocation is original, adapting Samuel Schlesinger's reserve formulas.

## Main results

* `exists_residualFirst_joint_charge`: charge before geometry, with a sixteenth for each part.
* `exists_prefix_joint_depth_family`: simultaneous slack-one budget and depth guards.
* `raw_residual_first_joint_reserve_le_payment`: both actual numerical contributions,
  preserving the literal RAW history and request signals.

The depth family fixes a request's exponents and identifiers; it does not cover
future identifier growth or all recursive requests. It supplies no execution or
noise-gate certificates. The returned primitive mean guard is useful to later
clients but is not used to replace any premise of the actual consumer.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Cslib Cslib.Probability Cslib.RowCompression

/-- One charge pays both contributions with an explicit budget split. The mean
uses the actual structural charge; the noise uses its natural allocation charge.
Neither the field nor the request nor the precision is fixed before this choice. -/
theorem exists_residualFirst_joint_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap floor cap C Cpre : ℝ) (hcap : 0 ≤ binCap) (hf : 0 < floor) (lower : ℕ) :
    ∃ A₀ : ℕ, lower ≤ A₀ ∧ 1 ≤ A₀ ∧ ∀ A ≥ A₀,
      residualRawMeanRootCost HP binCap * (2 : ℝ) ^ (-(A : ℝ)) ≤ 1 ∧
      ∀ p : ℝ,
        residualFirstMeanPayment HP floor cap C Cpre
          (residualRawMeanRootCost HP binCap * (2 : ℝ) ^ (-p) *
            (2 : ℝ) ^ (-(A : ℝ))) ≤ ((2 : ℝ) ^ (-p)) ^ 4 / 16 ∧
        residualFirstNoisePayment HP floor cap C Cpre
          ((1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-p)) ≤ ((2 : ℝ) ^ (-p)) ^ 4 / 16 := by
  obtain ⟨Am, hl, hmpos, hm⟩ := exists_residualFirstMean_reserve_charge
    HP binCap floor cap C Cpre hcap hf lower
  obtain ⟨An, _, hn⟩ := exists_residualFirstNoise_reserve_charge
    HP floor cap C Cpre hf lower
  refine ⟨max Am An + 1, hl.trans (by omega), by omega, ?_⟩
  intro A hA
  have hmA : Am ≤ A - 1 := by omega
  have hnA : An ≤ A - 1 := by omega
  have ha : 1 ≤ A := by omega
  have hcast : (A : ℝ) = (A - 1 : ℕ) + 1 := by exact_mod_cast (Nat.sub_add_cancel ha).symm
  have he (p : ℝ) : (2 : ℝ) ^ (-(p + 1)) = (2 : ℝ) ^ (-p) / 2 := by
    rw [neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
    ring
  have hnat (a : ℕ) : (1 / 2 : ℝ) ^ a = (2 : ℝ) ^ (-(a : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    simp only [one_div, inv_pow]
  refine ⟨(hm A (by exact_mod_cast (by omega : Am ≤ A))).1, ?_⟩
  intro p
  have hmean := (hm ((A - 1 : ℕ) : ℝ) (by exact_mod_cast hmA)).2 (p + 1)
  have hnoise := hn (A - 1) hnA (p + 1)
  have hid : (2 : ℝ) ^ (-p) * (2 : ℝ) ^ (-(A : ℝ)) =
      (2 : ℝ) ^ (-(p + 1)) * (2 : ℝ) ^ (-((A - 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hcast]
    congr 1; ring
  constructor
  · convert hmean using 1
    · congr 1
      nlinarith only [congrArg (fun x => residualRawMeanRootCost HP binCap * x) hid]
    · rw [he]; ring
  · rw [hnat (A - 1)] at hnoise
    rw [hnat A]
    convert hnoise using 1
    · congr 1
      nlinarith only [hid]
    · rw [he]; ring

/-- For the concrete slack-one schedule, every fixed request admits a growing
power-of-two budget family with simultaneous precision, cutoff-fit and omission
depth guards. The depth also covers all fixed exponents and identifiers. A field
and full bin family can be chosen after this depth; recursive calls are not supplied. -/
theorem exists_prefix_joint_depth_family
    {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (A : ℕ) (B : BudgetData HP P) (hslack : B.slack = 1)
    (ks ka ku idMax : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let M := 2 ^ N
      let n := M / 8 + 1
      ks ≤ n ∧ 2 * ka ≤ n ∧ ku ≤ n ∧ idMax < 2 ^ n ∧
      B.slack * (1 + 4 * (n + ka)) < M ∧ M ≤ 32 * B.slack * n ∧
      16 * (B.slack : ℝ) *
        (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
          A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M ∧
      0 < B.requestPrecision M r := by
  obtain ⟨N₀, hfamily⟩ := exists_prefix_budget_family A B ks ka r
  refine ⟨max N₀ (64 * (ks + ka + ku + idMax + 1)), ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hlarge : 64 * (ks + ka + ku + idMax + 1) ≤ N := (le_max_right _ _).trans hN
  have hNM := Nat.lt_two_pow_self (n := N)
  have hid : idMax ≤ 2 ^ N / 8 + 1 := by omega
  have hb := hfamily N hN₀
  have hp := B.requestPrecision_prefix_margin A (2 ^ N) ks ka r hs ht hb
  refine ⟨by omega, by omega, by omega, hid.trans_lt Nat.lt_two_pow_self, ?_, ?_, hb, ?_⟩
  · rw [hslack]
    omega
  · rw [hslack]
    omega
  · have hzero : (0 : ℝ) ≤ A := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ (Nat.log2 (2 ^ N) + 1 : ℕ) := Nat.cast_nonneg _
    linarith only [hp, hzero, hm]

variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)
open Finset NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

/-- The sum of the actual first clipped-mean and unconditional decoded-noise
numerical reserves, using the same RAW history, request, horizon and reference.
The endpoint calls, own-request IH and noise gates remain explicit. -/
theorem raw_residual_first_joint_reserve_le_payment
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
    (A : ℕ)
    (hbudget : 16 * (B.slack : ℝ) *
      (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
        A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M)
    (hg : ∀ j ∈ range (Nat.log2 M + 1), ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin)) → B.ResidualEndpointGates history m r bin) :
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
    let a := fun j => rowNormPow 4 P r.source.rate X Y
      (actualNoiseEntry r.source.role r.terminal.role (side P ks) (side P ka) (side P ka)
        B.padding r.source.suffix r.terminal.suffix ka G Δ 0 0 j)
    (∀ i σ x y, Δ σ x i y 0 = requestSignals z B.padding id r
      ((B.completedGroup history M (dyadicSlack m i) .residual r).getD 0) 0 σ x y 0) ∧
    (∀ i < m, ∃ F, B.completedGroup history M (dyadicSlack m i) .residual r = some F) ∧
    B.raw history M .residual r = some (B.rawFirstPrefixes history M .residual r m) ∧
    initialSeparatedReserve HP C Cpre
      (∑ j ∈ range m, dyadicFloor δ m j * b j ^ (4⁻¹ : ℝ))
      (b (Nat.log2 M) ^ (4⁻¹ : ℝ)) (tail ^ (4⁻¹ : ℝ))
      (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) *
        ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor δ m j ^ 4)) * b j)
      + initialSeparatedReserve HP C Cpre
        (∑ j ∈ range m, dyadicFloor δ m j * a j ^ (4⁻¹ : ℝ))
        (a (Nat.log2 M) ^ (4⁻¹ : ℝ))
        (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ))
        (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) *
          ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
          ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor δ m j ^ 4)) * a j) ≤
      residualFirstMeanPayment HP δ cap C Cpre
        (residualRawMeanRootCost HP B.binCap * (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (-B.rankCharge)) +
      residualFirstNoisePayment HP δ cap C Cpre
        ((1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-B.requestPrecision M r)) := by
  extract_lets m G X Y Δ μ b tail a
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
  have htailpaid : tail ^ (4⁻¹ : ℝ) ≤ (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63 := by
    have hh := Real.rpow_le_rpow htail0 hmoment (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    have hid : (((2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63) ^ 4) ^ (4⁻¹ : ℝ) =
        (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63 := by
      convert Real.pow_rpow_inv_natCast (by positivity :
        0 ≤ (2 + 256 / δ) ^ (4⁻¹ : ℝ) * E / 63) (by decide : (4 : ℕ) ≠ 0) using 1
    exact hh.trans_eq hid
  have hnoise := B.rawFirstPrefixes_decoded_noise_reserve_le_payment
    history M r r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
    (by change r.source = {r.source with rate := rate ks}; rw [← hs])
    (by change r.terminal = {r.terminal with rate := rate ka}; rw [← ht])
    husage hka (by intro i _; rw [hrate]) H hks hcalls G
    (HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC) second hg A hbudget
    δ cap C Cpre hδ
  apply add_le_add _ hnoise
  change _ ≤ residualFirstMeanPayment HP δ cap C Cpre E
  unfold residualFirstMeanPayment
  apply initialSeparatedReserve_mono HP C Cpre
  · exact sum_nonneg fun j _ => mul_nonneg (dyadicFloor_nonneg hδ.le m j)
      (Real.rpow_nonneg (hb j) _)
  · exact Real.rpow_nonneg (hb _) _
  · exact Real.rpow_nonneg htail0 _
  · exact hpre
  · exact hfinal
  · exact htailpaid
  · convert mul_le_mul_of_nonneg_left hrawpay (by norm_num : (0 : ℝ) ≤ 64) using 1; ring

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
