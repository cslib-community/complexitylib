/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialMeanUniform
public import Complexity.Foundations.Probability.HierarchyInitialSecondMeanAllocation
public import Complexity.Foundations.Probability.HierarchyInitialSecondNoiseAllocation

/-!
# Joint allocation of the four initial statistics

The existing first-coordinate, supported second-mean and sparse second-noise payments
share one structural charge. This module retains deterministic heavy-event rarity,
unconditional noise propagation and the literal raw false-event weights. Field coverage
is explicit. The result is numerical allocation for the initial row; successful recursive
children, the simultaneous invariant and native workspace bounds remain separate.
The assembly is original and reuses the existing finite fourth-moment estimates.

## Main definitions

* `initialComputedFourStatisticReserve`: the actual mixed-tail numerical reserve.

## Main results

* `initialComputedPrecisionMoment_secondNoise_schedule`: sparse noise in the actual minimum.
* `initialComputedFourStatisticReserve_exists_charge`: one charge for all four statistics.
* `initial_compressed_precision_reserve_fourStatistics`: the executed-history bridge.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- The actual computed second-noise minimum consumes all four scalar allocations. -/
theorem initialComputedPrecisionMoment_secondNoise_schedule (A : ℕ) (B : BudgetData HP P)
    (hfield : (512 * HP.K + 1) * 2 ^ (2 * A) ≤ P) (M n ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ss st : List (ZMod P)) (hs : r.source.rate = rate ks)
    (hadm : B.initialSecondNoiseAdmissible r R ks ka ss st)
    (hp : 0 ≤ B.requestPrecision M r) (coefficient ζ Lh Lρ floor radius : ℝ)
    (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let E := |ζ| * (1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-B.requestPrecision M r)
    let b := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
      ζ Lh Lρ j true 1
    (∑ j ∈ range m, dyadicFloor floor m j * b j ^ (4⁻¹ : ℝ)) ≤ floor * E / 511 ∧
    b (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤ E / 4 ∧
    (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * b j ^ (4⁻¹ : ℝ)) ≤ E * (458752 / 57) ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * b j) ≤
      (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)) * E ^ 4 / 63 := by
  extract_lets m E b
  have hb (j : ℕ) : b j ≤ B.initialSecondNoiseMoment M r ζ j :=
    B.initialComputedPrecisionMoment_secondNoise_le M n r R ks ka ss st
      coefficient ζ Lh Lρ j hadm
  have hbn (j : ℕ) : 0 ≤ b j := B.initialComputedPrecisionMoment_nonneg M n r
    (by rw [hs]; exact (rate_pos ks).le) R ks ka ss st coefficient ζ Lh Lρ j true 1
  have hroot (j : ℕ) : b j ^ (4⁻¹ : ℝ) ≤
      B.initialSecondNoiseMoment M r ζ j ^ (4⁻¹ : ℝ) :=
    Real.rpow_le_rpow (hbn j) (hb j) (by norm_num)
  obtain ⟨hp0, hf0, ht0, hr0⟩ := B.initialSecondNoiseMoment_schedule A hfield M ks r hs hp
    ζ floor radius hf
  refine ⟨?_, (hroot _).trans hf0, ?_, ?_⟩
  · exact (sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hroot j)
      (dyadicFloor_nonneg hf.le m j)).trans hp0
  · exact (sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hroot j) (by positivity)).trans ht0
  · apply le_trans (sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hb j) ?_) hr0
    have hfl := dyadicFloor_pos hf m j
    positivity

/-- All four actual computed statistics in the mixed-tail separated reserve. The two
means receive their literal heavy-event weights; neither centered noise does. The raw
coefficient 64 occurs once, outside the sum of the four moment allocations. -/
@[expose] def initialComputedFourStatisticReserve (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P))
    (coefficient ζ Lh Lρ floor cap C Cpre : ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let b := fun j noise ν => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
    ζ Lh Lρ j noise ν
  let a := fun j noise ν => b j noise ν ^ (4⁻¹ : ℝ)
  let radius := (2 * max cap 16) ^ (4⁻¹ : ℝ)
  initialSeparatedReserve HP C Cpre
    (B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor +
      ∑ j ∈ range m, dyadicFloor floor m j * (a j false 1 + (a j true 0 + a j true 1)))
    (B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient +
      (a (Nat.log2 M) false 1 + (a (Nat.log2 M) true 0 + a (Nat.log2 M) true 1)))
    ((B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor +
      ∑ j ∈ range m, (((2 + 256 / dyadicFloor floor m j) /
        (compatibleCapacity HP.K m j : ℝ)) ^ (4⁻¹ : ℝ)) *
        ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a i false 1) +
      ∑ i ∈ range m, (28 : ℝ) ^ (m - i) * (a i true 0 + a i true 1))
    (64 * (B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor radius +
      ∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) *
          (b j false 1 + (b j true 0 + b j true 1))))

/-- A common charge pays the actual four-statistic numerical reserve. All structural
constants, including preparation scale and regularity, are fixed before the charge;
field coverage, depth coverage and active initial-row requests are explicit afterwards.
Successful simultaneous recursion and native-space realization are not asserted. -/
theorem initialComputedFourStatisticReserve_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap coefficient ζ Lh Lρ floor cap C Cpre : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A → B.binRate = rate →
      B.cutoff = (fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
        rate 1 i (fun _ => 1)) → B.auxiliary = (fun _ => polynomialPrepCutoff4 HP.θ) →
      (512 * HP.K + 1) * 2 ^ (2 * A) ≤ P →
      ∀ (M n ks ka ku : ℕ), B.bins = range (n + 1) → M ≤ 32 * B.slack * n →
      ∀ (H : Horizon P), n ≤ H.maxExponent → ks ≤ H.maxExponent → ka ≤ H.maxExponent →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
        (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss → r.terminal = gridChannel R.terminal ka st →
      ka ≤ ku → r.usage = gridChannel R.terminal ku st →
      r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) → 0 < B.requestPrecision M r →
      (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 →
      B.initialComputedFourStatisticReserve M n r R ks ka ss st coefficient ζ Lh Lρ
        floor cap C Cpre ≤ ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let Lmean := 2 * ((max (512 * (6 * binCap + 3) ^ 3) (32768 * binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * E + 4 * (1 + 2 * binCap))
  let Lnoise := 2 * (initialNormalizedNoiseConstant binCap coefficient + 256 * binCap)
  let Lprep := initialSecondMeanConstant HP binCap coefficient ζ Lh Lρ
  let L := 2 * (|Lmean| + |Lnoise| + 2 * |Lprep| + |ζ|)
  obtain ⟨A, hA⟩ := initialFirstCoordinatePayment_exists_charge HP floor cap C Cpre L
  refine ⟨A + 1, by omega, ?_⟩
  intro P _ B hcap hcharge hrate hcutoff haux hfield M n ks ka ku hbins hhi H hn hks hka
    r R ss st hs ht husage hu htask hp hbase hrow
  let e := (2 : ℝ) ^ (-B.requestPrecision M r)
  let a := (2 : ℝ) ^ (-B.rankCharge)
  let x := 2 * (((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * e * a) * E + 4 * (1 + 2 * B.binCap) * e * a)
  let y := 2 * (initialNormalizedNoiseConstant B.binCap coefficient + 256 * B.binCap) * e * a
  let v := initialSecondMeanConstant HP B.binCap coefficient ζ Lh Lρ * e * a
  let w := |ζ| * a * e
  let z := L * (2 : ℝ) ^ (-(A : ℝ)) * e
  let radius := (2 * max cap 16) ^ (4⁻¹ : ℝ)
  let m := Nat.log2 M + 1
  have hcharge1 : 1 ≤ B.rankCharge := by rw [hcharge]; exact_mod_cast Nat.le_add_left 1 A
  have hcharge0 : 0 ≤ B.rankCharge := by linarith
  have hcap0 := B.binCap_nonneg
  have hsumE : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hx : 0 ≤ x := by dsimp only [x, e, a]; positivity
  have hy : 0 ≤ y := by dsimp only [y, initialNormalizedNoiseConstant, e, a]; positivity
  have hv : 0 ≤ v := by
    dsimp only [v, initialSecondMeanConstant, initialNormalizedNoiseConstant, e, a]
    positivity
  have hw : 0 ≤ w := by dsimp only [w, a, e]; positivity
  have hz : 0 ≤ z := by dsimp only [z, L, e]; positivity
  have hsmall : a ≤ (2 : ℝ) ^ (-(A : ℝ)) := by
    dsimp only [a]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hcharge]
    push_cast
    linarith
  have hsum : x + y + 2 * v + w ≤ z / 2 := by
    have hcoef : Lmean + Lnoise + 2 * Lprep + |ζ| ≤ L / 2 := by
      dsimp only [L]
      linarith [le_abs_self Lmean, le_abs_self Lnoise, le_abs_self Lprep]
    have hL : 0 ≤ L / 2 := by dsimp only [L]; positivity
    calc
      _ = (Lmean + Lnoise + 2 * Lprep + |ζ|) * a * e := by
        dsimp only [x, y, v, w, Lmean, Lnoise, Lprep]
        rw [hcap]
        ring
      _ ≤ (L / 2) * a * e := by
        have ha0 : 0 ≤ a * e := by dsimp only [a, e]; positivity
        nlinarith [mul_le_mul_of_nonneg_right hcoef ha0]
      _ ≤ (L / 2) * (2 : ℝ) ^ (-(A : ℝ)) * e :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hL) (by
          dsimp only [e]; positivity)
      _ = z / 2 := by dsimp only [z]; ring
  have hsrate : r.source.rate = rate ks := by rw [hs]; rfl
  have htrate : r.terminal.rate = rate ka := by rw [ht]; rfl
  have hrank : 1 ≤ r.task.rank := by
    rw [htask]
    norm_num [HierarchyTask.rank, BoundedRowTask.localTask, CorrectionRowTask.rank,
      PilotRowTask.rank, PilotTask.rank]
  have hM : 0 < M := (Nat.zero_le _).trans_lt
    (B.initial_coarse_scale_active hcharge1 M ks ka r hrank hrate hsrate htrate hp 0
      (Nat.zero_le _))
  have hbinsH : ∀ bin ∈ B.bins, bin ≤ H.maxExponent := by
    intro bin hb
    rw [hbins, mem_range] at hb
    omega
  obtain ⟨hm0, hm1, hm2, hm3⟩ := B.initialComputedFirstBudgets_uniform hcharge1
    M n ks ka hbins hrate hcutoff hhi H hks hka r hrank hsrate htrate hp hbase hrow
    R ss st coefficient floor radius hf
  obtain ⟨hn0, hn1, hn2, hn3⟩ := B.initialComputedPrecisionMoment_firstNoise_polynomial_schedule
    hcharge0 hrate hcutoff H hbinsH M n ks ka hM r R ss st hs ht htask hka hp.le hbase hrow
    coefficient ζ Lh Lρ floor radius hf
  obtain ⟨hv0, hv1, hv2, hv3⟩ := B.initialComputedPrecisionMoment_secondMean_schedule
    hcharge1 M n ks ka hbins hrate hcutoff hhi H hn hks hka r R ss st hs ht htask hp
    hbase hrow coefficient ζ Lh Lρ floor radius hf
  have hadm : B.initialSecondNoiseAdmissible r R ks ka ss st :=
    ⟨haux, hs, ht, ⟨H, hks⟩, ku, husage, hu⟩
  obtain ⟨hw0, hw1, hw2, hw3⟩ := B.initialComputedPrecisionMoment_secondNoise_schedule
    (A + 1) hfield M n ks ka r R ss st hsrate hadm hp.le coefficient ζ Lh Lρ floor radius hf
  have haeq : (1 / 2 : ℝ) ^ (A + 1) = a := by
    dsimp only [a]
    rw [hcharge, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    simp only [one_div, inv_pow]
  simp only [haeq] at hw0 hw1 hw2 hw3
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511 at hm0
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x at hm1
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 at hm2
  change _ ≤ 8 * x ^ 4 * (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)) / 63 at hm3
  change _ ≤ floor * y / 511 at hn0
  change _ ≤ y / 4 at hn1
  change _ ≤ y * (458752 / 57) at hn2
  change _ ≤ (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)) * y ^ 4 / 63 at hn3
  change _ ≤ floor * v / 511 at hv0
  change _ ≤ 2 * v at hv1
  change _ ≤ (2 + 256 / floor) ^ (4⁻¹ : ℝ) * v / 63 at hv2
  change _ ≤ (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)) * v ^ 4 / 63 at hv3
  change _ ≤ floor * w / 511 at hw0
  change _ ≤ w / 4 at hw1
  change _ ≤ w * (458752 / 57) at hw2
  change _ ≤ (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)) * w ^ 4 / 63 at hw3
  have h8 : 1 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hq : 0 ≤ (2 + 256 / floor) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (by positivity) _
  have hlin : (8 : ℝ) ^ (4⁻¹ : ℝ) * x + y + 2 * v + w ≤
      ((8 : ℝ) ^ (4⁻¹ : ℝ) + 1) * z := by
    have hxz : x ≤ z := by linarith only [hsum, hy, hv, hw, hz]
    have hrest : y + 2 * v + w ≤ z := by linarith only [hsum, hx, hz]
    nlinarith only [mul_le_mul_of_nonneg_left hxz
      (show 0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) by positivity), hrest]
  have htail : (8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 +
      (2 + 256 / floor) ^ (4⁻¹ : ℝ) * v / 63 +
      (y + w) * (458752 / 57) ≤
      ((8 : ℝ) ^ (4⁻¹ : ℝ) * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 + 458752 / 57) * z := by
    have hmean : (8 : ℝ) ^ (4⁻¹ : ℝ) * x + v ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * z := by
      have hxv : x + 2 * v ≤ z := by linarith only [hsum, hy, hw, hz]
      nlinarith only [mul_le_mul_of_nonneg_left hxv
        (show 0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) by positivity),
        mul_nonneg (sub_nonneg.mpr h8) hv, hv]
    have hyw : y + w ≤ z := by linarith only [hsum, hx, hv, hz]
    nlinarith only [mul_le_mul_of_nonneg_right hmean hq, hyw]
  have hp4 (u : ℝ) (hu : 0 ≤ u) (huz : u ≤ z / 2) : u ^ 4 ≤ z ^ 4 / 16 := by
    have hh := pow_le_pow_left₀ hu huz 4
    nlinarith only [hh]
  have hrawpow : 8 * x ^ 4 + y ^ 4 + v ^ 4 + w ^ 4 ≤ 9 * z ^ 4 := by
    have hx4 := hp4 x hx (by linarith only [hsum, hy, hv, hw])
    have hy4 := hp4 y hy (by linarith only [hsum, hx, hv, hw])
    have hv4 := hp4 v hv (by linarith only [hsum, hx, hy, hv, hw])
    have hw4 := hp4 w hw (by linarith only [hsum, hx, hy, hv])
    nlinarith only [hx4, hy4, hv4, hw4, pow_nonneg hz 4]
  obtain ⟨hpn, hfn, htn⟩ := B.initialComputedFirstBudgets_nonneg M n ks ka r
    (by rw [hsrate]; exact (rate_pos ks).le) R ss st coefficient floor hf.le
  have hnonneg (j : ℕ) (noise : Bool) (ν : Fin 2) :
      0 ≤ B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν :=
    B.initialComputedPrecisionMoment_nonneg M n r (by rw [hsrate]; exact (rate_pos ks).le)
      R ks ka ss st coefficient ζ Lh Lρ j noise ν
  have hroot (j : ℕ) (noise : Bool) (ν : Fin 2) :
      0 ≤ B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν ^
        (4⁻¹ : ℝ) := Real.rpow_nonneg (hnonneg j noise ν) _
  have hprePay : (8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511 +
      (floor * v / 511 + (floor * y / 511 + floor * w / 511)) ≤
      ((8 : ℝ) ^ (4⁻¹ : ℝ) + 1) * z * floor / 511 := by
    nlinarith only [mul_le_mul_of_nonneg_right hlin hf.le, mul_nonneg hv hf.le]
  have hfinalPay : (8 : ℝ) ^ (4⁻¹ : ℝ) * x + (2 * v + (y / 4 + w / 4)) ≤
      ((8 : ℝ) ^ (4⁻¹ : ℝ) + 1) * z := by nlinarith only [hlin, hy, hw]
  have htailPay : ((8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 +
      (2 + 256 / floor) ^ (4⁻¹ : ℝ) * v / 63) +
      (y * (458752 / 57) + w * (458752 / 57)) ≤
      ((8 : ℝ) ^ (4⁻¹ : ℝ) * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 + 458752 / 57) * z := by
    nlinarith only [htail]
  let W := 64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)
  have hrawPay : 64 * (8 * x ^ 4 * W / 63 +
      (W * v ^ 4 / 63 + (W * y ^ 4 / 63 + W * w ^ 4 / 63))) ≤
      64 * 9 * z ^ 4 * W / 63 := by
    have hW : 0 ≤ W := by dsimp only [W]; positivity
    nlinarith only [mul_le_mul_of_nonneg_left hrawpow hW]
  have hpaid : B.initialComputedFourStatisticReserve M n r R ks ka ss st coefficient
      ζ Lh Lρ floor cap C Cpre ≤ initialFirstCoordinatePayment HP floor cap C Cpre z := by
    unfold initialComputedFourStatisticReserve initialFirstCoordinatePayment
    dsimp only
    apply initialSeparatedReserve_mono HP C Cpre
    · exact add_nonneg hpn (sum_nonneg fun j _ => mul_nonneg (dyadicFloor_nonneg hf.le _ _)
        (add_nonneg (hroot j false 1) (add_nonneg (hroot j true 0) (hroot j true 1))))
    · exact add_nonneg hfn (add_nonneg (hroot _ false 1)
        (add_nonneg (hroot _ true 0) (hroot _ true 1)))
    · apply add_nonneg (add_nonneg htn ?_) ?_
      · exact sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg (by
          have hfl := dyadicFloor_pos hf m j
          positivity) _) (sum_nonneg fun i _ => mul_nonneg (by positivity) (hroot i false 1))
      · exact sum_nonneg fun i _ => mul_nonneg (by positivity)
          (add_nonneg (hroot i true 0) (hroot i true 1))
    · simpa only [mul_add, sum_add_distrib] using
        (add_le_add hm0 (add_le_add hv0 (add_le_add hn0 hw0))).trans hprePay
    · exact (add_le_add hm1 (add_le_add hv1 (add_le_add hn1 hw1))).trans hfinalPay
    · simpa only [mul_add, sum_add_distrib] using
        (add_le_add (add_le_add hm2 hv2) (add_le_add hn2 hw2)).trans htailPay
    · simpa only [W, radius, mul_add, sum_add_distrib] using
        (mul_le_mul_of_nonneg_left (add_le_add hm3 (add_le_add hv3 (add_le_add hn3 hw3)))
          (by norm_num : (0 : ℝ) ≤ 64)).trans hrawPay
  exact hpaid.trans (hA e)

section Execution
variable (B : BudgetData HP P) (M : ℕ) (hM : 0 < M) (n : ℕ)
  (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1)) (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
  (hD : B.padding ≠ 0) (H : Horizon P) (hn : n ≤ H.maxExponent)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
  (ks ka : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel R.source ks ss)
  (ht : r.terminal = gridChannel R.terminal ka st) (hks : ks ≤ H.maxExponent)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
include hM hbins hrate hcutoff haux hD hn hs ht hks hC hC1

/-- The unchanged executed groups and preparation list reach the named four-statistic
reserve. This consumes the second, mixed-tail conclusion of the existing execution
bound; final-payment monotonicity and nonnegative fourth-root identities are explicit. -/
theorem initial_compressed_precision_reserve_fourStatistics
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ) (ζ floor : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0) (coefficient : ℝ)
    (ih : ∀ bin ∈ B.bins, ∀ m < M, 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤ coefficient ^ 4 *
            ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ T, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some T)
    (bin ku : ℕ) (husage : ka ≤ ku) (hu : r.usage = gridChannel R.terminal ku st)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ)
    (hh : ∀ a b, |polynomialPrepCutoff4 HP.θ a - polynomialPrepCutoff4 HP.θ b| ≤ Lh * |a - b|)
    (hρ : ∀ a b, |HP.ρ a - HP.ρ b| ≤ Lρ * |a - b|)
    (hka : ka ≤ H.maxExponent) (hf : 0 < floor) (hcharge : 0 ≤ B.rankCharge)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (cap C Cpre : ℝ) :
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
          { r with usage := r.terminal }) = some groups ∧
      let F := fun p σ x y => ((groups.take p).map (fun T => T σ x y)).sum
      ∀ W, (List.range (Nat.log2 M + 1)).mapM (fun j =>
        B.complete M r (B.binPreparation bin r (F (j + 1)))
          (dyadicSlack (Nat.log2 M + 1) j)) = some W →
        B.initialFourMaxReserve M bin ka ζ floor r R ks ku ss st B.base F W cap C Cpre ≤
          B.initialComputedFourStatisticReserve M n r R ks ka ss st coefficient ζ Lh Lρ
            floor cap C Cpre := by
  obtain ⟨groups, hgroups, hpay⟩ := B.initial_compressed_precision_reserve M hM n hbins hrate
    hcutoff haux hD H hn r R ks ka ss st hs ht hks hC hC1 exponent ζ floor D hzero coefficient
    ih bin ku husage hu hLh hLρ hh hρ hka hf hcharge htask cap C Cpre
  refine ⟨groups, hgroups, ?_⟩
  dsimp only
  intro W hW
  have hsep := (hpay W hW).2.1
  have hr : 0 ≤ r.source.rate := by rw [hs]; exact (rate_pos ks).le
  have hnonneg (j : ℕ) (noise : Bool) (ν : Fin 2) :
      0 ≤ B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν :=
    B.initialComputedPrecisionMoment_nonneg M n r hr R ks ka ss st coefficient ζ Lh Lρ
      j noise ν
  have hpow (j : ℕ) (noise : Bool) (ν : Fin 2) :
      (B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν ^
        (4⁻¹ : ℝ)) ^ 4 =
          B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν :=
    Real.rpow_inv_natCast_pow (hnonneg j noise ν) (by decide : (4 : ℕ) ≠ 0)
  dsimp only at hsep
  simp_rw [hpow] at hsep
  apply hsep.trans
  unfold initialComputedFourStatisticReserve
  dsimp only
  obtain ⟨hpn, hfn, htn⟩ := B.initialComputedFirstBudgets_nonneg M n ks ka r hr R ss st
    coefficient floor hf.le
  have hcap := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hpayn : 0 ≤ B.initialComputedFirstFinalPayment M n r R ks ka ss st coefficient := by
    unfold initialComputedFirstFinalPayment
    split_ifs
    · exact le_min hfn (by positivity)
    · exact hfn
  have hroot (j : ℕ) (noise : Bool) (ν : Fin 2) :
      0 ≤ B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j noise ν ^
        (4⁻¹ : ℝ) := Real.rpow_nonneg (hnonneg j noise ν) _
  apply initialSeparatedReserve_mono HP C Cpre
  · exact add_nonneg hpn (sum_nonneg fun j _ => mul_nonneg (dyadicFloor_nonneg hf.le _ _)
      (add_nonneg (hroot j false 1) (add_nonneg (hroot j true 0) (hroot j true 1))))
  · exact add_nonneg hpayn (add_nonneg (hroot _ false 1)
      (add_nonneg (hroot _ true 0) (hroot _ true 1)))
  · apply add_nonneg (add_nonneg htn ?_) ?_
    · exact sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg (by
        have hfl := dyadicFloor_pos hf (Nat.log2 M + 1) j
        positivity) _) (sum_nonneg fun i _ => mul_nonneg (by positivity) (hroot i false 1))
    · exact sum_nonneg fun i _ => mul_nonneg (by positivity)
        (add_nonneg (hroot i true 0) (hroot i true 1))
  · exact le_rfl
  · exact add_le_add (B.initialComputedFirstFinalPayment_le M n r R ks ka ss st coefficient)
      le_rfl
  · exact le_rfl
  · exact le_rfl

end Execution

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
