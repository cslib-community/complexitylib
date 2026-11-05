/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyTransportedPreparation
import Complexity.Foundations.Probability.HierarchyInitialMeanUniform

/-!
# Uniform allocation for the actual initial preparation mean

The actual second-mean minimum consumes the first clipped mean and centered first noise.
Its supported relative coefficient is fixed before the field, depth, endpoints and budget.
Slope-one growth is paid by the literal stationary floor, deterministic rarity tail and
raw false-event weights. The separate centered-noise slots receive no rarity discount.

Depth must cover the parent budget and the parent must have positive precision. These
conditional numerical payments do not prove child accuracy or availability, correction
products, or the native logarithmic-space realization.

## Main definitions

* `initialSecondMeanConstant`: a coefficient from primitive hierarchy and cutoff data.
* `initialComputedSecondMeanReserve`: the four literal second-mean allocations.

## Main results

* `initialComputedPrecisionMoment_secondMean_root_uniform_le`: actual rooted cost payment.
* `initialComputedPrecisionMoment_secondMean_schedule`: four actual weighted sums.
* `initialComputedSecondMeanReserve_exists_charge`: one fixed structural charge.
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

/-- The preparation coefficient and both first-coordinate currencies, before geometry.
The scale ζ and scalar regularity constants are fixed before selecting the charge. -/
@[expose] def initialSecondMeanConstant (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap coefficient ζ Lh Lρ : ℝ) : ℝ :=
  (8 * (2 * HP.K) * (|ζ| * preparationRelativeConstant HP Lh Lρ) ^ 4) ^ (4⁻¹ : ℝ) *
    ((8 : ℝ) ^ (4⁻¹ : ℝ) *
      ((max (512 * (6 * binCap + 3) ^ 3) (32768 * binCap ^ 3)) ^ (4⁻¹ : ℝ) *
        |coefficient| * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) +
          4 * (1 + 2 * binCap)) +
      2 * (initialNormalizedNoiseConstant binCap coefficient + 256 * binCap))

section Uniform
variable (B : BudgetData HP P) (hA : 1 ≤ B.rankCharge) (M n ks ka : ℕ)
  (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1)) (hhi : M ≤ 32 * B.slack * n)
  (H : Horizon P) (hn : n ≤ H.maxExponent) (hks : ks ≤ H.maxExponent)
  (hka : ka ≤ H.maxExponent)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
  (ss st : List (ZMod P))
  (hs : r.source = gridChannel R.source ks ss) (ht : r.terminal = gridChannel R.terminal ka st)
  (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (hp : 0 < B.requestPrecision M r)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
include hA hbins hrate hcutoff hhi hn hks hka hs ht htask hp hC hC1

/-- The actual supported second-mean minimum has slope-one growth. Both first statistics
are paid on full terminal rank; no inverse usage density or field width is introduced. -/
theorem initialComputedPrecisionMoment_secondMean_root_uniform_le
    (coefficient ζ Lh Lρ : ℝ) (j : ℕ) (hj : j < Nat.log2 M + 1) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j false 1 ^
        (4⁻¹ : ℝ) ≤
      initialSecondMeanConstant HP B.binCap coefficient ζ Lh Lρ *
        (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
          (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
  let e := (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let k := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
    |coefficient|
  let s := 4 * (1 + 2 * B.binCap)
  let z := 2 * (initialNormalizedNoiseConstant B.binCap coefficient + 256 * B.binCap)
  let D := 8 * (2 * HP.K) * (|ζ| * preparationRelativeConstant HP Lh Lρ) ^ 4
  let cost := B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ j
  have hcap := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hs0 : 0 ≤ s := by dsimp only [s]; positivity
  have hz : 0 ≤ z := by dsimp only [z, initialNormalizedNoiseConstant]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hcharge : 0 ≤ B.rankCharge := by linarith
  have hsrate : r.source.rate = rate ks := by rw [hs]; rfl
  have htrate : r.terminal.rate = rate ka := by rw [ht]; rfl
  have hrank : 1 ≤ r.task.rank := by
    rw [htask]
    norm_num [HierarchyTask.rank, BoundedRowTask.localTask, CorrectionRowTask.rank,
      PilotRowTask.rank, PilotTask.rank]
  have hM : 0 < M := (Nat.zero_le _).trans_lt
    (B.initial_coarse_scale_active hA M ks ka r hrank hrate hsrate htrate hp 0 (Nat.zero_le _))
  have hbinsH : ∀ bin ∈ B.bins, bin ≤ H.maxExponent := by
    intro bin hb
    rw [hbins, mem_range] at hb
    omega
  have hnonneg (noise : Bool) (ν : Fin 2) : 0 ≤ cost noise ν :=
    B.initialComputedPrecisionMoment_nonneg M n r (by rw [hsrate]; exact (rate_pos ks).le)
      R ks ka ss st coefficient ζ Lh Lρ j noise ν
  have hmean : cost false 0 ^ (4⁻¹ : ℝ) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * (k * E + s) * e *
        (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
    have hm := B.initialComputedPrecisionMoment_first_root_le hcharge hrate H M n j ks ka
      hka hbinsH r (by rw [hsrate]; exact (rate_pos ks).le) hsrate htrate htask R ss st
      coefficient ζ Lh Lρ
    have hw := B.initialClippedEndpointWindow_growing M j ka {r with usage := r.terminal}
    have hd := B.initialPolynomialLoss_root_uniform_le hA M n j ks ka hbins hrate hcutoff
      hhi H hks hka r hrank hsrate htrate hp hC hC1 R ss st
    apply hm.trans
    apply (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hw (by positivity)) hd) (by positivity)).trans_eq
    dsimp only [k, s, e, E]
    ring
  have hnoise : cost true 0 ^ (4⁻¹ : ℝ) ≤
      z * e * (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
    have hmin : cost true 0 ≤ B.initialComputedNormalizedNoise M r R ks ka ss st coefficient j := by
      have hadm : B.initialNormalizedNoiseAdmissible M r ka :=
        ⟨hcharge, hrate, htask, hp.le, H, hka, hbinsH⟩
      simp only [cost, initialComputedPrecisionMoment, initialComputedCenteredNoise,
        Bool.not_true, Bool.false_eq_true, false_and, ↓reduceIte, and_self, hadm]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hb := hmin.trans (B.initialComputedNormalizedNoise_polynomial_uniform_le hcharge
      hrate hcutoff H hbinsH M j ks ka hM hj r R ss st hs ht htask hka hp.le hC hC1 coefficient)
    have hb' : cost true 0 ≤
        (z * e * (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4 := by
      have hp' : B.requestPrecision M {r with usage := r.terminal} =
          B.requestPrecision M r := rfl
      simpa only [z, e, hp', mul_assoc] using hb
    have hroot := Real.rpow_le_rpow (hnonneg true 0) hb' (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    have hid : ((z * e * (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4) ^
        (4⁻¹ : ℝ) = z * e * (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
      convert Real.pow_rpow_inv_natCast (by positivity :
        0 ≤ z * e * (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j)
        (by decide : (4 : ℕ) ≠ 0) using 1
    have hroot' : cost true 0 ^ (4⁻¹ : ℝ) ≤
        z * e * (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
      exact hroot.trans_eq hid
    exact hroot'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) _)
      (mul_nonneg hz he))
  have hselector := B.initialComputedPrecisionMoment_secondMean_le M n r R ks ka ss st
    coefficient ζ Lh Lρ j
  change cost false 1 ≤ D * (cost false 0 + cost true 0) at hselector
  have hb := Real.rpow_le_rpow (hnonneg false 1) hselector (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rw [Real.mul_rpow hD (add_nonneg (hnonneg false 0) (hnonneg true 0))] at hb
  apply (hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_add_le_add_rpow (hnonneg false 0) (hnonneg true 0)
      (by norm_num) (by norm_num)) (Real.rpow_nonneg hD _))).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add hmean hnoise) (Real.rpow_nonneg hD _)).trans_eq
  dsimp only [initialSecondMeanConstant, D, k, E, s, z, e]
  ring

/-- All four literal allocations of the actual second-mean minimum. The tail is the
same deterministic rarity-weighted sum consumed by the two-coordinate reserve. -/
theorem initialComputedPrecisionMoment_secondMean_schedule
    (coefficient ζ Lh Lρ floor Rraw : ℝ) (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let x := initialSecondMeanConstant HP B.binCap coefficient ζ Lh Lρ *
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
    let b := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
      ζ Lh Lρ j false 1
    let a := fun j => b j ^ (4⁻¹ : ℝ)
    (∑ j ∈ range m, dyadicFloor floor m j * a j) ≤ floor * x / 511 ∧
    a (Nat.log2 M) ≤ 2 * x ∧
    (∑ j ∈ range m,
      (((2 + 256 / dyadicFloor floor m j) / (compatibleCapacity HP.K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a i) ≤
      (2 + 256 / floor) ^ (4⁻¹ : ℝ) * x / 63 ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * Rraw ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * b j) ≤
      (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) * x ^ 4 / 63 := by
  extract_lets m x b a
  have hcap := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hx : 0 ≤ x := by
    dsimp only [x, initialSecondMeanConstant, initialNormalizedNoiseConstant]
    positivity
  have hbn (j : ℕ) : 0 ≤ b j := B.initialComputedPrecisionMoment_nonneg M n r
    (by rw [hs]; exact (rate_pos ks).le) R ks ka ss st coefficient ζ Lh Lρ j false 1
  have hg (j : ℕ) (hj : j < m) : a j ≤ x * (2 : ℝ) ^ dyadicSlack m j :=
    B.initialComputedPrecisionMoment_secondMean_root_uniform_le hA M n ks ka
      hbins hrate hcutoff hhi H hn hks hka r R ss st hs ht htask hp hC hC1
      coefficient ζ Lh Lρ j hj
  have hpre := compatible_growing_mean_pre_le hf.le hx m a hg
  have htail := compatible_growing_mean_tail_le hf hx HP.K m a hg
  have hraw := compatible_growing_mean_raw_le hf HP.K m Rraw a
    (fun j hj => ⟨Real.rpow_nonneg (hbn j) _, hg j hj⟩)
  have hpow (j : ℕ) : a j ^ 4 = b j :=
    Real.rpow_inv_natCast_pow (hbn j) (by decide : (4 : ℕ) ≠ 0)
  simp_rw [hpow] at hraw
  have hfinal := hg (Nat.log2 M) (by dsimp only [m]; omega)
  have hd : dyadicSlack m (Nat.log2 M) = 1 := by simp [m, dyadicSlack]
  rw [hd, pow_one] at hfinal
  exact ⟨hpre, by simpa only [mul_comm] using hfinal, htail, hraw⟩

end Uniform

/-- The actual second-mean part of the two-coordinate separated reserve. Its four
payments use the literal false/one statistic, including its deterministic tail weight. -/
@[expose] def initialComputedSecondMeanReserve (B : BudgetData HP P) (M n : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (coefficient ζ Lh Lρ floor cap C Cpre : ℝ) : ℝ :=
  let m := Nat.log2 M + 1
  let b := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
    ζ Lh Lρ j false 1
  let a := fun j => b j ^ (4⁻¹ : ℝ)
  let Rraw := (2 * max cap 16) ^ (4⁻¹ : ℝ)
  initialSeparatedReserve HP C Cpre
    (∑ j ∈ range m, dyadicFloor floor m j * a j)
    (a (Nat.log2 M))
    (∑ j ∈ range m,
      (((2 + 256 / dyadicFloor floor m j) / (compatibleCapacity HP.K m j : ℝ)) ^
        (4⁻¹ : ℝ)) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * a i)
    (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) * Rraw ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * b j)

/-- A single charge, after the preparation scale and scalar regularity constants but
before any geometry, pays the four actual second-mean allocations. This certificate
retains budget/depth coverage and positive parent precision. Centered second noise and
the simultaneous recursive execution/accuracy induction remain separate. -/
theorem initialComputedSecondMeanReserve_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap coefficient ζ Lh Lρ floor cap C Cpre : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A → B.binRate = rate →
      B.cutoff = (fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
        rate 1 i (fun _ => 1)) →
      ∀ (M n ks ka : ℕ), B.bins = range (n + 1) → M ≤ 32 * B.slack * n →
      ∀ (H : Horizon P), n ≤ H.maxExponent → ks ≤ H.maxExponent → ka ≤ H.maxExponent →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
        (ss st : List (ZMod P)),
      r.source = gridChannel R.source ks ss → r.terminal = gridChannel R.terminal ka st →
      r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩) → 0 < B.requestPrecision M r →
      (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 →
      B.initialComputedSecondMeanReserve M n r R ks ka ss st coefficient ζ Lh Lρ
        floor cap C Cpre ≤ ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  let L := 2 * |initialSecondMeanConstant HP binCap coefficient ζ Lh Lρ|
  obtain ⟨A, hA⟩ := initialFirstTransportPayment_exists_charge HP floor cap C Cpre L
  refine ⟨A + 1, by omega, ?_⟩
  intro P _ B hcap hcharge hrate hcutoff M n ks ka hbins hhi H hn hks hka
    r R ss st hs ht htask hp hbase hrow
  have hcharge1 : 1 ≤ B.rankCharge := by rw [hcharge]; exact_mod_cast Nat.le_add_left 1 A
  let e := (2 : ℝ) ^ (-B.requestPrecision M r)
  let x := initialSecondMeanConstant HP B.binCap coefficient ζ Lh Lρ * e *
    (2 : ℝ) ^ (-B.rankCharge)
  let Rraw := (2 * max cap 16) ^ (4⁻¹ : ℝ)
  have hcap0 := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hx : 0 ≤ x := by
    dsimp only [x, e, initialSecondMeanConstant, initialNormalizedNoiseConstant]
    positivity
  have hscalar : 2 * x ≤ L * (2 : ℝ) ^ (-(A : ℝ)) * e := by
    have hsmall : (2 : ℝ) ^ (-B.rankCharge) ≤ (2 : ℝ) ^ (-(A : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hcharge]
      push_cast
      linarith
    have hcoef : 2 * initialSecondMeanConstant HP B.binCap coefficient ζ Lh Lρ ≤ L := by
      dsimp only [L]
      rw [hcap]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    calc
      _ = (2 * initialSecondMeanConstant HP B.binCap coefficient ζ Lh Lρ) *
          (2 : ℝ) ^ (-B.rankCharge) * e := by dsimp only [x]; ring
      _ ≤ L * (2 : ℝ) ^ (-B.rankCharge) * e := by gcongr
      _ ≤ _ := by dsimp only [L]; gcongr
  obtain ⟨hpre, hfinal, htail, hraw⟩ := B.initialComputedPrecisionMoment_secondMean_schedule
    hcharge1 M n ks ka hbins hrate hcutoff hhi H hn hks hka r R ss st hs ht htask hp
    hbase hrow coefficient ζ Lh Lρ floor Rraw hf
  let b := fun j => B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
    ζ Lh Lρ j false 1
  have hb (j : ℕ) : 0 ≤ b j := B.initialComputedPrecisionMoment_nonneg M n r
    (by rw [hs]; exact (rate_pos ks).le) R ks ka ss st coefficient ζ Lh Lρ j false 1
  have h8 : 1 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hpaid : B.initialComputedSecondMeanReserve M n r R ks ka ss st coefficient
      ζ Lh Lρ floor cap C Cpre ≤ initialFirstTransportPayment HP floor cap C Cpre (2 * x) := by
    unfold initialComputedSecondMeanReserve initialFirstTransportPayment
    apply initialSeparatedReserve_mono HP C Cpre
    · exact sum_nonneg fun j _ => mul_nonneg (dyadicFloor_nonneg hf.le _ _)
        (Real.rpow_nonneg (hb j) _)
    · exact Real.rpow_nonneg (hb _) _
    · exact sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg (by
          have hfl := dyadicFloor_pos hf (Nat.log2 M + 1) j
          positivity) _)
        (sum_nonneg fun i _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hb i) _))
    · apply hpre.trans
      have hh : x ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * (2 * x) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hh hf.le]
    · apply hfinal.trans
      nlinarith [mul_le_mul_of_nonneg_right h8 (show 0 ≤ 2 * x by positivity)]
    · apply htail.trans
      have hh : x ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * (2 * x) := by nlinarith
      have hq : 0 ≤ (2 + 256 / floor) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (by positivity) _
      nlinarith [mul_le_mul_of_nonneg_left hh hq]
    · apply (mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 64)).trans
      have hw : 0 ≤ 64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4) := by positivity
      change 64 * (_ * x ^ 4 / 63) ≤ _
      dsimp only [Rraw] at hw ⊢
      nlinarith [mul_nonneg hw (pow_nonneg hx 4)]
  exact hpaid.trans ((initialFirstTransportPayment_mono HP floor cap C Cpre hf.le
    (by positivity : 0 ≤ 2 * x) hscalar).trans (hA e))

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
