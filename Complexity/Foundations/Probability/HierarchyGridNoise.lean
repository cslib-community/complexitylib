/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRelativeNoise
public import Complexity.Foundations.Probability.SpectralPayment.Squared
import Complexity.Foundations.Probability.GridRowMoment.Rate

/-!
# Grid charges for transported residual noise

The production magnitude sums over terminal vertices. On rounded grids its
per-vertex charge is constant, including the reset factor in the product.
These original identities concern the existing allocator, without recursive IH.
Semantic boundary sampling and the final prefix reserve remain separate.

## Main results

* `positiveCharge_grid_eq`: exact direct and reset-product weights.
* `magnitude_grid_eq`: the terminal-vertex factor in the production allocator.
-/

public section
noncomputable section
open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Exact positive per-vertex charge, with the reset-right normalization cancelled
only after the actual channel density is substituted. No horizon is needed. -/
theorem positiveCharge_grid_eq
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka i : ℕ)
    (ht : r.terminal.rate = rate ka) (hi : B.binRate i = rate i) (y : ZMod P) :
    B.positiveCharge r i y =
      (rate i * gridMass P ka / gridMass P (max ka i)) * (2 * B.binCap) +
      (rate i * rate ka / gridMass P (max ka i)) *
        ((P : ℝ) * B.atomCap * (2 * B.binCap)) := by
  let R := HierarchyTask.rawRequests (k := HP.k) 0 i (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate i)
  have huD : R.direct.usage.rate = rate (max ka i) := by
    dsimp only [R, HierarchyTask.rawRequests]; rw [ht, hi, rate_min]
  have huR : R.right.usage.rate = rate (max ka i) := by
    dsimp only [R, HierarchyTask.rawRequests]; rw [ht, hi, rate_min]
  have hm : R.right.source.rate = rate ka := ht
  have hd := usageRatio_grid B.padding r.terminal R.direct ka (max ka i) ht huD y
  have hr := usageRatio_grid B.padding r.terminal R.right ka (max ka i) ht huR y
  have hz := (gridMass_pos (P := P) ka).ne'
  change |B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y| * _ +
    |B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal R.right y *
      (r.terminal.rate / (dens {τ | R.right.source.retains (channels B.padding) τ y} : ℝ))| * _ = _
  rw [hd, hr, channel_density B.padding R.right.source ka hm]
  change |B.binRate i * (gridMass P ka / gridMass P (max ka i))| * _ +
    |B.binRate i * (gridMass P ka / gridMass P (max ka i)) *
      (r.terminal.rate / gridMass P ka)| * _ = _
  rw [hi, ht]
  have he : rate i * (gridMass P ka / gridMass P (max ka i)) *
      (rate ka / gridMass P ka) = rate i * rate ka / gridMass P (max ka i) := by
    field_simp
  rw [he, abs_of_nonneg (mul_nonneg (rate_pos i).le (by unfold gridMass; positivity)),
    abs_of_nonneg (div_nonneg (mul_nonneg (rate_pos i).le (rate_pos ka).le)
      (by unfold gridMass; positivity))]
  ring

/-- Every terminal vertex has the same positive charge on grid rates. -/
theorem positiveCharge_grid_const
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka i : ℕ)
    (ht : r.terminal.rate = rate ka) (hi : B.binRate i = rate i) (y : ZMod P) :
    B.positiveCharge r i y = B.positiveCharge r i 0 := by
  rw [B.positiveCharge_grid_eq r ka i ht hi y, B.positiveCharge_grid_eq r ka i ht hi 0]

/-- The once-negative charge has terminal usage and therefore ratio one. -/
theorem negativeMagnitude_grid_eq
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ)
    (ht : r.terminal.rate = rate ka) :
    B.negativeMagnitude r = (P : ℝ) * (rate ka * B.atomCap) := by
  let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
      r.terminal, { r.terminal with rate := min r.terminal.rate r.terminal.rate }⟩
  have hu : q.usage.rate = rate ka := by simp [q, ht]
  have hz := (gridMass_pos (P := P) ka).ne'
  have hr (y : ZMod P) := usageRatio_grid B.padding r.terminal q ka ka ht hu y
  unfold negativeMagnitude
  change (∑ y, |r.terminal.rate *
    HierarchyTask.usageRatio (channels B.padding) r.terminal q y| * _) = _
  change ((side P ka : ℝ) / P) ^ 4 ≠ 0 at hz
  simp only [hr, div_self hz, mul_one, ht, abs_of_pos (rate_pos ka),
    sum_const, card_univ, ZMod.card, nsmul_eq_mul]

/-- Exact production identity: the finite bin charges are repeated at all P
vertices. The constant preparation and atom terms are retained. -/
theorem magnitude_grid_eq
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ)
    (ht : r.terminal.rate = rate ka) (hi : ∀ i ∈ B.bins, B.binRate i = rate i) :
    2 * (P : ℝ) * ((∑ i ∈ B.bins, B.positiveCharge r i 0) + rate ka * B.atomCap) =
      B.magnitude r - 1 - B.atomCap := by
  have hp (i : ℕ) (h : i ∈ B.bins) :
      B.positiveMagnitude r i = (P : ℝ) * B.positiveCharge r i 0 := by
    unfold positiveMagnitude
    simp only [B.positiveCharge_grid_const r ka i ht (hi i h), sum_const,
      card_univ, ZMod.card, nsmul_eq_mul]
  simp only [magnitude, sum_congr rfl hp, B.negativeMagnitude_grid_eq r ka ht, ← mul_sum]
  ring

/-- A pointwise table bound pays only the actual joint retained-pair mass.
The two distinct roles and horizon are explicit; the table may use every role. -/
theorem grid_row_moment_le_joint (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ)
    (ss st : List (ZMod P)) (H : Horizon P)
    (hs : ks ≤ H.maxExponent) (ha : ka ≤ H.maxExponent)
    (F : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hF : ∀ σ x y, |F σ x y| ≤ c) :
    rowNormPow 4 P (rate ks)
      (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
      (NormalizedMoments.retainedMask t (side P ka) B.padding st) F ≤
      256 * P * rate ka * c ^ 4 := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hd : gridMass P ks * gridMass P ka ≤ 256 * rate ks * rate ka := by
    have hh := mul_le_mul (gridMass_bounds H hs).2 (gridMass_bounds H ha).2
      (gridMass_pos (P := P) ka).le
      (mul_nonneg (by norm_num) (rate_pos ks).le)
    nlinarith only [hh]
  have hb := rowNormPow_le_mul (s := 4) (N := (P : ℝ)) (u := rate ks)
    (X := NormalizedMoments.retainedMask s (side P ks) B.padding ss)
    (Y := NormalizedMoments.retainedMask t (side P ka) B.padding st)
    (Z := F) (Z' := fun _ _ _ => c) (c := 1)
    (mul_nonneg hP.le (rate_pos ks).le) (fun σ x y _ _ => by
      rw [one_mul, abs_of_nonneg hc]
      exact pow_le_pow_left₀ (abs_nonneg _) (hF σ x y) 4)
  rw [one_mul, rowNormPow_const_eq_dens_sum] at hb
  simp_rw [grid_joint_density B.padding s t hst ks ka ss st,
    abs_of_nonneg hc] at hb
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at hb
  calc
    _ ≤ (↑P * rate ks)⁻¹ * (↑P * (↑P *
        (gridMass P ks * gridMass P ka * c ^ 4))) := hb
    _ ≤ (↑P * rate ks)⁻¹ * (↑P * (↑P *
        ((256 * rate ks * rate ka) * c ^ 4))) := by
      gcongr
      exact inv_nonneg.mpr (mul_nonneg hP.le (rate_pos ks).le)
    _ = _ := by field_simp [(rate_pos ks).ne', hP.ne']

/-- Keep the genuine decoder denominator inside the relative endpoint moment.
The explicit range premise can be supplied after successful gates have been
identified; it is not an accuracy or canonical-support assumption. -/
theorem residualSample_relative_fourth_le_of_abs
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (H : Horizon P) (hs : ks ≤ H.maxExponent) (ha : ka ≤ H.maxExponent)
    (E : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {c : ℝ} (hc : 0 ≤ c) (hE : ∀ σ x y, |E σ x y| ≤ 2 * c) :
    rowNormPow 4 P (rate ks)
      (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
      (NormalizedMoments.retainedMask t (side P ka) B.padding st)
      (fun σ x y => E σ x y / (rate ka + G x y)) ≤
      4096 * P * c ^ 4 / rate ka ^ 3 := by
  have hf := rate_pos ka
  have hh := B.grid_row_moment_le_joint s t hst ks ka ss st H hs ha
    (fun σ x y => E σ x y / (rate ka + G x y)) (by positivity : 0 ≤ 2 * c / rate ka)
    (fun σ x y => by
      rw [abs_div, abs_of_pos (add_pos_of_pos_of_nonneg hf (hG x y))]
      exact (div_le_div_of_nonneg_right (hE σ x y)
        (add_nonneg hf.le (hG x y))).trans
        (div_le_div_of_nonneg_left (by positivity) hf (by linarith [hG x y])))
  apply hh.trans_eq
  field_simp
  ring

/-- Centering costs sixteen, while the grid mass retains the terminal rate.
This is the assembled range route; no recursive accuracy hypothesis is used. -/
theorem residualTransported_centered_relative_fourth_le_of_abs
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (H : Horizon P) (hs : ks ≤ H.maxExponent) (ha : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (E : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (hE : ∀ σ x y, |E σ x y| ≤ 2 * B.magnitude r / P) :
    let X := NormalizedMoments.retainedMask s (side P ks) B.padding ss
    let Y := NormalizedMoments.retainedMask t (side P ka) B.padding st
    rowNormPow 4 P (rate ks) X Y
      (fun σ x y => (E σ x y - rowSliceMean X Y E x y) / (rate ka + G x y)) ≤
      65536 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3) := by
  dsimp only
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hh := B.residualSample_relative_fourth_le_of_abs s t hst ks ka ss st H hs ha
    E G hG (div_nonneg (B.magnitude_pos r).le hP.le)
    (fun σ x y => by simpa only [mul_div_assoc] using hE σ x y)
  have hcenter := rowNormPow_centered_sub_fourth_le
    (mul_nonneg hP.le (rate_pos ks).le)
    (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
    (NormalizedMoments.retainedMask t (side P ka) B.padding st)
    (fun σ x y => E σ x y / (rate ka + G x y)) 0
  simp only [rowSliceMean, Pi.zero_apply, expect_const_zero, sub_zero,
    ← expect_div, ← sub_div] at hcenter
  apply hcenter.trans ((mul_le_mul_of_nonneg_left hh (by norm_num)).trans_eq ?_)
  field_simp
  ring

omit [Fact P.Prime] in
/-- The admissible H4 horizon gives the fourth-power field comparison. It does
not give `1 ≤ P * rate ka`, which already fails at P=5, ka=2. -/
theorem one_le_field_fourth_mul_rate (H : Horizon P) {ka : ℕ}
    (ha : ka ≤ H.maxExponent) : 1 ≤ (P : ℝ) ^ 4 * rate ka := by
  have hn : 2 ^ ka ≤ P := (Nat.pow_le_pow_right (by decide) ha).trans H.side_admissible
  have hh : (2 : ℝ) ^ ka ≤ P := by exact_mod_cast hn
  have hp : 0 < (2 : ℝ) ^ ka := by positivity
  have h4 := pow_le_pow_left₀ hp.le hh 4
  rw [rate, inv_pow]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hp 4)).mpr (by simpa only [one_mul] using h4)

/-- The squared production coefficient pays the assembled transported range.
The horizon comparison is fourth-power, rather than an invalid lower bound on Pf. -/
theorem transported_range_squared_coefficient_le
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ks ka : ℕ)
    (hs : r.source.rate = rate ks) (hks : ka ≤ ks)
    (H : Horizon P) (ha : ka ≤ H.maxExponent) :
    (131072 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3)) /
      (32 * ((P : ℝ) ^ 2 / (P * r.source.rate) * B.magnitude r ^ 4) + 1) ^ 2 ≤ 64 := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast (Fact.out : P.Prime).two_le
  have hu := rate_pos ks
  have hf := rate_pos ka
  have hH := B.magnitude_pos r
  have hH4 := one_le_pow₀ (B.one_le_magnitude r) (n := 4)
  have huf := rate_antitone hks
  have hfP := one_le_field_fourth_mul_rate H ha
  have hsmall : 2 * rate ks ^ 2 ≤ (P : ℝ) ^ 5 * rate ka ^ 3 * B.magnitude r ^ 4 := by
    calc
      _ ≤ (P : ℝ) * rate ks ^ 2 := by gcongr
      _ ≤ (P : ℝ) * (rate ka ^ 2 * B.magnitude r ^ 4) := by
        gcongr
        exact (pow_le_pow_left₀ hu.le huf 2).trans
          (le_mul_of_one_le_right (by positivity) hH4)
      _ ≤ (P : ℝ) * ((P : ℝ) ^ 4 * rate ka) *
          (rate ka ^ 2 * B.magnitude r ^ 4) := by
        nlinarith only [mul_le_mul_of_nonneg_left hfP
          (show 0 ≤ (P : ℝ) * (rate ka ^ 2 * B.magnitude r ^ 4) by positivity)]
      _ = _ := by ring
  let C := 32 * ((P : ℝ) ^ 2 / (P * r.source.rate) * B.magnitude r ^ 4)
  have hC : 0 < C := by dsimp only [C]; rw [hs]; positivity
  calc
    _ ≤ (131072 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3)) / C ^ 2 := by
      change _ / (C + 1) ^ 2 ≤ _
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    _ = 128 * rate ks ^ 2 /
        ((P : ℝ) ^ 5 * rate ka ^ 3 * B.magnitude r ^ 4) := by
      dsimp only [C]
      rw [hs]
      field_simp
      ring
    _ ≤ 64 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hsmall]

/-- The unchanged production step count pays the transported range with eighth
power precision decay. This is per group; prefix summation remains unpaid. -/
theorem transported_range_spectral_payment
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ks ka : ℕ)
    (hs : r.source.rate = rate ks) (hks : ka ≤ ks)
    (H : Horizon P) (ha : ka ≤ H.maxExponent) :
    (131072 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3)) *
      (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)) ^ (2 * B.steps M r d) ≤
      64 * (((2 : ℝ) ^ (-B.requestPrecision M r)) * (64 : ℝ)⁻¹ ^ d) ^ 8 := by
  let C := 32 * ((P : ℝ) ^ 2 / (P * r.source.rate) * B.magnitude r ^ 4)
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hu := rate_pos ks
  have hf := rate_pos ka
  have hC : 0 ≤ C := by dsimp only [C]; rw [hs]; positivity
  have hh := spectralWalkLength_squared_payment
    (by norm_num : 0 < 1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4))
    (by norm_num : 1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4) < 1) hC
    (by positivity : 0 < (2 : ℝ) ^ (-B.requestPrecision M r))
    d (B.steps M r d) (Nat.le_max_right _ _)
  have hc := B.transported_range_squared_coefficient_le r ks ka hs hks H ha
  calc
    _ ≤ (131072 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3)) *
        ((((2 : ℝ) ^ (-B.requestPrecision M r)) * (64 : ℝ)⁻¹ ^ d) ^ 8 /
          (C + 1) ^ 2) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = ((131072 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3)) /
        (C + 1) ^ 2) *
        (((2 : ℝ) ^ (-B.requestPrecision M r)) * (64 : ℝ)⁻¹ ^ d) ^ 8 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- The literal direct/product recipe fits the production per-vertex charge
using only ranges. The unfiltered product costs P; no support inference is made. -/
theorem rawPositiveSample_abs_le_positiveCharge
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : ℕ)
    (child : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Matrix (ZMod P) (ZMod P) ℝ)
    (x y : ZMod P)
    (hD :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      |child Q.direct x y| ≤ 2 * B.binCap)
    (hL :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ z, |child Q.left x z| ≤ B.atomCap)
    (hR :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ z, |child Q.right z y| ≤ 2 * B.binCap) :
    |HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i) child x y| ≤ B.positiveCharge r i y := by
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)
  have hp : |∑ z, child Q.left x z * child Q.right z y| ≤
      (P : ℝ) * B.atomCap * (2 * B.binCap) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _z : ZMod P, B.atomCap * (2 * B.binCap) := by
        apply sum_le_sum
        intro z _
        rw [abs_mul]
        exact mul_le_mul (hL z) (hR z) (abs_nonneg _) (by
          unfold atomCap; exact mul_nonneg (by norm_num) (HP.Q_nonneg _))
      _ = _ := by simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; ring
  unfold HierarchyTask.rawPositiveSample
  dsimp only
  apply (abs_add_le _ _).trans
  have hd := mul_le_mul_of_nonneg_left hD (abs_nonneg
    (B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.direct y))
  have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg
    (B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal Q.right y *
      ((midpoint r).rate / (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ))))
  simpa only [positiveCharge, Q, HierarchyTask.usageRatio, HierarchyTask.rawRequests,
    midpoint, abs_mul] using add_le_add hd hh

/-- Both literal errors are charged, including exhausted endpoints against zero.
The premises are per-sample range bounds against the genuine canonical rays;
execution and the child gates that establish them remain explicit at callers. -/
theorem residualTransportedGroupInput_abs_le_magnitude_div
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka : ℕ)
    (ht : r.terminal.rate = rate ka) (hi : ∀ i ∈ B.bins, B.binRate i = rate i)
    (hE : ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) →
      ∀ σ x y, |(B.sample history m .residual r bin).getD 0 σ x y -
        B.residualCanonicalRay r bin σ x y| ≤
        2 * (match bin with
          | some i => B.positiveCharge r i 0
          | none => rate ka * B.atomCap)) :
    ∀ σ x y, |B.residualTransportedGroupInput history M d r σ x y| ≤
      2 * B.magnitude r / P := by
  let charge : Option ℕ → ℝ := fun bin => match bin with
    | some i => B.positiveCharge r i 0
    | none => rate ka * B.atomCap
  have hc (bin : Option ℕ) : 0 ≤ charge bin := by
    cases bin with
    | some i => exact B.positiveCharge_nonneg r i 0
    | none => exact mul_nonneg (rate_pos ka).le (by
        unfold atomCap; exact mul_nonneg (by norm_num) (HP.Q_nonneg _))
  let E := fun m bin σ x y => (B.sample history m .residual r bin).getD 0 σ x y -
    (if m = 0 then 0 else B.residualCanonicalRay r bin σ x y)
  have he (bin : Option ℕ) (hb : bin ∈ B.rays .residual) (m : ℕ)
      (hm : m = LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin))
      (σ x y) : |E m bin σ x y| ≤ 2 * charge bin := by
    by_cases hz : m = 0
    · subst m
      change |(0 : ℝ) - 0| ≤ 2 * charge bin
      rw [sub_self, abs_zero]
      exact mul_nonneg (by norm_num) (hc bin)
    · simpa only [E, hz, ↓reduceIte, charge] using hE bin hb m (by omega) hm σ x y
  have hsum : ((B.rays .residual).map charge).sum =
      (∑ i ∈ B.bins, B.positiveCharge r i 0) + rate ka * B.atomCap := by
    simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def, charge]
    rw [sum_map_toList]
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  intro σ x y
  change |((B.rays .residual).map (fun bin =>
    E (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) bin σ x y -
    E (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) bin σ x y)).sum| ≤ _
  have hbound : ∀ bin ∈ B.rays .residual,
      |E (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) bin σ x y -
       E (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) bin σ x y| ≤
      4 * charge bin := by
    intro bin hb
    exact (abs_sub _ _).trans (by
      linarith [he bin hb _ (Or.inl rfl) σ x y, he bin hb _ (Or.inr rfl) σ x y])
  have hconvert (v : Option ℕ → ℝ) :
      ((B.rays .residual).map v).sum = ∑ bin ∈ insert none (B.bins.image some), v bin := by
    rw [sum_insert (by simp), sum_image (fun _ _ _ _ h => Option.some.inj h)]
    simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
    rw [sum_map_toList]; ring
  rw [hconvert]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ bin ∈ insert none (B.bins.image some), 4 * charge bin := by
      apply sum_le_sum
      intro bin hb
      apply hbound
      simpa only [rays, List.mem_append, List.mem_map, mem_toList, List.mem_singleton,
        mem_insert, mem_image, eq_comm, or_comm] using hb
    _ = 4 * ((∑ i ∈ B.bins, B.positiveCharge r i 0) + rate ka * B.atomCap) := by
      rw [← mul_sum, ← hconvert, hsum]
    _ ≤ _ := by
      apply (le_div_iff₀ hP).mpr
      have hm := B.magnitude_grid_eq r ka ht hi
      have ha : 0 ≤ B.atomCap := by
        unfold atomCap; exact mul_nonneg (by norm_num) (HP.Q_nonneg _)
      nlinarith only [hm, ha]

/-- Production transported-noise budget from an assembled pointwise range.
The original graph, steps, denominator and correlated-prefix cube are retained.
This bound does not pay the semantic boundary or its final structural reserve. -/
theorem rawRelativeNoiseBudget_transported_le_of_abs
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hks : ka ≤ ks)
    (H : Horizon P) (hsource : ks ≤ H.maxExponent)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (j : ℕ)
    (hE : ∀ i ∈ range j, ∀ σ x y,
      |B.residualTransportedGroupInput history M (dyadicSlack (Nat.log2 M + 1) i) r σ x y| ≤
        2 * B.magnitude r / P) :
    B.rawRelativeNoiseBudget M r s t hst ks ka ss st
      (fun i => B.residualTransportedGroupInput history M
        (dyadicSlack (Nat.log2 M + 1) i) r) G j ≤
      (j : ℝ) ^ 3 * ∑ i ∈ range j,
        64 * (((2 : ℝ) ^ (-B.requestPrecision M r)) *
          (64 : ℝ)⁻¹ ^ dyadicSlack (Nat.log2 M + 1) i) ^ 8 := by
  let ρ : ℝ := 1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)
  have hρ : 0 ≤ ρ := by norm_num [ρ]
  let cost := 65536 * B.magnitude r ^ 4 / ((P : ℝ) ^ 3 * rate ka ^ 3)
  have hcost : 0 ≤ cost := by
    dsimp only [cost]
    exact div_nonneg (by positivity)
      (mul_nonneg (by positivity) (pow_nonneg (rate_pos ka).le _))
  have hbound := B.rawRelativeNoiseBudget_le_of_centered_fourth M r s t hst ks ka ss st
    hs (fun i => B.residualTransportedGroupInput history M
      (dyadicSlack (Nat.log2 M + 1) i) r) G j (fun _ => cost) (by
        intro i hi
        rw [show r.source.rate = rate ks by rw [hs]; rfl]
        exact B.residualTransported_centered_relative_fourth_le_of_abs s t hst ks ka ss st
          H hsource (hks.trans hsource) r _ G hG (hE i hi))
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro i _
  let d := dyadicSlack (Nat.log2 M + 1) i
  have hw : ‖fun xy : ZMod P × ZMod P => 2 *
      (graph s t hst (side P ks) (side P ka) (side_le P ks) (side_le P ka)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding st)
        xy.1 xy.2).spectralExpansion ^ (2 * B.steps M r d)‖ ≤
      2 * ρ ^ (2 * B.steps M r d) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro xy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg (RotationMap.spectralExpansion_nonneg _) _))]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (RotationMap.spectralExpansion_nonneg _)
    unfold graph
    rw [RotationMap.spectralExpansion_reindex, RotationMap.spectralExpansion_reindex]
    exact spectralExpansion_lazy_ofPerms_componentMove_le (by decide)
  apply (mul_le_mul_of_nonneg_right hw hcost).trans
  have hh := B.transported_range_spectral_payment M d r ks ka
    (by rw [hs]; rfl) hks H (hks.trans hsource)
  convert hh using 1
  dsimp only [cost]
  ring

/-- Genuine final correction range, including the actual final source-child
iteration and the zero result on invalid requests. -/
theorem residualCanonicalChild_correction_abs_le (i : ℕ)
    (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (htask : q.task = HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k))
    (σ : Environment P 3) (x y : ZMod P) :
    |B.residualCanonicalChild i q σ x y| ≤ B.atomCap := by
  unfold residualCanonicalChild canonicalRequestChild
  rw [htask, HierarchyTask.correctionAtomTask_last HP.k_pos]
  dsimp only
  split_ifs with hr
  · have hh := selectedRequest_mem_Icc HP B.padding id q
      ⌈4 * (1 + 32 * HP.R)⌉₊
      (fun _ => stageRaw HP B.padding id q hr B.base (HP.k - 1))
      (sourcePreparation HP B.padding id q hr B.base (HP.k - 1))
      (fun _ => stageMaximum HP B.padding id q hr B.base) σ x y
    exact (abs_of_nonneg hh.1).trans_le hh.2
  · change |(0 : ℝ)| ≤ _
    rw [abs_zero]
    exact mul_nonneg (by norm_num) (HP.Q_nonneg _)

/-- Genuine bin ranges follow from the same bounded dense normalizer as the
executed compressed-bin gates, independently of earlier accuracy. -/
theorem residualCanonicalChild_dense_abs_le (i : ℕ)
    (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (l j : ℕ)
    (htask : q.task = .baseNormalized l j)
    (σ : Environment P 3) (x y : ZMod P) :
    |B.residualCanonicalChild i q σ x y| ≤ 2 * B.binCap := by
  simp only [residualCanonicalChild, canonicalRequestChild, htask]
  exact denseChild_range B.padding id q B.base (B.cutoff i) (B.auxiliary i) HP.ρ HP.K
    B.binCap_nonneg (B.cutoff_bounds i) (fun d => ⟨HP.ρ_nonneg d, HP.ρ_le_one d⟩) σ x y

/-- Actual positive endpoint error against its genuine canonical ray. Successful
whole-row lookups and the three gate ranges are explicit; no IH is needed. -/
theorem positiveSample_residual_error_le_of_gates
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (m i : ℕ) (hm : 0 < m) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (child : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hrows :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _), row history m q = some (child q))
    (hD :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x y, |child Q.direct σ x y| ≤ 2 * B.binCap)
    (hL :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ x z, |child Q.left σ x z| ≤ B.atomCap)
    (hR :
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ σ z y, |child Q.right σ z y| ≤ 2 * B.binCap) :
    ∀ σ x y, |(B.sample history m .residual r (some i)).getD 0 σ x y -
      B.residualCanonicalRay r (some i) σ x y| ≤ 2 * B.positiveCharge r i y := by
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)
  intro σ x y
  rw [sample, ite_eq_right (by omega), B.positiveSample_of_rows history m i .residual r child hrows,
    Option.getD_some]
  apply (abs_sub _ _).trans
  have ha := B.rawPositiveSample_abs_le_positiveCharge r i (fun q => child q σ) x y
    (hD σ x y) (hL σ x) (fun z => hR σ z y)
  have hc := B.rawPositiveSample_abs_le_positiveCharge r i
    (fun q => B.residualCanonicalChild i q σ) x y
    (B.residualCanonicalChild_dense_abs_le i Q.direct _ _ rfl σ x y)
    (fun z => B.residualCanonicalChild_correction_abs_le i Q.left rfl σ x z)
    (fun z => B.residualCanonicalChild_dense_abs_le i Q.right _ _ rfl σ z y)
  change _ + |HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)
    (fun q => B.residualCanonicalChild i q σ) x y| ≤ _
  linarith only [ha, hc]

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
