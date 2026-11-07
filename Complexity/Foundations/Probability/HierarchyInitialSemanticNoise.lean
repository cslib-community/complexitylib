/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyInitialMeanPayment
import Complexity.Foundations.Probability.HierarchyInitialFeasibility

/-!
# Structural payment for semantic initial noise

A canonical initial sample is independent of its positive recursive budget. Its paired
input therefore vanishes unless the group slack straddles the zero-budget boundary.
Every nonzero input has slack at least half the parent budget. This extra spectral decay
pays the existing correlated-prefix cube and a structural rank salary, uniformly before
field width, the terminal exponent or the number of bins is chosen.

These original finite inequalities preserve the existing conditional-noise budget and
walk schedule. They do not prove simultaneous recursive availability or a native space bound.

## Main results

* `initialGroupInput_eq_zero_of_two_mul_lt`: cancellation at two positive endpoint budgets.
* `initialRelativeNoiseBudget_polynomial_uniform_le`: uniform payment of the existing budget.
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

/-- Both positive canonical endpoints are identical, including bins cut off at both ends. -/
theorem initialGroupInput_eq_zero_of_two_mul_lt (B : BudgetData HP P) (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hd : 2 * d < M) :
    B.initialGroupInput M d r = 0 := by
  funext σ x y
  unfold initialGroupInput
  apply sum_eq_zero
  intro bin _
  have hz : (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) = 0) ↔
      (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)) = 0) := by
    unfold LogSpaceEstimation.lastBudget
    omega
  by_cases hf : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) = 0
  · rw [ite_eq_left hf, ite_eq_left (hz.mp hf), sub_self]
  · rw [ite_eq_right hf, ite_eq_right (fun hc => hf (hz.mpr hc)), sub_self]

/-- The exact conditional summand already used by `initialRelativeNoiseBudget`. -/
@[expose] def initialRelativeGroupNoiseBudget (B : BudgetData HP P) (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P)) : ℝ :=
  let Xs := retainedMask s (side P ks) B.padding ss
  let Ya := retainedMask t (side P ka) B.padding st
  let graphV := graph s t hst (side P ks) (side P ka) (side_le P ks) (side_le P ka)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding st)
  let q := {r with usage := r.terminal}
  ((P : ℝ) * r.source.rate)⁻¹ * ∑ x, ∑ y,
    (({σ | Xs σ x ∧ Ya σ y} : Finset (Environment P 3)).dens : ℝ) *
      (2 * (graphV x y).spectralExpansion ^ (2 * B.steps M q d) *
        𝔼 σ ∈ ({σ | Xs σ x ∧ Ya σ y} : Finset (Environment P 3)),
          |(B.initialGroupInput M d q σ x y -
            rowSliceMean Xs Ya (B.initialGroupInput M d q) x y) /
              (rate ka + B.base x y)| ^ 4)

/-- Late semantic groups make no contribution to the existing conditional budget. -/
theorem initialRelativeGroupNoiseBudget_eq_zero (B : BudgetData HP P) (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P)) (hd : 2 * d < M) :
    B.initialRelativeGroupNoiseBudget M d r s t hst ks ka ss st = 0 := by
  simp [initialRelativeGroupNoiseBudget, B.initialGroupInput_eq_zero_of_two_mul_lt M d _ hd,
    rowSliceMean]

/-- The existing polynomial conditional estimate and unchanged spectral allocator pay
one actual semantic group. This is the per-group calculation in the earlier prefix bound. -/
theorem initialRelativeGroupNoiseBudget_polynomial_le (B : BudgetData HP P)
    (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hb : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (ha : ka ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1) :
    B.initialRelativeGroupNoiseBudget M d r s t hst ks ka ss st ≤
      (256 * B.binCap) ^ 4 *
        ((2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
          (64 : ℝ)⁻¹ ^ d) ^ 4 := by
  let C := (256 * B.binCap) ^ 4
  let ρ : ℝ := 1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4)
  let q := {r with usage := r.terminal}
  let T := B.steps M q d
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
  unfold initialRelativeGroupNoiseBudget
  dsimp only
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

private theorem inverse_four_pow (n : ℕ) :
    (1 / 4 : ℝ) ^ n = (2 : ℝ) ^ (-2 * (n : ℝ)) := by
  have hb : (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by norm_num [Real.rpow_neg]
  rw [hb, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

private theorem inverse_sixtyfour_pow (n : ℕ) :
    (64 : ℝ)⁻¹ ^ n = (2 : ℝ) ^ (-6 * (n : ℝ)) := by
  have hb : (64 : ℝ)⁻¹ = (2 : ℝ) ^ (-6 : ℝ) := by norm_num [Real.rpow_neg]
  rw [hb, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

omit [Fact P.Prime] in
/-- Positive parent precision bounds the structural salary by the parent budget. -/
theorem rankCharge_le_budget_of_initial_precision (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (M ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hp : 0 ≤ B.requestPrecision M r) : B.rankCharge ≤ M := by
  have hrank : (1 : ℝ) ≤ r.task.rank := by
    rw [htask]
    norm_num [HierarchyTask.rank, BoundedRowTask.localTask, CorrectionRowTask.rank,
      PilotRowTask.rank, PilotTask.rank]
  have hslack : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
  have hdiv : (M : ℝ) / (16 * B.slack) ≤ M :=
    div_le_self (Nat.cast_nonneg _) (by nlinarith)
  rw [B.requestPrecision_grid M ks ka r hs ht] at hp
  have hmul : B.rankCharge ≤ B.rankCharge * r.task.rank := by nlinarith
  have hks : (0 : ℝ) ≤ ks := by positivity
  have hka : (0 : ℝ) ≤ ka := by positivity
  linarith

/-- The original correlated-prefix cube is absorbed by the large slack of every nonzero
semantic group. Its constant is independent of width, terminal exponent and bin count. -/
theorem initialRelativeNoiseBudget_polynomial_uniform_le (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hb : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (M : ℕ) (hM : 0 < M) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) (ha : ka ≤ H.maxExponent)
    (hp : 0 ≤ B.requestPrecision M r)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (j : ℕ) (hj : j ≤ Nat.log2 M + 1) :
    B.initialRelativeNoiseBudget M r s t hst ks ka ss st B.base j ≤
      (256 * B.binCap * (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
        (2 : ℝ) ^ (-B.rankCharge) *
        (1 / 4 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) (j - 1)) ^ 4 := by
  let m := Nat.log2 M + 1
  let last := dyadicSlack m (j - 1)
  let e := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal})
  let T := 256 * B.binCap * e * (2 : ℝ) ^ (-B.rankCharge) * (1 / 4 : ℝ) ^ last
  let z := (2 : ℝ) ^ (-(M : ℝ))
  have hcap := B.binCap_nonneg
  have hT : 0 ≤ T := by dsimp only [T, e]; positivity
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hAM := B.rankCharge_le_budget_of_initial_precision hcharge M ks ka r
    (by rw [hs]; rfl) (by rw [ht]; rfl) htask hp
  have hjM : j ≤ M := by
    have hlog : Nat.log2 M < M := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_lt_self 2 hM.ne'
    omega
  have hjpow : (j : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast hjM.trans (Nat.lt_two_pow_self (n := M)).le
  have hsum (i : ℕ) (hi : i ∈ range j) :
      B.initialRelativeGroupNoiseBudget M (dyadicSlack m i) r s t hst ks ka ss st ≤
        (T * z) ^ 4 := by
    let d := dyadicSlack m i
    by_cases hd : 2 * d < M
    · rw [B.initialRelativeGroupNoiseBudget_eq_zero M d r s t hst ks ka ss st hd]
      positivity
    have hM2 : M ≤ 2 * d := by omega
    have hlast : last ≤ d := by
      dsimp only [last, d, dyadicSlack]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by have := mem_range.mp hi; omega)
    have hdecay : (64 : ℝ)⁻¹ ^ d ≤
        (2 : ℝ) ^ (-B.rankCharge) * (2 : ℝ) ^ (-(M : ℝ)) * (1 / 4 : ℝ) ^ last := by
      rw [inverse_sixtyfour_pow, inverse_four_pow,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have hm2 : (M : ℝ) ≤ 2 * d := by exact_mod_cast hM2
      have hl : (last : ℝ) ≤ d := by exact_mod_cast hlast
      linarith
    have hpoly := B.initialRelativeGroupNoiseBudget_polynomial_le hrate hcutoff H hb
      M d r s t hst ks ka ss st hs ht ha hC hC1
    apply hpoly.trans
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hh := mul_le_mul_of_nonneg_left hdecay
      (show 0 ≤ 256 * B.binCap * e by dsimp only [e]; positivity)
    calc
      _ = (256 * B.binCap * e) * (64 : ℝ)⁻¹ ^ d := by dsimp only [e]; ring
      _ ≤ 256 * B.binCap * e * ((2 : ℝ) ^ (-B.rankCharge) *
          (2 : ℝ) ^ (-(M : ℝ)) * (1 / 4 : ℝ) ^ last) := hh
      _ = T * z := by dsimp only [T, z]; ring
  unfold initialRelativeNoiseBudget
  dsimp only
  rw [min_eq_left hj]
  change (j : ℝ) ^ 3 * ∑ i ∈ range j,
    B.initialRelativeGroupNoiseBudget M (dyadicSlack m i) r s t hst ks ka ss st ≤ T ^ 4
  have hh := mul_le_mul_of_nonneg_left (sum_le_sum hsum)
    (show 0 ≤ (j : ℝ) ^ 3 by positivity)
  apply hh.trans
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hjz : (j : ℝ) * z ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hjpow hz
    have heq : (2 : ℝ) ^ M * z = 1 := by
      dsimp only [z]
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp
    exact h.trans_eq heq
  calc
    _ = (T * ((j : ℝ) * z)) ^ 4 := by ring
    _ ≤ T ^ 4 := pow_le_pow_left₀ (mul_nonneg hT (mul_nonneg (Nat.cast_nonneg _) hz))
      (mul_le_of_le_one_right hT hjz) 4

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
