/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyTransportedPreparation
public import Complexity.Foundations.Probability.GridRowMoment.JointDensity
import Complexity.Foundations.Probability.GridRowMoment.Rate
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Uniform true-mass payments for initial conditional means

The actual polynomial deficit is a subtable of the nonnegative substochastic base.
Integrating its true mass over the two independent endpoint grids removes field width
from its fourth moment. A least inactive bin bounds the omitted ratio-16 rate tail.
The retained depth still has to cover the parent budget; fixed depth cannot support
arbitrarily large budgets. These original fourth-moment estimates implement the true-mass
mechanism of [OpenAI2026LogSpace, Lemma 7.4, p. 37, and Lemma 7.6, pp. 40–41],
revision `7ef5c0cc`, with explicit grid rounding. The source uses eighth moments and
covers general table, vector and correction tasks; this module proves fourth-moment
initial-row estimates on the ratio-16 grid with `M ≤ 32 * slack * n` depth coverage.
It does not formalize the full recursive Lemma 7.6 or supply child availability or
second preparation.

## Main results

* `initialPolynomialLoss_le_base`: the actual semantic deficit is bounded by true mass.
* `initialInactiveCharge_fine_tail_le`: a bin-count-independent literal inactive tail.
* `initialPolynomialLoss_root_uniform_le`: the semantic schedule with uniform constant.
* `initialComputedFirstBudgets_uniform`: all four actual first-mean budget consumers.
* `initialComputedFirstBudgets_uniform_exists_charge`: one charge pays their separated reserve.
* `initialComputedFirstCoordinateReserve_uniform_exists_charge`: complete first-coordinate reserve.
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

/-- The literal omitted and inactive polynomial mass is a subtable of the base.
This includes temporally inactive prefixes and needs no activity hypothesis. -/
theorem initialPolynomialLoss_le_base (B : BudgetData HP P) (M n j : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1) (x y : ZMod P) :
    B.initialPolynomialLoss M n j r x y ≤ B.base x y := by
  have hf : B.initialFineLoss M (Nat.log2 M + 1) j r x y ≤
      ∑ i ∈ B.bins, B.binRate i * B.cutoff i (B.base x y / B.binRate i) := by
    apply sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by rw [hrate]; exact (rate_pos i).le) (B.cutoff_bounds i _).1
  rw [B.initialBins_polynomial_sum n hbins hrate hcutoff hC hC1 x y] at hf
  unfold initialPolynomialLoss
  rw [B.initialCoarseLoss_eq_zero, add_zero]
  linarith

/-- Application-specific true-mass integration on the two actual rounded grids. -/
private lemma grid_trueMass_le (B : BudgetData HP P) (R : RoleProfile 3)
    (ks ka : ℕ) (ss st : List (ZMod P)) (H : Horizon P)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (hC1 : B.base *ᵥ 1 ≤ 1)
    (v : ZMod P → ZMod P → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ x y, |v x y| ^ 4 ≤ c * B.base x y) :
    rowNormPow 4 P (rate ks)
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st) (fun _ => v) ≤
        256 * rate ka * c := by
  have hsp := rate_pos ks
  have hap := rate_pos ka
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hd : gridMass P ks * gridMass P ka ≤ 256 * rate ks * rate ka := by
    have hs := (gridMass_bounds H hks).2
    have ht := (gridMass_bounds H hka).2
    have hsn : 0 ≤ gridMass P ks := by unfold gridMass; positivity
    nlinarith [mul_le_mul hs ht (by unfold gridMass; positivity) (by positivity)]
  rw [rowNormPow_const_eq_dens_sum]
  simp_rw [grid_joint_density B.padding R.source R.terminal R.source_terminal]
  calc
    _ ≤ ((P : ℝ) * rate ks)⁻¹ * ∑ x, ∑ y,
        (256 * rate ks * rate ka) * (c * B.base x y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum fun x _ => sum_le_sum fun y _ =>
        mul_le_mul hd (hv x y) (by positivity) (by positivity)
    _ = ((P : ℝ) * rate ks)⁻¹ * (256 * rate ks * rate ka * c) *
        ∑ x, ∑ y, B.base x y := by simp only [← mul_sum]; ring
    _ ≤ ((P : ℝ) * rate ks)⁻¹ * (256 * rate ks * rate ka * c) * P := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hr (x : ZMod P) : ∑ y, B.base x y ≤ 1 := by
        simpa only [mulVec, dotProduct, Pi.one_apply, mul_one] using hC1 x
      simpa only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one] using
        sum_le_sum (fun x (_ : x ∈ (univ : Finset (ZMod P))) => hr x)
    _ = _ := by field_simp [(rate_pos ks).ne', hP.ne']

/-- A substochastic base pays a clipped deterministic subtable independently of width. -/
theorem initialPolynomialLoss_row_le (B : BudgetData HP P) (M n j ks ka : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : r.source.rate = rate ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (R : RoleProfile 3) (ss st : List (ZMod P)) :
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
        (rate ka + B.base x y))) ≤ 256 := by
  have hap := rate_pos ka
  rw [hs]
  have h := B.grid_trueMass_le R ks ka ss st H hks hka hC1
    (fun x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
      (rate ka + B.base x y))) (c := (rate ka)⁻¹) (by positivity) ?_
  · simpa only [mul_assoc, mul_inv_cancel₀ (rate_pos ka).ne', mul_one] using h
  intro x y
  have hxy := hC x y
  let z := min 1 (|B.initialPolynomialLoss M n j r x y| / (rate ka + B.base x y))
  have hz : 0 ≤ z := le_min (by norm_num) (div_nonneg (abs_nonneg _)
    (by positivity))
  have hz1 : z ≤ 1 := min_le_left _ _
  have hzC : z ≤ B.base x y / rate ka := by
    apply (min_le_right _ _).trans
    rw [abs_of_nonneg (B.initialPolynomialLoss_nonneg M n j r hrate hC x y)]
    exact (div_le_div_of_nonneg_right
      (B.initialPolynomialLoss_le_base M n j hbins hrate hcutoff r hC hC1 x y)
      (by positivity)).trans (div_le_div_of_nonneg_left (hC x y) (rate_pos ka)
        (le_add_of_nonneg_right (hC x y)))
  rw [abs_of_nonneg hz]
  have hp : z ^ 4 ≤ z := by
    nlinarith [sq_nonneg z, sq_nonneg (z ^ 2), mul_nonneg hz (sub_nonneg.mpr hz1),
      mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz1),
      mul_nonneg (by positivity : 0 ≤ z ^ 3) (sub_nonneg.mpr hz1)]
  simpa only [div_eq_mul_inv, mul_comm] using hp.trans hzC

/-- True mass gives the cubic fine-entry cost for the actual clipped deficit. -/
theorem initialPolynomialLoss_row_entry_le (B : BudgetData HP P) (M n j ks ka : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (H : Horizon P) (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hs : r.source.rate = rate ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (R : RoleProfile 3) (ss st : List (ZMod P)) {b : ℝ} (hb : 0 ≤ b)
    (hentry : ∀ x y, B.initialPolynomialLoss M n j r x y ≤ b) :
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
        (rate ka + B.base x y))) ≤ 256 * (b / rate ka) ^ 3 := by
  have hap := rate_pos ka
  rw [hs]
  have h := B.grid_trueMass_le R ks ka ss st H hks hka hC1
    (fun x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
      (rate ka + B.base x y))) (c := b ^ 3 / rate ka ^ 4) (by positivity) ?_
  · convert h using 1; field_simp
  intro x y
  have hxy := hC x y
  let L := B.initialPolynomialLoss M n j r x y
  have hL : 0 ≤ L := B.initialPolynomialLoss_nonneg M n j r hrate hC x y
  have hLC : L ≤ B.base x y :=
    B.initialPolynomialLoss_le_base M n j hbins hrate hcutoff r hC hC1 x y
  have hLb : L ≤ b := hentry x y
  have hz : 0 ≤ min 1 (|L| / (rate ka + B.base x y)) := by positivity
  have hzL : min 1 (|L| / (rate ka + B.base x y)) ≤ L / rate ka := by
    apply (min_le_right _ _).trans
    rw [abs_of_nonneg hL]
    exact div_le_div_of_nonneg_left hL hap (le_add_of_nonneg_right hxy)
  calc
    _ ≤ (L / rate ka) ^ 4 := by
      rw [abs_of_nonneg hz]
      exact pow_le_pow_left₀ hz hzL 4
    _ = L ^ 3 * L / rate ka ^ 4 := by rw [div_pow]; ring
    _ ≤ b ^ 3 * B.base x y / rate ka ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ hL hLb 3) hLC hL (by positivity)
    _ = _ := by ring

omit [Fact P.Prime] in
private lemma rate_ratio_rpow (ka bin : ℕ) :
    rate bin / rate ka = (2 : ℝ) ^ (4 * ((ka : ℝ) - bin)) := by
  have he (k : ℕ) : rate k = (2 : ℝ) ^ (-4 * (k : ℝ)) := by
    rw [rate_eq_source_grid]
    rw [show (16⁻¹ : ℝ) = (2 : ℝ) ^ (-4 : ℝ) by norm_num]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [he, he, ← Real.rpow_sub (by norm_num)]
  congr 1
  ring

omit [Fact P.Prime] in
/-- Positive parent precision rules out coarse-scale omission. -/
theorem initial_coarse_scale_active (B : BudgetData HP P)
    (hA : 1 ≤ B.rankCharge) (M ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 1 ≤ r.task.rank)
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hp : 0 < B.requestPrecision M r) :
    ∀ bin ≤ ka, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale {r with usage := r.terminal} (some bin)) < M := by
  have hc : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hrR : (1 : ℝ) ≤ r.task.rank := by exact_mod_cast hr
  have hai : 1 ≤ B.rankCharge * r.task.rank := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hrR)]
  rw [B.requestPrecision_grid M ks ka r hs ht] at hp
  have hm : (B.slack : ℝ) * (1 + 4 * ((ka : ℝ) + ka)) < M := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).mp
      (show 2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank <
        (M : ℝ) / (16 * B.slack) by linarith)
    nlinarith [Nat.cast_nonneg (α := ℝ) ks, Nat.cast_nonneg (α := ℝ) ka]
  have hmN : B.slack * (1 + 4 * (ka + ka)) < M := by exact_mod_cast hm
  exact B.retained_scaleCutoff_lt {r with usage := r.terminal} M ka ka hrate ht hmN

omit [Fact P.Prime] in
/-- The literal inactive charge has an exponential fine-rate tail, with no bin count
or assumption that all retained cutoffs fit the budget. -/
theorem initialInactiveCharge_fine_tail_le (B : BudgetData HP P)
    (hA : 1 ≤ B.rankCharge) (M n j ks ka : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 1 ≤ r.task.rank)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hp : 0 < B.requestPrecision M r)
    (hd : dyadicSlack (Nat.log2 M + 1) j < M) :
    B.initialInactiveCharge M j r ≤
      2 * B.binCap * rate ka * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack) := by
  let S := B.bins.filter (fun bin => M ≤ max (dyadicSlack (Nat.log2 M + 1) j)
    (LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale {r with usage := r.terminal} (some bin))))
  have he : B.initialInactiveCharge M j r = B.binCap * ∑ bin ∈ S, rate bin := by
    simp only [initialInactiveCharge, S, sum_filter, hrate]
  rw [he]
  by_cases hS : S.Nonempty
  · let b := S.min' hS
    have hb : b ∈ S := min'_mem S hS
    have homit : M ≤ LogSpaceEstimation.scaleCutoff B.slack
        (B.sampleScale {r with usage := r.terminal} (some b)) := by
      have hh := (mem_filter.mp hb).2
      omega
    have hab : ka < b := by
      by_contra hh
      have hc := B.initial_coarse_scale_active hA M ks ka r hr hrate hs ht hp b
        (by omega)
      omega
    have hratio : rate b / rate ka ≤ (2 : ℝ) ^ (1 - (M : ℝ) / B.slack) := by
      have hc : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
      have hdif : (((ka : ℤ) - b).natAbs : ℝ) = (b : ℝ) - ka := by
        rw [Int.natAbs_natCast_sub_natCast_of_le (Nat.le_of_lt hab), Nat.cast_sub (by omega)]
      rw [B.sampleScale_grid {r with usage := r.terminal} ka b hrate ht,
        LogSpaceEstimation.scaleCutoff, Int.natAbs_mul] at homit
      norm_num only [Int.natAbs_natCast] at homit
      have hh : (M : ℝ) ≤ B.slack * (1 + 4 * (((ka : ℤ) - b).natAbs : ℝ)) := by
        exact_mod_cast homit
      rw [hdif] at hh
      rw [rate_ratio_rpow]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hbudget : (M : ℝ) / B.slack ≤ 1 + 4 * ((b : ℝ) - ka) :=
        (div_le_iff₀ hc).2 (by nlinarith [hh])
      nlinarith
    have hsum : ∑ i ∈ S, rate i ≤ (16 / 15 : ℝ) * rate b := by
      calc
        _ ≤ ∑ i ∈ Ico b (n + 1), rate i := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro i hi
            exact mem_Ico.mpr ⟨min'_le S i hi, by
              have hh := (mem_filter.mp hi).1
              rw [hbins, mem_range] at hh
              exact hh⟩
          · intro i _ _
            exact (rate_pos i).le
        _ ≤ _ := by
          simp_rw [rate_eq_source_grid]
          have h := geom_sum_Ico_le_of_lt_one (m := b) (n := n + 1)
            (by norm_num : (0 : ℝ) ≤ 16⁻¹) (by norm_num : (16⁻¹ : ℝ) < 1)
          convert h using 1; ring
    have hrateb : rate b ≤ rate ka * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack) := by
      exact (div_le_iff₀ (rate_pos ka)).mp hratio |>.trans_eq (by ring)
    calc
      _ ≤ B.binCap * ((16 / 15 : ℝ) * rate b) :=
        mul_le_mul_of_nonneg_left hsum B.binCap_nonneg
      _ ≤ B.binCap * ((16 / 15 : ℝ) *
          (rate ka * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrateb (by norm_num)) B.binCap_nonneg
      _ ≤ _ := by
        have hn := B.binCap_nonneg
        have hk := rate_pos ka
        have ht : 0 ≤ (2 : ℝ) ^ (1 - (M : ℝ) / B.slack) := by positivity
        nlinarith [mul_nonneg hn (mul_nonneg hk.le ht)]
  · rw [not_nonempty_iff_eq_empty.mp hS, sum_empty, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) B.binCap_nonneg)
      (rate_pos ka).le) (by positivity)

omit [Fact P.Prime] in
private lemma initial_mean_rate_salary (B : BudgetData HP P)
    (hA : 1 ≤ B.rankCharge) (M n ks ka : ℕ) (hhi : M ≤ 32 * B.slack * n)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 1 ≤ r.task.rank)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hp : 0 < B.requestPrecision M r) :
    rate n / rate ka ≤ (2 : ℝ) ^ (-(4 / 3 : ℝ) * (B.requestPrecision M r + B.rankCharge)) ∧
    (2 : ℝ) ^ (1 - (M : ℝ) / B.slack) ≤
      (2 : ℝ) ^ (-(4 / 3 : ℝ) * (B.requestPrecision M r + B.rankCharge)) := by
  have hc : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hq : (M : ℝ) / (16 * B.slack) ≤ 2 * n := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).2
    have hh : (M : ℝ) ≤ 32 * B.slack * n := by exact_mod_cast hhi
    nlinarith
  have hrR : (1 : ℝ) ≤ r.task.rank := by exact_mod_cast hr
  have hAi : B.rankCharge ≤ B.rankCharge * r.task.rank :=
    le_mul_of_one_le_right (by linarith) hrR
  have hpgrid := B.requestPrecision_grid M ks ka r hs ht
  have hka : (ka : ℝ) ≤ n := by
    nlinarith [Nat.cast_nonneg (α := ℝ) ks]
  have hratio : (M : ℝ) / B.slack = 16 * ((M : ℝ) / (16 * B.slack)) := by
    field_simp
  constructor
  · rw [rate_ratio_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) ks]
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hratio]
    nlinarith [Nat.cast_nonneg (α := ℝ) ks, Nat.cast_nonneg (α := ℝ) ka]

/-- After the temporal boundary, one uniform constant pays all semantic loss.
Only the necessary depth-to-budget coverage remains; field width, endpoint exponents,
and cutoffs of individual retained bins are unrestricted within the grid horizon. -/
theorem initialPolynomialLoss_row_uniform_le (B : BudgetData HP P)
    (hA : 1 ≤ B.rankCharge) (M n j ks ka : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1)) (hhi : M ≤ 32 * B.slack * n)
    (H : Horizon P) (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 1 ≤ r.task.rank)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hp : 0 < B.requestPrecision M r) (hd : dyadicSlack (Nat.log2 M + 1) j < M)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (R : RoleProfile 3) (ss st : List (ZMod P)) :
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
        (rate ka + B.base x y))) ≤
      (4 * (1 + 2 * B.binCap) * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)) ^ 4 := by
  let w := (2 : ℝ) ^ (-(4 / 3 : ℝ) * (B.requestPrecision M r + B.rankCharge))
  let t := (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let b := rate n + 2 * B.binCap * rate ka * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack)
  have hcap := B.binCap_nonneg
  have hap := rate_pos ka
  have hn := rate_pos n
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hloss (x y : ZMod P) : B.initialPolynomialLoss M n j r x y ≤ b :=
    (B.initialPolynomialLoss_le M n j r hrate hC x y).trans
      (add_le_add le_rfl (B.initialInactiveCharge_fine_tail_le hA M n j ks ka hbins
        hrate r hr hs ht hp hd))
  obtain ⟨homit, hfine⟩ := B.initial_mean_rate_salary hA M n ks ka hhi r hr hs ht hp
  have hbr : b / rate ka ≤ (1 + 2 * B.binCap) * w := by
    dsimp only [b]
    have he : (rate n + 2 * B.binCap * rate ka *
        (2 : ℝ) ^ (1 - (M : ℝ) / B.slack)) / rate ka =
        rate n / rate ka + 2 * B.binCap * (2 : ℝ) ^ (1 - (M : ℝ) / B.slack) := by
      field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hfine (by positivity : 0 ≤ 2 * B.binCap)]
  have hw3 : w ^ 3 = t ^ 4 := by
    dsimp only [w, t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcube : (1 + 2 * B.binCap) ^ 3 ≤ (1 + 2 * B.binCap) ^ 4 := by
    have hh : 1 ≤ 1 + 2 * B.binCap := by linarith
    calc
      _ ≤ (1 + 2 * B.binCap) ^ 3 * (1 + 2 * B.binCap) :=
        le_mul_of_one_le_right (by positivity) hh
      _ = _ := by ring
  calc
    _ ≤ 256 * (b / rate ka) ^ 3 := B.initialPolynomialLoss_row_entry_le
      M n j ks ka hbins hrate hcutoff H hks hka r hs hC hC1 R ss st hb hloss
    _ ≤ 256 * ((1 + 2 * B.binCap) * w) ^ 3 := by gcongr
    _ = 256 * (1 + 2 * B.binCap) ^ 3 * t ^ 4 := by rw [mul_pow, hw3]; ring
    _ ≤ 256 * (1 + 2 * B.binCap) ^ 4 * t ^ 4 := by gcongr
    _ = _ := by dsimp only [t]; ring

/-- One rooted envelope pays every literal semantic prefix, including complete temporal
inactivity. Its constant depends only on the primitive bin cap. -/
theorem initialPolynomialLoss_root_uniform_le (B : BudgetData HP P)
    (hA : 1 ≤ B.rankCharge) (M n j ks ka : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1)) (hhi : M ≤ 32 * B.slack * n)
    (H : Horizon P) (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 1 ≤ r.task.rank)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hp : 0 < B.requestPrecision M r)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (R : RoleProfile 3) (ss st : List (ZMod P)) :
    rowNormPow 4 P r.source.rate
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ka) B.padding st)
      (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
        (rate ka + B.base x y))) ^ (4⁻¹ : ℝ) ≤
      (4 * (1 + 2 * B.binCap) * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)) * (2 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j := by
  let d := dyadicSlack (Nat.log2 M + 1) j
  let C := 4 * (1 + 2 * B.binCap)
  let t := (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge)
  let D := rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n j r x y| /
      (rate ka + B.base x y)))
  have hcap := B.binCap_nonneg
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hD : 0 ≤ D := rowNormPow_nonneg
    (by rw [hs]; exact mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) _
  have htarget : D ≤ (C * t * (2 : ℝ) ^ d) ^ 4 := by
    by_cases hd : d < M
    · have h := B.initialPolynomialLoss_row_uniform_le hA M n j ks ka hbins hrate
        hcutoff hhi H hks hka r hr hs ht hp hd hC hC1 R ss st
      have h' : D ≤ (C * t) ^ 4 := by simpa only [C, t, mul_assoc] using h
      exact h'.trans (pow_le_pow_left₀ (mul_nonneg hC0 ht0)
        (le_mul_of_one_le_right (mul_nonneg hC0 ht0) (one_le_pow₀ (by norm_num))) 4)
    · have hdm : (M : ℝ) ≤ d := by exact_mod_cast Nat.le_of_not_gt hd
      have hc : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
      have hrR : (1 : ℝ) ≤ r.task.rank := by exact_mod_cast hr
      have hAi : B.rankCharge ≤ B.rankCharge * r.task.rank :=
        le_mul_of_one_le_right (by linarith) hrR
      have hdiv : (M : ℝ) / (16 * B.slack) ≤ M := by
        apply div_le_self (Nat.cast_nonneg M)
        linarith
      have hexp : 0 ≤ -B.requestPrecision M r - B.rankCharge + (d : ℝ) := by
        rw [B.requestPrecision_grid M ks ka r hs ht]
        nlinarith [Nat.cast_nonneg (α := ℝ) ka, Nat.cast_nonneg (α := ℝ) ks]
      have ht1 : 1 ≤ t * (2 : ℝ) ^ d := by
        dsimp only [t]
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_add (by norm_num)]
        exact Real.one_le_rpow (by norm_num) hexp
      have hc4 : 4 ≤ C := by dsimp only [C]; linarith
      have h4 : 4 ≤ C * t * (2 : ℝ) ^ d := by
        nlinarith [mul_le_mul_of_nonneg_left ht1 hC0]
      exact (B.initialPolynomialLoss_row_le M n j ks ka hbins hrate hcutoff H hks
        hka r hs hC hC1 R ss st).trans
          (by convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4 4 using 1; norm_num)
  have hroot := Real.rpow_le_rpow hD htarget (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have he : ((C * t * (2 : ℝ) ^ d) ^ 4) ^ (4⁻¹ : ℝ) = C * t * (2 : ℝ) ^ d := by
    convert Real.pow_rpow_inv_natCast (by positivity : 0 ≤ C * t * (2 : ℝ) ^ d)
      (by decide : (4 : ℕ) ≠ 0) using 1
  rw [he] at hroot
  simpa only [C, t, mul_assoc, d, D] using hroot

/-- The actual stationary, final, rarity-tail and raw first-mean budgets share a
width-independent payment. Individual fine bins may remain inactive. This pays semantic
loss and normalized transport, conditional on the separately supplied child IH. -/
theorem initialComputedFirstBudgets_uniform (B : BudgetData HP P)
    (hA : 1 ≤ B.rankCharge) (M n ks ka : ℕ)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1)) (hhi : M ≤ 32 * B.slack * n)
    (H : Horizon P) (hks : ks ≤ H.maxExponent) (hka : ka ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 1 ≤ r.task.rank)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hp : 0 < B.requestPrecision M r)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (R : RoleProfile 3) (ss st : List (ZMod P))
    (coefficient floor Rraw : ℝ) (hf : 0 < floor) :
    let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-B.rankCharge)
    let S := 4 * (1 + 2 * B.binCap) * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge)
    let x := 2 * (K * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) + S)
    B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511 ∧
    B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * x ∧
    B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 ∧
    B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor Rraw ≤
      8 * x ^ 4 * (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) / 63 := by
  extract_lets K S x
  let m := Nat.log2 M + 1
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let D := fun i => rowNormPow 4 P r.source.rate
    (retainedMask R.source (side P ks) B.padding ss)
    (retainedMask R.terminal (side P ka) B.padding st)
    (fun _ x y => min 1 (|B.initialPolynomialLoss M n i r x y| /
      (rate ka + B.base x y)))
  have hK : 0 ≤ K := by have hc := B.binCap_nonneg; dsimp only [K]; positivity
  have hS : 0 ≤ S := by have hc := B.binCap_nonneg; dsimp only [S]; positivity
  have hE : 0 ≤ E := mul_nonneg (by norm_num)
    (tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h)
  have hD (i : ℕ) : 0 ≤ D i := rowNormPow_nonneg
    (by rw [hs]; exact mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) _
  have hg (i : ℕ) : D i ^ (4⁻¹ : ℝ) ≤ S * (2 : ℝ) ^ dyadicSlack m i :=
    B.initialPolynomialLoss_root_uniform_le hA M n i ks ka hbins hrate hcutoff hhi
      H hks hka r hr hs ht hp hC hC1 R ss st
  have hp := compatible_growing_mean_pre_le hf.le hS m
    (fun i => D i ^ (4⁻¹ : ℝ)) (fun i _ => hg i)
  have ht' := compatible_growing_mean_tail_le hf hS HP.K m
    (fun i => D i ^ (4⁻¹ : ℝ)) (fun i _ => hg i)
  have hr := compatible_growing_mean_raw_le hf HP.K m Rraw
    (fun i => D i ^ (4⁻¹ : ℝ))
    (fun i _ => ⟨Real.rpow_nonneg (hD i) _, hg i⟩)
  have hpow (i : ℕ) : (D i ^ (4⁻¹ : ℝ)) ^ 4 = D i := by
    convert Real.rpow_inv_natCast_pow (hD i) (by decide : (4 : ℕ) ≠ 0) using 1
  simp_rw [hpow] at hr
  have hfinal := hg (Nat.log2 M)
  have hd : dyadicSlack m (Nat.log2 M) = 1 := by simp [m, dyadicSlack]
  rw [hd, pow_one] at hfinal
  have hx : K * E + S ≤ x := by dsimp only [x, E]; nlinarith
  have hx0 : 0 ≤ x := (add_nonneg (mul_nonneg hK hE) hS).trans hx
  have hp4 : (K * E) ^ 4 + S ^ 4 ≤ x ^ 4 := by
    have hke := mul_nonneg hK hE
    have h1 := pow_le_pow_left₀ hke (show K * E ≤ x / 2 by dsimp only [x, E]; linarith) 4
    have h2 := pow_le_pow_left₀ hS (show S ≤ x / 2 by dsimp only [x, E]; linarith) 4
    nlinarith [pow_nonneg hx0 4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * (floor * E / 511) + _) ≤ _
    apply (mul_le_mul_of_nonneg_left (add_le_add_right hp _) (by positivity)).trans
    nlinarith [mul_le_mul_of_nonneg_left hx (by positivity :
      0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * floor / 511)]
  · change (8 : ℝ) ^ (4⁻¹ : ℝ) * (K * E + D (Nat.log2 M) ^ (4⁻¹ : ℝ)) ≤ _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp only [x, E]
    nlinarith
  · change (8 : ℝ) ^ (4⁻¹ : ℝ) *
      (K * ((2 + 256 / floor) ^ (4⁻¹ : ℝ) * E / 63) + _) ≤ _
    apply (mul_le_mul_of_nonneg_left (add_le_add_right ht' _) (by positivity)).trans
    nlinarith [mul_le_mul_of_nonneg_left hx (by positivity :
      0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63)]
  · change 8 * (K ^ 4 * (_ * E ^ 4 / 63) + _) ≤ _
    apply (mul_le_mul_of_nonneg_left (add_le_add_right hr _) (by norm_num : (0 : ℝ) ≤ 8)).trans
    nlinarith [mul_le_mul_of_nonneg_left hp4 (by positivity :
      0 ≤ 8 * (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) / 63)]

/-- One structural charge, fixed before width, depth, budget and endpoint exponents,
pays the complete separated first-mean reserve. The budget must be covered by retained
depth, and the parent must be active. Second mean and both centered noises remain separate. -/
theorem initialComputedFirstBudgets_uniform_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap coefficient floor cap C Cpre : ℝ) (hf : 0 < floor) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A →
      ∀ (M n ks ka : ℕ), B.bins = range (n + 1) → B.binRate = rate →
      B.cutoff = (fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
        rate 1 i (fun _ => 1)) → M ≤ 32 * B.slack * n →
      ∀ (H : Horizon P), ks ≤ H.maxExponent → ka ≤ H.maxExponent →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)), 1 ≤ r.task.rank →
      r.source.rate = rate ks → r.terminal.rate = rate ka →
      0 < B.requestPrecision M r → (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 →
      ∀ (R : RoleProfile 3) (ss st : List (ZMod P)),
      initialSeparatedReserve HP C Cpre
        (B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor)
        (B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient)
        (B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor)
        (64 * B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor
          ((2 * max cap 16) ^ (4⁻¹ : ℝ))) ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let L := 2 * ((max (512 * (6 * binCap + 3) ^ 3) (32768 * binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * E + 4 * (1 + 2 * binCap))
  obtain ⟨A, hA⟩ := initialFirstTransportPayment_exists_charge HP floor cap C Cpre L
  refine ⟨A + 1, by omega, ?_⟩
  intro P _ B hcap hcharge M n ks ka hbins hrate hcutoff hhi H hks hka
    r hrank hs ht hp hC hC1 R ss st
  have hcharge1 : 1 ≤ B.rankCharge := by rw [hcharge]; exact_mod_cast Nat.le_add_left 1 A
  obtain ⟨hpre, hfinal, htail, hraw⟩ := B.initialComputedFirstBudgets_uniform
    hcharge1 M n ks ka hbins hrate hcutoff hhi H hks hka r hrank hs ht hp hC hC1 R ss st
    coefficient floor ((2 * max cap 16) ^ (4⁻¹ : ℝ)) hf
  let K := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (-B.rankCharge)
  let S := 4 * (1 + 2 * B.binCap) * (2 : ℝ) ^ (-B.requestPrecision M r) *
    (2 : ℝ) ^ (-B.rankCharge)
  let x := 2 * (K * E + S)
  have hbc := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h
  have hE : 0 ≤ E := mul_nonneg (by norm_num)
    (tsum_nonneg fun h => LogSpaceEstimation.scaleMajorant_nonneg h)
  have hx : 0 ≤ x := by dsimp only [x, K, S]; positivity
  have hscalar : x ≤ L * (2 : ℝ) ^ (-(A : ℝ)) *
      (2 : ℝ) ^ (-B.requestPrecision M r) := by
    have hL : 0 ≤ L := by
      dsimp only [L]
      rw [← hcap]
      positivity
    have hsmall : (2 : ℝ) ^ (-B.rankCharge) ≤ (2 : ℝ) ^ (-(A : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hcharge]
      push_cast
      linarith
    have heq : x = L * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (-B.requestPrecision M r) := by
      dsimp only [x, K, S, L]
      rw [hcap]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hL) (by positivity)
  obtain ⟨hpn, hfn, htn⟩ := B.initialComputedFirstBudgets_nonneg M n ks ka r
    (by rw [hs]; exact (rate_pos ks).le) R ss st coefficient floor hf.le
  have hpaid : initialSeparatedReserve HP C Cpre
      (B.initialComputedFirstPreBudget M n r R ks ka ss st coefficient floor)
      (B.initialComputedFirstFinalBudget M n r R ks ka ss st coefficient)
      (B.initialComputedFirstTailBudget M n r R ks ka ss st coefficient floor)
      (64 * B.initialComputedFirstRawBudget M n r R ks ka ss st coefficient floor
        ((2 * max cap 16) ^ (4⁻¹ : ℝ))) ≤
      initialFirstTransportPayment HP floor cap C Cpre x := by
    unfold initialFirstTransportPayment
    apply initialSeparatedReserve_mono HP C Cpre
    · exact hpn
    · exact hfn
    · exact htn
    · exact hpre
    · exact hfinal
    · exact htail
    · convert mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 64) using 1; ring
  exact hpaid.trans ((initialFirstTransportPayment_mono HP floor cap C Cpre hf.le hx
    hscalar).trans (hA _))

/-- One charge pays the actual complete first-coordinate reserve without field-width,
half-depth or all-cutoffs-active restrictions. Retained depth must cover the budget and
all endpoint/bin exponents must be admissible. This is conditional numerical allocation:
second-coordinate payment and successful simultaneous recursion remain separate. -/
theorem initialComputedFirstCoordinateReserve_uniform_exists_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (binCap coefficient floor cap C Cpre : ℝ) (hf : 0 < floor) :
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
      (∀ x y, 0 ≤ B.base x y) → B.base *ᵥ 1 ≤ 1 → ∀ (ζ Lh Lρ : ℝ),
      B.initialComputedFirstCoordinateReserve M n r R ks ka ss st coefficient ζ Lh Lρ
        floor cap C Cpre ≤ ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  let E := 4 * ∑' h, LogSpaceEstimation.scaleMajorant h
  let Lmean := 2 * ((max (512 * (6 * binCap + 3) ^ 3) (32768 * binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * E + 4 * (1 + 2 * binCap))
  let Lnoise := 2 * (initialNormalizedNoiseConstant binCap coefficient + 256 * binCap)
  let L := |Lmean| + |Lnoise|
  obtain ⟨A, hA⟩ := initialFirstCoordinatePayment_exists_charge HP floor cap C Cpre L
  refine ⟨A + 1, by omega, ?_⟩
  intro P _ B hcap hcharge hrate hcutoff M n ks ka hbins hhi H hn hks hka
    r R ss st hs ht htask hprecision hbase hrow ζ Lh Lρ
  let e := (2 : ℝ) ^ (-B.requestPrecision M r)
  let a := (2 : ℝ) ^ (-B.rankCharge)
  let T := (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
    (4⁻¹ : ℝ) * |coefficient| * e * a
  let S := 4 * (1 + 2 * B.binCap) * e * a
  let x := 2 * (T * E + S)
  let y := 2 * (initialNormalizedNoiseConstant B.binCap coefficient + 256 * B.binCap) * e * a
  let z := L * (2 : ℝ) ^ (-(A : ℝ)) * e
  let Rraw := (2 * max cap 16) ^ (4⁻¹ : ℝ)
  have hcharge1 : 1 ≤ B.rankCharge := by rw [hcharge]; exact_mod_cast Nat.le_add_left 1 A
  have hcharge0 : 0 ≤ B.rankCharge := by linarith
  have hcap0 := B.binCap_nonneg
  have hsum : 0 ≤ ∑' h, LogSpaceEstimation.scaleMajorant h :=
    tsum_nonneg LogSpaceEstimation.scaleMajorant_nonneg
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hx : 0 ≤ x := by dsimp only [x, T, S, e, a]; positivity
  have hy : 0 ≤ y := by dsimp only [y, initialNormalizedNoiseConstant, e, a]; positivity
  have hz : 0 ≤ z := by dsimp only [z, L, e]; positivity
  have hrank : 1 ≤ r.task.rank := by
    rw [htask]
    norm_num [HierarchyTask.rank, BoundedRowTask.localTask, CorrectionRowTask.rank,
      PilotRowTask.rank, PilotTask.rank]
  have hxm : x = Lmean * a * e := by
    dsimp only [x, T, S, Lmean]
    rw [hcap]
    ring
  have hLmean : Lmean ≤ L := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hLnoise : Lnoise ≤ L := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  have hsmall : a ≤ (2 : ℝ) ^ (-(A : ℝ)) := by
    dsimp only [a]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hcharge]
    push_cast
    linarith
  have hL : 0 ≤ L := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hae : 0 ≤ a * e := by dsimp only [a, e]; positivity
  have hxz : x ≤ z := by
    rw [hxm]
    calc
      _ ≤ L * a * e := by nlinarith [mul_le_mul_of_nonneg_right hLmean hae]
      _ ≤ L * (2 : ℝ) ^ (-(A : ℝ)) * e :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hL) (by
          dsimp only [e]; positivity)
      _ = z := rfl
  have hyz : y ≤ z := by
    have heq : y = Lnoise * a * e := by
      dsimp only [y, Lnoise]
      rw [hcap]
      ring
    rw [heq]
    calc
      _ ≤ L * a * e := by nlinarith [mul_le_mul_of_nonneg_right hLnoise hae]
      _ ≤ L * (2 : ℝ) ^ (-(A : ℝ)) * e :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hL) (by
          dsimp only [e]; positivity)
      _ = z := rfl
  have hsrate : r.source.rate = rate ks := by rw [hs]; rfl
  have htrate : r.terminal.rate = rate ka := by rw [ht]; rfl
  have hM : 0 < M := (Nat.zero_le _).trans_lt
    (B.initial_coarse_scale_active hcharge1 M ks ka r hrank hrate hsrate htrate
      hprecision 0 (Nat.zero_le _))
  obtain ⟨hm0, hm1, hm2, hm3⟩ := B.initialComputedFirstBudgets_uniform
    hcharge1 M n ks ka hbins hrate hcutoff hhi H hks hka r hrank hsrate htrate
    hprecision hbase hrow R ss st
    coefficient floor Rraw hf
  obtain ⟨hz0, hz1, hz2, hz3⟩ := B.initialComputedPrecisionMoment_firstNoise_polynomial_schedule
    hcharge0 hrate hcutoff H (fun bin hb => by rw [hbins, mem_range] at hb; omega)
    M n ks ka hM r R ss st hs ht htask hka hprecision.le hbase hrow
    coefficient ζ Lh Lρ floor Rraw hf
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x * floor / 511 at hm0
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x at hm1
  change _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * x * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 at hm2
  change _ ≤ 8 * x ^ 4 * (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) / 63 at hm3
  change _ ≤ floor * y / 511 at hz0
  change _ ≤ y / 4 at hz1
  change _ ≤ y * (458752 / 57) at hz2
  change _ ≤ (64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4)) * y ^ 4 / 63 at hz3
  obtain ⟨hpn, hfn, htn⟩ := B.initialComputedFirstBudgets_nonneg M n ks ka r
    (by rw [hsrate]; exact (rate_pos ks).le) R ss st coefficient floor hf.le
  have hroot (j : ℕ) : 0 ≤ B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient
      ζ Lh Lρ j true 0 ^ (4⁻¹ : ℝ) := Real.rpow_nonneg
    (B.initialComputedPrecisionMoment_nonneg M n r (by rw [hsrate]; exact (rate_pos ks).le)
      R ks ka ss st coefficient ζ Lh Lρ j true 0) _
  have hpaid : B.initialComputedFirstCoordinateReserve M n r R ks ka ss st coefficient
      ζ Lh Lρ floor cap C Cpre ≤ initialFirstCoordinatePayment HP floor cap C Cpre z := by
    unfold initialComputedFirstCoordinateReserve initialFirstCoordinatePayment
    dsimp only
    apply initialSeparatedReserve_mono HP C Cpre
    · exact add_nonneg hpn (sum_nonneg fun j _ =>
        mul_nonneg (dyadicFloor_nonneg hf.le _ _) (hroot j))
    · exact add_nonneg hfn (hroot _)
    · exact add_nonneg htn (sum_nonneg fun j _ => mul_nonneg (by positivity) (hroot j))
    · apply (add_le_add hm0 hz0).trans
      calc
        _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * z * floor / 511 + floor * z / 511 := by gcongr
        _ = _ := by ring
    · apply (add_le_add hm1 hz1).trans
      have hfinal : y / 4 ≤ z := by linarith
      nlinarith only [mul_le_mul_of_nonneg_left hxz
        (show 0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) by positivity), hfinal]
    · apply (add_le_add hm2 hz2).trans
      calc
        _ ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * z * (2 + 256 / floor) ^ (4⁻¹ : ℝ) / 63 +
            z * (458752 / 57) := by gcongr
        _ = _ := by ring
    · apply (mul_le_mul_of_nonneg_left (add_le_add hm3 hz3) (by norm_num : (0 : ℝ) ≤ 64)).trans
      have hx4 := pow_le_pow_left₀ hx hxz 4
      have hy4 := pow_le_pow_left₀ hy hyz 4
      have hc : 0 ≤ 64 * (HP.K : ℝ) * Rraw ^ 4 / ((HP.K + 1) * floor ^ 4) := by positivity
      dsimp only [Rraw] at hc ⊢
      nlinarith only [mul_le_mul_of_nonneg_left hx4 hc, mul_le_mul_of_nonneg_left hy4 hc]
  exact hpaid.trans (hA e)

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
